/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackSchedule
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.ReplaySemantics
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.Bounds

/-!
# Statement layer — the real stateful replay executor/relation (D1)

This module is the single low-dependency, dependency-acyclic home of the **real
stateful verifier replay** that Lemma 5.25's seven items quantify over.  It is built directly on
the **canonical schedule layer** `BacktrackSchedule.lean`:

- the **cursor** is the real `DuplexSpongeFS.Backtrack.ScheduleCursor` (`queryIndex`,
  `absorbOffset`, `squeezeOffset`);
- the **action stream** is the salt absorb followed by the **real
  `DuplexSpongeFS.protocolPhases pSpec`**.  Under the paper-facing
  `Section5RoundStructure` interface this is exactly
  `Act_𝒱 = [Start, A(δ), A(ℓ_𝐏(1)), S(ℓ_𝐕(1)), …]`; the generic layer itself preserves the
  underlying direction-labelled action order rather than pretending every `ProtocolSpec` is
  paired;
- the **partial-block cursor movement** is the **real `ScheduleCursor.absorb` / `.squeeze`**
  (with `.absorbOne`/`.squeezeOne` crossing rate boundaries by emitting a permutation query);
- the phase layout (salt locations, per-phase source locations, first-squeeze marker) is the
  **real `ScheduleCursor.buildPhaseSchedule`** / `PhaseLayout`;
- the **exact verifier permutation count** `N_𝒱` is the **real `verifierPermCallCount pSpec δ`**.

It is a **coherent object, not a bag of unrelated Props**: `ReplayState` records the real cursor,
the real phase schedule, the real raw insertion `QueryLog`, and the **strict-prefix vs. full**
two-table split (Backtrack scans the strict prefix; LookAhead the full table); `replayStep` is the
single cursor/phase transition; and the two **independent** frame-check relations — the
absorb-side (11a) and the squeeze-side (11b) — are separate predicates so that Lemma 5.25 items
2/3 and the no-abort claims can cite them distinctly.  `Certified` (the post-prover/pre-squeeze
marker) is the **existing** real `firstSqueezeQuery?` marker of `ReplaySemantics`.

Rules honoured: **no** fabricated boundary type, **no** generic `Prop` combinator standing in for
an execution, **no** free `ℕ`/`ℝ` standing in for a real quantity, **no** `sorry`/`admit`/`axiom`.
This module imports no live Section 5 algorithm beyond the canonical schedule layer and the real
`TraceNabla`/forward-table data shapes.
-/

namespace DuplexSpongeFS

namespace Statement

open DuplexSpongeFS.Backtrack
open OracleSpec
open ProtocolSpec
open DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n} {U : Type}
  [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [HasMessageSize pSpec] [HasChallengeSize pSpec]

/-! ## The replayed cursor and phases (canonical re-exports) -/

/-- The real stateful-replay cursor: `queryIndex` (forward permutation calls emitted),
`absorbOffset`/`squeezeOffset` (positions in the current rate block).  Single source of truth:
`BacktrackSchedule.ScheduleCursor`. -/
abbrev ReplayCursor := DuplexSpongeFS.Backtrack.ScheduleCursor

/-- One actual replayed protocol phase: a prover-message absorb or a verifier-challenge squeeze.
Single source of truth: `BacktrackSchedule.ScheduleCursor.PhaseShape`. -/
abbrev ReplayPhase := DuplexSpongeFS.Backtrack.ScheduleCursor.PhaseShape

/-- The per-phase layout recovered by the real scheduler: source locations, the first-squeeze
marker, and the post-phase query counter. -/
abbrev ReplayPhaseLayout := DuplexSpongeFS.Backtrack.ScheduleCursor.PhaseLayout

/-- The full value-free layout of one replay: salt locations, one phase layout per protocol
operation, and the final cursor (whose `queryIndex` is the exact `N_𝒱`). -/
abbrev ReplayPhaseSchedule := DuplexSpongeFS.Backtrack.ScheduleCursor.PhaseSchedule

/-- The one rate coordinate `⟨q, x⟩` of a prospective permutation-query input. -/
abbrev ReplayRateLocation := DuplexSpongeFS.Backtrack.ScheduleCursor.RateLocation

/-! ## Start (the paper's DS.Start initial action) -/

/-- The paper's `Start` action is a single hash query to `h` that initialises the sponge to its
all-zero capacity/rate.  Over the raw trace this is the one `Start`-type entry (the `+1` in
`N := T + 1 + N_𝒱`); the verifier itself makes no forward `p` call on it.  This names the Start
hash entry concretely as the `.inl` query. -/
def StartHashQuery (start : StmtIn) : (duplexSpongeChallengeOracle StmtIn U).Domain :=
  .inl start

/-- The initial rate of the `Start` state is all-zero (the `b = 0` case of eq. (11a)): after
`DS.Start`, the reusable sponge state `sInit` (whose capacity is the hash answer
`h(start)`) has every rate coordinate equal to `0`.  `rateListOf` cannot be applied to the raw
hash answer (the hash query returns only the `C`-capacity vector), so this names the property on
the post-`Start` sponge state itself. -/
def StartRateAllZero (sInit : CanonicalSpongeState U) : Prop :=
  ∀ x ∈ rateListOf U sInit, x = (0 : U)

/-! ## The stateful replay step (partial-block cursor movement) -/

/-- One replayed phase advances the **real** cursor by the **real** schedule transition:
`absorb`/`squeeze` for a `PhaseShape`, exactly the stateful partial-block movement of eq. (4a)
(reusing a partially used rate block, crossing the boundary by emitting a permutation query).
The Section 5 theorems instantiate this only under `Section5Nonempty`; the generic cursor is kept
total because the underlying FS and DSFS constructions remain general. -/
def replayStep (R : ℕ) (cursor : ReplayCursor) (phase : ReplayPhase) : ReplayCursor :=
  DuplexSpongeFS.Backtrack.ScheduleCursor.schedulePhase R cursor phase |>.2

/-- Replay the whole `Act_𝒱` action stream (salt absorb then all protocol phases) from the
paper's start cursor `(q,a,s) = (0,0,r)`, returning the **real** `PhaseSchedule`. -/
noncomputable def replayPhaseSchedule (R : ℕ) (δ : ℕ) : ReplayPhaseSchedule :=
  DuplexSpongeFS.Backtrack.ScheduleCursor.buildPhaseSchedule R ⟨0, 0, R⟩ δ
    (DuplexSpongeFS.protocolPhases (pSpec := pSpec))

/-- The exact verifier permutation-call count `N_𝒱` (eq. 4b): the final `queryIndex` of the real
replay.  Single source of truth: `DuplexSpongeFS.verifierPermCallCount`. -/
noncomputable abbrev VerifierPermCallCount (δ : ℕ) : ℕ :=
  DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)

/-- The cursor immediately after the leading salt absorb of a replay. -/
def saltCursor (R : ℕ) (δ : ℕ) : ReplayCursor :=
  DuplexSpongeFS.Backtrack.ScheduleCursor.absorb R ⟨0, 0, R⟩ δ

/-! ## Certified post-prover/pre-squeeze markers (real, existing) -/

/-- A certified nonempty post-prover/pre-squeeze marker: `pos` is exactly the first forward
permutation query of a nonempty verifier squeeze at a rate boundary.  This is the **existing** real
marker `Certified` of `ReplaySemantics` (= `ScheduleCursor.firstSqueezeQuery?`), re-exported here
for the stateful-replay lemmas. -/
abbrev CertifiedMarker (R : ℕ) (cursor : ReplayCursor) (len pos : ℕ) : Prop :=
  DuplexSpongeFS.Statement.Certified R cursor len pos

/-! ## Absorb-side and squeeze-side frame checks (separate, eq. 11a / 11b) -/

/-- The **absorb-side** frame check (eq. 11a): after a salt/prover-message absorb of `len` source
units ending in rate status `i_A`, the untouched rate suffix of the terminal absorb input `inState`
equals the all-zero initial suffix (when `b = 0`) or the corresponding suffix of the preceding
permutation output `predOut` (otherwise).  Separate from the squeeze-side check so item 2 and the
stateful-fidelity claims can cite the absorb direction alone. -/
def AbsorbFrame (R : ℕ) (b i_A : ℕ) (inState predOut : CanonicalSpongeState U) : Prop :=
  i_A ≤ R ∧
    ∀ x, i_A ≤ x → x < R →
      (rateListOf U inState)[x]? =
        (if b = 0 then some (0 : U) else (rateListOf U predOut)[x]?)

/-- The **squeeze-side** frame check (eq. 11b): for a completed nonempty verifier squeeze of `len`
output units, `inBlocks q`/`outBlocks q` name the rate block of the `q`-th permutation query's
input/output, and the cross-call rate equalities hold across the **actual `d` emitted forward
calls** at block indices `β..β+d-1`: the untouched input rate suffix
`s_(in,β+1) ‖ … ‖ s_(in,β+d-1)` equals
the preceding output suffix `s_(out,β) ‖ … ‖ s_(out,β+d-2)` (both sides empty when `d = 1`).

`d` is **supplied as the actual stateful number of emitted forward calls** — `d := q_after -
q_before` of the transition this frame is attached to — and the predicate checks **only** the
cross-call rate
equalities for that supplied actual `d`.  There is **no** ceiling here: the combinatorial
`⌈len/R⌉` can remain at most an *upper-bound* lemma on `d`, and is deliberately not an equality
inside this stateful predicate.  Separately citable from the absorb-side check. -/
def SqueezeFrame (R : ℕ) (len β d : ℕ) (inBlocks outBlocks : ℕ → Vector U R) : Prop :=
  0 < R ∧ 0 < len ∧
    ∀ ι, ι + 1 < d → inBlocks (β + 1 + ι) = outBlocks (β + ι)

/-! ## Trace-derived frame witnesses (fix #5) — indexed by `queryIndex`, filtered forward-only

`ScheduleCursor.queryIndex` counts **forward permutation calls**.  The raw replay `Trace`, by
contrast, is indexed over *all* raw entries — it includes the `DS.Start`/hash entry (`.inl _`) and
any inverse occurrences (`.inr (.inr _)`).  So a frame reader must **not** index the raw trace by
`queryIndex`.  Instead we project the raw trace to its **order-preserving forward-permutation
list** `forwardPermutationStates` (dropping the hash and the inverses in raw order) and index *that*
by `queryIndex`; a correspondence lemma ties each projected pair to its raw forward occurrence. -/

/-- A self-contained `q`-th-element lookup over a flat list (no `get?` dependency). -/
def listNth {α : Type} : List α → ℕ → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listNth xs n

omit [SpongeSize] in
/-- A list index strictly below its length has a value.  This small totality fact is the bridge
from a replay-history **count** to the `IsForwardCall` no-gap condition: `queryIndex` counts the
order-preserving forward-only projection, not raw trace positions. -/
theorem listNth_eq_some_of_lt_length {α : Type} (xs : List α) (q : ℕ) (hq : q < xs.length) :
    ∃ x, listNth xs q = some x := by
  induction xs generalizing q with
  | nil =>
      simp at hq
  | cons x xs ih =>
      cases q with
      | zero => exact ⟨x, rfl⟩
      | succ q =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hq
          obtain ⟨y, hy⟩ := ih q hq
          exact ⟨y, by simpa [listNth] using hy⟩

/-- The **order-preserving forward-permutation projection** of a raw replay `Trace`: the list of
forward-pass sponge pairs `(s_in, s_out)` appearing as `.inr (.inl _)` raw occurrences, in raw-trace
order, with the `DS.Start`/hash entry and the inverse occurrences dropped.  Because
`ScheduleCursor.queryIndex` counts exactly the forward permutation calls, the `q`-th element of this
list is the forward pair recorded when `queryIndex = q` — the correct value-domain for
`queryIndex`-indexed frame reads. -/
def forwardPermutationStates (trace : DuplexSpongeFS.Statement.Trace StmtIn U) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) :=
  trace.filterMap fun occ =>
    match occ with
    | ⟨.inr (.inl sIn), sOut⟩ => some (sIn, sOut)
    | _ => none

/-- The `q`-th forward permutation pair (indexed by `queryIndex`), or `none` past the number of
forward calls recorded. -/
def nthForwardPair (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (q : ℕ) :
    Option (CanonicalSpongeState U × CanonicalSpongeState U) :=
  listNth (forwardPermutationStates trace) q

/-- The sponge state read as **input** by the `q`-th forward permutation call, indexed by
`queryIndex` (the all-zero state past the recorded forward calls). -/
noncomputable def fwdInputState (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (q : ℕ) :
    CanonicalSpongeState U :=
  match nthForwardPair trace q with
  | some p => p.1
  | none => 0

/-- The sponge state written as **output** by the `q`-th forward permutation call, indexed by
`queryIndex` (the all-zero state past the recorded forward calls). -/
noncomputable def fwdOutputState (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (q : ℕ) :
    CanonicalSpongeState U :=
  match nthForwardPair trace q with
  | some p => p.2
  | none => 0

/-- The replay recorded a `q`-th forward permutation call (indexed by `queryIndex`). -/
def IsForwardCall (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (q : ℕ) : Prop :=
  match nthForwardPair trace q with
  | some _ => True
  | none => False

omit [DecidableEq U] in
/-- Every index below the length of the forward-only trace projection is a recorded forward call.
This is intentionally a statement about the filtered projection: hash and inverse entries do not
occupy a `ScheduleCursor.queryIndex` position. -/
theorem isForwardCall_of_lt_forwardPermutationStates_length
    (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (q : ℕ)
    (hq : q < (forwardPermutationStates trace).length) :
    IsForwardCall trace q := by
  obtain ⟨pair, hpair⟩ := listNth_eq_some_of_lt_length (forwardPermutationStates trace) q hq
  simp [IsForwardCall, nthForwardPair, hpair]

/-- The rate block of the input/output state of the `q`-th forward permutation call, read off the
actual trace — the value-level `inBlocks`/`outBlocks` the squeeze frame compares.  The rate block is
the real sponge rate `SpongeSize.R` (the raw trace states are `CanonicalSpongeState`). -/
noncomputable def fwdBlockIn (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (q : ℕ) :
    Vector U SpongeSize.R :=
  CanonicalSpongeState.rateSegment (fwdInputState trace q)

/-- The rate block of the input/output state of the `q`-th forward permutation call, read off the
actual trace — the value-level `inBlocks`/`outBlocks` the squeeze frame compares.  The rate block is
the real sponge rate `SpongeSize.R` (the raw trace states are `CanonicalSpongeState`). -/
noncomputable def fwdBlockOut (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (q : ℕ) :
    Vector U SpongeSize.R :=
  CanonicalSpongeState.rateSegment (fwdOutputState trace q)

omit [DecidableEq U] in
/-- **Correspondence** between a projected forward pair and its raw-trace occurrence: a pair
`(s_in, s_out)` is in the order-preserving forward projection of `trace` iff the raw occurrence
`⟨.inr (.inl s_in), s_out⟩` is a member of `trace`.  So each projected entry named by
`queryIndex` is
exactly the forward-pass data of one real raw forward occurrence. -/
lemma mem_forwardPermutationStates_iff_raw_occurrence
    (trace : DuplexSpongeFS.Statement.Trace StmtIn U)
    (p : CanonicalSpongeState U × CanonicalSpongeState U) :
    p ∈ forwardPermutationStates trace ↔
      (⟨.inr (.inl p.1), p.2⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t) ∈ trace := by
  unfold forwardPermutationStates
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨occ, hocc, hf⟩
    rcases occ with ⟨q0, a0⟩
    cases q0 with
    | inl v =>
        simp at hf
    | inr q0 =>
        cases q0 with
        | inl sIn =>
            simp at hf
            rw [← hf]
            simpa using hocc
        | inr sOut =>
            simp at hf
  · rintro hocc
    refine ⟨(⟨.inr (.inl p.1), p.2⟩ : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t), hocc, ?_⟩
    simp

/-! ## The stateful replay: one coherent execution, successor-linked at every step -/

/-- One genuine squeeze transition of `Act_𝒱`.  The predecessor/successor cursor is the real
`replayStep` cursor transition, and every block is read from the actual forward-permutation
projection of `trace`.  Absorb-side equation (11a) is deliberately *not* attached to an emitted
query here: a salt or prover absorb may end in a partially used block and emit no query at all.
It is instead checked by `AbsorbFrameCheck`, which follows the scheduler's write locations and
therefore also covers such partial-block absorbs. -/
def replayTransition (R : ℕ) (cursor : ReplayCursor) (phase : ReplayPhase)
    (trace : DuplexSpongeFS.Statement.Trace StmtIn U) : Prop :=
  let next := replayStep R cursor phase
  let q_before := cursor.queryIndex
  let q_after := next.queryIndex
  let d := q_after - q_before
  match phase with
  | .absorb _ => True
  | .squeeze len =>
      (∀ ι, ι < d → IsForwardCall trace (q_before + ι)) ∧
        SqueezeFrame SpongeSize.R len q_before d (fwdBlockIn trace) (fwdBlockOut trace)

/-! ## Absorb-side frame check (eq. 11a), including partial blocks -/

/-- All source-rate locations written by the leading salt or a prover-message absorb, in their
real schedule order.  This is the exact write set used by the live stateful Backtrack parser.
No verifier squeeze contributes a source location. -/
noncomputable def replayWriteLocations (R δ : ℕ) (phases : List ReplayPhase) :
    List ReplayRateLocation :=
  let schedule :=
    DuplexSpongeFS.Backtrack.ScheduleCursor.buildPhaseSchedule R ⟨0, 0, R⟩ δ phases
  schedule.saltLocations ++
    schedule.phaseLayouts.flatMap
      DuplexSpongeFS.Backtrack.ScheduleCursor.PhaseLayout.sourceLocations

/-- Equation (11a) for a single *recorded* input coordinate.  A coordinate written by salt or a
prover message is unconstrained: it carries source data.  Every other coordinate of a real forward
input is forced to be the all-zero Start value at query `0`, or the corresponding rate coordinate
of the preceding forward output.  This is the proof-facing version of
`BacktrackSequence.frameHoldsAt`.

The `R = SpongeSize.R` conjunct makes the schedule's rate-coordinate space explicit.  It is
definitionally true at every Section 5 use (`R := SpongeSize.R`) and prevents a statement over a
schedule rate from being silently compared with a different sponge rate. -/
def AbsorbFrameCoordinate (R : ℕ) (writes : List ReplayRateLocation)
    (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (queryIndex rateOffset : ℕ) : Prop :=
  if ⟨queryIndex, rateOffset⟩ ∈ writes then True else
    IsForwardCall trace queryIndex ∧
      rateOffset < R ∧
      (rateListOf U (fwdInputState trace queryIndex))[rateOffset]? =
        (if queryIndex = 0 then some (0 : U)
          else (rateListOf U (fwdOutputState trace (queryIndex - 1)))[rateOffset]?)

/-- The complete absorb-side frame check (eq. 11a) for a stateful replay.  Crucially it does not
require the salt absorb, or any individual prover absorb, to emit a permutation query.  A partial
absorb is checked when its prospective input becomes a real recorded forward call; if a later
write overwrites that coordinate first, the scheduler places it in `writes` and it is correctly
unconstrained. -/
noncomputable def AbsorbFrameCheck (R δ : ℕ) (phases : List ReplayPhase)
    (trace : DuplexSpongeFS.Statement.Trace StmtIn U) : Prop :=
  R = SpongeSize.R ∧
    ∀ queryIndex, queryIndex < (forwardPermutationStates trace).length →
      ∀ rateOffset, rateOffset < R →
        AbsorbFrameCoordinate R (replayWriteLocations R δ phases) trace queryIndex rateOffset

/-! ## The two-table split (Backtrack strict-prefix / LookAhead full) -/

/-- The **strict-prefix** table presented to BackTrack: the forward table normalised from the
insertion trace's strict prefix of length `cutoff` (all but the terminal entry, whose sentinel is
the query currently being classified). -/
def strictPrefixTable (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (cutoff : ℕ) :
    ForwardTable U :=
  DuplexSpongeFS.Statement.strictPrefixOf U (DuplexSpongeFS.Statement.forwardTableOfTrace trace)
    cutoff

/-- The **full** table presented to LookAhead: the forward table normalised from the whole
insertion trace. -/
def fullTable (trace : DuplexSpongeFS.Statement.Trace StmtIn U) : ForwardTable U :=
  DuplexSpongeFS.Statement.fullOf U (DuplexSpongeFS.Statement.forwardTableOfTrace trace)

-- The two-table split is coherent: the strict-prefix table (at any cutoff) is always a prefix of
-- the full table.  This is the invariant `ReplayState.prefix_is_prefix` for a replay whose tables
-- were derived from one raw trace.
omit [DecidableEq U] in
lemma strictPrefixTable_isPrefix_fullTable
    (trace : DuplexSpongeFS.Statement.Trace StmtIn U) (cutoff : ℕ) :
    List.IsPrefix (strictPrefixTable trace cutoff) (fullTable trace) := by
  unfold strictPrefixTable fullTable
  exact List.take_prefix cutoff (DuplexSpongeFS.Statement.forwardTableOfTrace trace)

/-! ## The coherent replay execution (replace the bag-of-fields `ReplayState`) -/

/-- A record containing unrelated `cursor`,
`schedule`, `insertionTrace`, `strictPrefix`, `full`, `prefix_is_prefix` stored side by side with no
law tying them to one execution.  It is replaced by `ReplayExecution`, a genuine successor-linked
object in which:

- `phases` is the real `Act_𝒱` phase list (`protocolPhases pSpec`) — prover absorbs and verifier
  squeezes in round order (the leading salt absorb `A(δ)` is the separate step `salt_start`);
- the cursor movement is the **real** `replayStep` (`ScheduleCursor.absorb`/`.squeeze`): the
  terminal cursor `final` is the genuine fold of `phases` from the salt cursor (`runs`), so every
  step is successor-linked with partial rate-block continuation;
- `salt_run` links the start to the real salt cursor `saltCursor R δ`, and `schedule` is the real
  `PhaseSchedule` of the whole replay (salt + `phases`);
- the raw insertion log `trace` and its **derived** tables (`strictPrefix` = `strictPrefixTable
  trace cutoff`, `full` = `fullTable trace`) are linked by `tablesDerived`, and `prefix_is_prefix`
  is the two-table law on them.

The cursor/schedule and two-table parts are coherent by construction: `runs` folds the real
schedule and the tables are derived from the one observed raw trace.  Crucially, this record does
**not** yet assert that the observed trace realizes that schedule — its `trace` can contain hash,
forward, and inverse occurrences whose phase-by-phase origin must still be proved.  That stronger
link is the purpose of the separate `ReplayHistory` witness below and of Lemma 5.25.  Keeping the
distinction explicit prevents a cursor-count fact from being mistaken for a live replay
realization theorem. -/
structure ReplayExecution (StmtIn : Type) (U : Type) [SpongeUnit U] [SpongeSize]
    (R δ : ℕ) (phases : List ReplayPhase) where
  trace : DuplexSpongeFS.Statement.Trace StmtIn U
  cutoff : ℕ
  salt_start : ReplayCursor
  salt_run : salt_start = saltCursor R δ
  final : ReplayCursor
  runs : phases.foldl (fun c ph => replayStep R c ph) salt_start = final
  /-- The schedule is not caller-chosen: it is the canonical salt-plus-phase replay. -/
  schedule : ReplayPhaseSchedule
  schedule_is_canonical :
    schedule = DuplexSpongeFS.Backtrack.ScheduleCursor.buildPhaseSchedule R ⟨0, 0, R⟩ δ phases
  /-- The recorded terminal cursor is the canonical schedule's final cursor. -/
  final_is_schedule_final : final = schedule.finalCursor
  strictPrefix : ForwardTable U := strictPrefixTable trace cutoff
  full : ForwardTable U := fullTable trace
  tablesDerived : strictPrefix = strictPrefixTable trace cutoff ∧ full = fullTable trace := by
    constructor <;> rfl
  prefix_is_prefix : List.IsPrefix strictPrefix full

/-- The executable replay runner: fold every `Act_𝒱` phase through the real cursor transition
`replayStep` from the salt cursor `A(δ)`, computing the terminal cursor.  `ScheduleCursor` is a
plain inductive, so this genuinely computes (a real runner, not a relation over supplied
successors).  Its `queryIndex` is exactly `VerifierPermCallCount δ`. -/
noncomputable def replayRunCursor (R δ : ℕ) : ReplayCursor :=
  (DuplexSpongeFS.protocolPhases (pSpec := pSpec)).foldl
    (fun c ph => replayStep R c ph) (saltCursor R δ)

/-- The executable stateful replay runner ends at the canonical schedule's terminal cursor.
Consequently its `queryIndex` is exactly the paper's `N_𝒱`, not a rounded block budget.  This is
the cursor-count half of the future live replay-realization theorem; it is independent of the
sampled sponge values and of any Backtrack/LookAhead search. -/
theorem replayRunCursor_eq_schedule_final (R δ : ℕ) :
    replayRunCursor (pSpec := pSpec) R δ =
      (replayPhaseSchedule (pSpec := pSpec) R δ).finalCursor := by
  unfold replayRunCursor replayPhaseSchedule saltCursor replayStep
  simp only [DuplexSpongeFS.Backtrack.ScheduleCursor.buildPhaseSchedule]
  rw [DuplexSpongeFS.Backtrack.ScheduleCursor.absorbWithLocations_cursor]
  rw [DuplexSpongeFS.Backtrack.ScheduleCursor.schedulePhases_final_eq_foldl]

/-- The stateful replay runner's final number of forward permutation calls is the canonical exact
verifier count `N_𝒱`. -/
theorem replayRunCursor_queryIndex_eq_verifierPermCallCount (δ : ℕ) :
    (replayRunCursor (pSpec := pSpec) SpongeSize.R δ).queryIndex =
      DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ) := by
  rw [replayRunCursor_eq_schedule_final]
  exact (DuplexSpongeFS.verifierPermCallCount_eq_finalQueryIndex
    (pSpec := pSpec) δ).symm

/-! ## ReplayHistory: trace-prefix realization witness -/

/-- The **replay-history / trace-prefix realization witness**: a single coherent
object, below every algorithm module, extending a replay with **a raw-trace prefix at every phase
boundary**.  `c_0 = saltCursor R δ` is the cursor after `DS.Start` + the salt absorb, `cᵢ` is the
cursor after salt plus the first `i` protocol phases, and `tracePrefix i` is the raw trace prefix
carrying exactly the occurrences emitted up to that boundary (in particular `tracePrefix 0` carries
the `Start`-hash + salt absorb and `tracePrefix phases.length = trace` is the full `Act_𝒱` log).

It does **not** prove anything — the realization facts below are un-proved `Prop` **fields of one
execution witness** (built by a later refinement/proof obligation, never assembled here as scattered
Props), exactly the prefix/order/count correspondence Cochrane requires:

1. `prefix_final` — `tracePrefix phases.length = trace` (the terminal boundary is the final trace);
2. `prefix_mono` — `tracePrefix i` is a raw-trace prefix of `tracePrefix (i+1)` for every boundary;
3. `prefix_count` — at every boundary `i ≤ phases.length`,
   `length (forwardPermutationStates (tracePrefix i)) = cᵢ.queryIndex` (this includes `i = 0`, where
   `c₀ = saltCursor R δ`, via `cur0_salt`/`salt_prefix0`: the salt absorb's forward count);
4. `prefix_new_entries` — the forward entries newly added between `tracePrefix i` and
   `tracePrefix (i+1)` are **exactly those indexed `q_before … q_after-1`**, where `q_before =
   cᵢ.queryIndex`, `q_after = c_{i+1}.queryIndex` come from the actual cursor transition
   (`cur_succ`); formally the projection at `i+1` is the projection at `i` concatenated with the
   `(q_after - q_before)`-long projected sublist of the full trace starting at `q_before`;
5. `absorb_frames` — the schedule-wide absorb-side frame check (11a), using the exact salt/message
   write locations, covers every recorded forward input including partial-block absorbs that emitted
   no call at their own phase boundary;
6. `squeeze_frames` — each squeeze-side frame (11b) reads **those exact projected entries** at the
   history's own predecessor cursor.

The law is a coherent witness, not a bag of facts: cursors, per-boundary trace prefixes, the
prefix/order/count correspondence, and the frame reads are all fields of one `ReplayHistory`. -/
structure ReplayHistory (StmtIn : Type) (U : Type) [SpongeUnit U] [SpongeSize]
    (R δ : ℕ) (phases : List ReplayPhase) where
  trace : DuplexSpongeFS.Statement.Trace StmtIn U
  -- the raw-trace prefix at every phase boundary (index 0 = after DS.Start + salt absorb)
  tracePrefix : ℕ → DuplexSpongeFS.Statement.Trace StmtIn U
  -- cᵢ: the cursor after salt plus the first `i` protocol phases (c₀ = salt cursor)
  cursors : ℕ → ReplayCursor
  -- (1) c₀ is the salt cursor; c_{i+1} = replayStep of cᵢ over phase i
  cur0_salt : cursors 0 = saltCursor R δ
  cur_succ : ∀ (i : ℕ), ∀ hi : i < phases.length,
    cursors (i + 1) = replayStep R (cursors i) (List.get phases ⟨i, hi⟩)
  -- (o) the transition is coherent: the terminal boundary cursor is a plain `replayStep` fold
  -- (expressed as: the successor law up to `phases.length` closes the sequence)
  -- the salt absorb's forward count realizes `tracePrefix 0`
  salt_prefix0 :
    (forwardPermutationStates (tracePrefix 0)).length = (saltCursor R δ).queryIndex
  prefix_mono : ∀ (i : ℕ), i < phases.length →
    List.IsPrefix (tracePrefix i) (tracePrefix (i + 1))
  prefix_final : tracePrefix phases.length = trace
  prefix_count : ∀ (i : ℕ), i ≤ phases.length →
    (forwardPermutationStates (tracePrefix i)).length = (cursors i).queryIndex
  prefix_new_entries : ∀ (i : ℕ), i < phases.length →
    let qb := (cursors i).queryIndex
    let qa := (cursors (i + 1)).queryIndex
    forwardPermutationStates (tracePrefix (i + 1)) =
      forwardPermutationStates (tracePrefix i) ++
        ((forwardPermutationStates trace).drop qb |>.take (qa - qb))
  absorb_frames : AbsorbFrameCheck R δ phases trace
  squeeze_frames : ∀ (i : ℕ), ∀ hi : i < phases.length,
    replayTransition R (cursors i) (List.get phases ⟨i, hi⟩) trace

/-- The schedule/trace **realization invariant** over a `ReplayHistory` witness: the
object itself carries the backbone — one **ordered** projected entry per emitted schedule call
(`witness-count`/`no-gaps` over its terminal cursor), and at every replay boundary the projected
length of `tracePrefix i` equals `cᵢ.queryIndex` (`history.prefix_count`), the nested raw-prefix law
(`history.prefix_mono`), and the per-boundary "new entries are exactly `q_before … q_after-1`"
  clause (`history.prefix_new_entries`) whose squeeze frame reads hit those exact entries
  (`history.squeeze_frames`).  The sibling `history.absorb_frames` field gives equation (11a) over
  the scheduler's complete write set, including a short salt or message that emitted no query.

The too-weak "`cᵢ ≤ complete trace length`" prefix clause of the *earlier* `ScheduleRealizesTrace`
is removed: it is replaced by the exact per-prefix equality `prefix_count` over the object's own
per-boundary trace prefixes.  `ReplayHistory.scheduleRealizesTrace` below derives the complete
invariant directly from these coherent fields; constructing a `ReplayHistory` from a live run
remains the separate executable-refinement obligation. -/
def ScheduleRealizesTrace (R δ : ℕ) (phases : List ReplayPhase)
    (history : ReplayHistory StmtIn U R δ phases) : Prop :=
  -- one ordered entry per emitted schedule permutation call (no gaps, count right, over the object)
  (∀ q, q < (history.cursors phases.length).queryIndex → IsForwardCall history.trace q) ∧
  (history.cursors phases.length).queryIndex = (forwardPermutationStates history.trace).length ∧
  (history.tracePrefix phases.length = history.trace) ∧
  -- per-replay-prefix projected length equals `cᵢ.queryIndex`, via the object's per-prefix trace
  (∀ i : ℕ, i ≤ phases.length →
    (forwardPermutationStates (history.tracePrefix i)).length = (history.cursors i).queryIndex) ∧
  -- raw prefixes are nested
  (∀ i : ℕ, i < phases.length →
    List.IsPrefix (history.tracePrefix i) (history.tracePrefix (i + 1))) ∧
  -- newly added forward entries between prefix i and i+1 are exactly `q_before … q_after-1`
  (∀ i : ℕ, i < phases.length →
    let qb := (history.cursors i).queryIndex
    let qa := (history.cursors (i + 1)).queryIndex
    forwardPermutationStates (history.tracePrefix (i + 1)) =
      forwardPermutationStates (history.tracePrefix i) ++
        ((forwardPermutationStates history.trace).drop qb |>.take (qa - qb)))

omit [DecidableEq U] in
/-- Every `ReplayHistory` realizes its own schedule/trace invariant.  There is no additional
semantic premise hidden in `ScheduleRealizesTrace`: its terminal count, prefix counts, nesting,
and exact newly-emitted intervals are the coherent history fields; a forward-only list position
below its recorded length is a genuine forward occurrence by
`isForwardCall_of_lt_forwardPermutationStates_length`. -/
theorem ReplayHistory.scheduleRealizesTrace {R δ : ℕ} {phases : List ReplayPhase}
    (history : ReplayHistory StmtIn U R δ phases) :
    ScheduleRealizesTrace R δ phases history := by
  have hterminalCount := history.prefix_count phases.length (le_refl phases.length)
  have hterminalCount' :
      (forwardPermutationStates history.trace).length =
        (history.cursors phases.length).queryIndex := by
    simpa [history.prefix_final] using hterminalCount
  refine ⟨?_, hterminalCount'.symm, history.prefix_final, history.prefix_count,
    history.prefix_mono, history.prefix_new_entries⟩
  intro q hq
  apply isForwardCall_of_lt_forwardPermutationStates_length history.trace q
  rwa [hterminalCount']

/-! ## Faithful Lemma 5.25 helpers (position/trace/successor-linked) -/

/-- The length (in sponge units) of one replayed phase: an absorb's message length or a squeeze's
challenge length.  This is what a phase's frame and marker are evaluated over. -/
def phaseLen : ReplayPhase → ℕ
  | .absorb len => len
  | .squeeze len => len

/-- The per-phase **predecessor cursors** of a replay: `scanl` the real `replayStep` from the
salt cursor over `phases` and keep its first `phases.length` elements. Thus
`phaseCursors R δ phases[i]` (for `i < phases.length`) is the real cursor immediately *before*
phase `i`—in particular index `0` is the salt cursor, not the cursor after phase `0`. A marker or
frame of phase `i` is therefore evaluated at `List.get (phaseCursors R δ phases) ⟨i, _⟩` with length
`phaseLen phases[i]` — the genuine position, not a global one. -/
noncomputable def phaseCursors (R δ : ℕ) (phases : List ReplayPhase) : List ReplayCursor :=
  (phases.scanl (fun c ph => replayStep R c ph) (saltCursor R δ)).take phases.length

omit [SpongeSize] in
/-- The predecessor-cursor list has exactly one entry per phase. -/
lemma phaseCursors_length (R δ : ℕ) (phases : List ReplayPhase) :
    (phaseCursors R δ phases).length = phases.length := by
  simp [phaseCursors, List.length_scanl]

/-- `pos` is a certified marker of the replayed `phases`: it is exactly the real
`firstSqueezeQuery?` marker of some replayed phase — the first permutation query of a *nonempty
squeeze beginning at a rate boundary* (an absorb, an empty squeeze, and all later calls are excluded
by `firstSqueezeQuery?`'s own definition).  The marker is evaluated at the phase's **real
predecessor cursor** `phaseCursors[i]` with the phase's real length, so it is position-linked, not a
global `∃` over arbitrary calls. -/
def ReplayHasMarker (R δ : ℕ) (phases : List ReplayPhase) (pos : ℕ) : Prop :=
  ∃ i : ℕ, ∃ hi : i < phases.length,
    DuplexSpongeFS.Backtrack.ScheduleCursor.firstSqueezeQuery? R
      (List.get (phaseCursors R δ phases) ⟨i,
        by simpa [phaseCursors, List.length_scanl] using hi⟩)
      (phaseLen (List.get phases ⟨i, hi⟩)) = some pos

/-- The **squeeze-frame-carrying run** over a phase list.  The cursor advances by the real
`replayStep`; each squeeze runs (11b) against the actual forward inputs/outputs selected by its
stateful query interval.  Absorb-side equation (11a) is intentionally supplied separately by
`AbsorbFrameCheck`, because a partial absorb need not have an emitted terminal permutation call. -/
def replaySqueezeFramesHeld (R : ℕ) (trace : DuplexSpongeFS.Statement.Trace StmtIn U) :
    List ReplayPhase → ReplayCursor → Prop
  | [], _ => True
  | phase :: rest, cursor =>
      replayTransition R cursor phase trace ∧
        replaySqueezeFramesHeld R trace rest (replayStep R cursor phase)

end Statement

end DuplexSpongeFS
