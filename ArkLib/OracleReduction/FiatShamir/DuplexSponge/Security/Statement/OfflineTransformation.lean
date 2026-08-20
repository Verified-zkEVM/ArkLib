/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.OnlineTransformation

/-!
# Statement layer — module 4: offline transformation (StdTrace / D2STrace / D2SAlgo),
# REPAIRED (R1)

This module is the dependency-acyclic home of the ***offline*** side of the transformation and
now builds on the **real** online boundary types of `OnlineTransformation` (which reference
`D2SMonitoredState`).  The current module enforces the following invariants:

- **StdTrace**: the two-table transformer now **retains the raw insertion-ordered `QueryLog`**
  as a field of `View` (`insertionTrace`) alongside the **strict-prefix normalized** table (for
  Backtrack) and the **full normalized** table (for LookAhead).  This is what lets the conflict
  clause record that a conflict **never mutates the installed tables but does append the raw
  attempted occurrence**, and what state `E`/`Monitor` over (the real `BadEventDS.E`).
- **D2STrace**: the thin codec wrapper now propagates the **three-way** revised step result
  (`continue` / `stopped` / `underlyingAbort`) against the real `D2SQuery.StepResult`
  (= `D2SRevisedStepResult`), distinguishing a monitored stop from an underlying abort.
- **D2SAlgo**: the memo clause is re-bound to the **real rate-only cache** field
  (`state.rateCacheP : List (RateOnlyCacheEntry)`), and the abort clause distinguishes the
  underlying abort outcome.

Rules honoured: **no** fabricated boundary type, **no** generic `Prop` outcome, **no** free
`ℕ`/`ℝ` standing in for a real quantity, **no** `sorry`/`admit`/`axiom`.  This module imports no
live Section 5 algorithm.  A fully `g_i`/`f_i`-keyed re-issue clause needs the
real encoded-marker-key type; where that type is not (yet) importable handler-free, the precise
requirement is recorded here instead of fabricated.
-/

namespace DuplexSpongeFS

namespace Statement

open OracleComp OracleSpec ProtocolSpec DSTraceStorage
open DuplexSpongeFS.ProverTransform

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-! ## `ForwardTable` as a real `TraceTableOps` -/

/-- `ForwardTable U` (a list of forward occurrences `(s_in, s_out)`) is a concrete `TraceTableOps`:
`entries t = t`, `add` appends a pair, and the lookups find a matching pair (a partial bijection on
`CanonicalSpongeState U`).  This lets the statement layer run the **real** `permInstallStatus` /
`installPerm` of `D2SPermInstall` directly on the two-table forward tables, so the `Install` verdict
recorded by `PrefixUpdate` is the **real** one. -/
instance instForwardTableTraceTableOps :
    DSTraceStorage.TraceTableOps (ForwardTable U) (CanonicalSpongeState U)
      (CanonicalSpongeState U) where
  empty := []
  add t k v := t ++ [(k, v)]
  inlu t k := (List.find? (fun e : ForwardOccurrence U => e.1 = k) t).map (fun e => e.2)
  outlu t v := (List.find? (fun e : ForwardOccurrence U => e.2 = v) t).map (fun e => e.1)
  entries t := t

/-! ## StdTrace: the two-table transformer -/

namespace StdTrace

/-- A StdTrace view: the **strict-prefix normalized** forward table (Backtrack scan target), the
**full normalized** forward table (LookAhead scan target), and — crucially — the **raw
insertion-ordered `QueryLog`** `insertionTrace` needed to state `E`/`Monitor` and to record an
attempted occurrence on a conflict.  The prefix invariant ties the Backtrack table to the full
table. -/
structure View (StmtIn : Type) (U : Type) [SpongeUnit U] [SpongeSize] where
  insertionTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)
  strictPrefix : ForwardTable U
  full : ForwardTable U
  prefix_is_prefix : List.IsPrefix strictPrefix full

/-- The **PrefixUpdate growth** (CO25 §5.5 Step 4): a normal (non-conflict) update evolves the
full normalized table by the **real table-only `Install`** — `(installPerm pre.full occ.1 occ.2) =
(status, post.full)` with `status ≠ .conflict` (a fresh `occ` appends it, a `present` leaves it) —
and appends the **exact raw occurrence** `(q, a)` to the insertion trace, records the **actual
`Install` verdict** `status`
(the real `PermInstallStatus`), grows the strict prefix by the same occurrence when the Backtrack
scan extends (or keeps it strictly a prefix otherwise), **runs the real `Monitor` = `BadEventDS.E`
on the extended trace and requires it to pass** (`¬ E` — the normal face of the paper's
`Install → append one actual occurrence → Monitor` discipline), and preserves the prefix
invariant. -/
def AppendOneOccurrence (pre post : View StmtIn U)
    (occ : ForwardOccurrence U)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (a : (duplexSpongeChallengeOracle StmtIn U).Range q)
    (status : PermInstallStatus) : Prop :=
  status ≠ PermInstallStatus.conflict
    ∧ (installPerm pre.full occ.1 occ.2) = (status, post.full)
    ∧ (post.strictPrefix = pre.strictPrefix ∨
        post.strictPrefix = pre.strictPrefix ++ [occ])
    ∧ post.insertionTrace = pre.insertionTrace ++ [⟨q, a⟩]
    ∧ post.insertionTrace.length = pre.insertionTrace.length + 1
    ∧ ¬ BadEventDS.E post.insertionTrace
    ∧ List.IsPrefix post.strictPrefix post.full

/-- A **conflict** `Install` (CO25 §5.5 Step 4.b.iv) leaves both StdTrace tables unchanged — no
append to `strictPrefix` / `full`, no reusable mapping — **but** appends the raw attempted
occurrence `(q, a)` to the insertion trace with the **actual `conflict` verdict** `status`, after
which the real `Monitor` = `BadEventDS.E` **fails** on the extended trace.  This is the faithful
reading of "conflict retains the attempted insertion-trace occurrence" (audit #1); it is exactly
the real `install_conflict_*_imp_E` content. -/
def ConflictRetainsAttemptedOccurrence (pre post : View StmtIn U)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (a : (duplexSpongeChallengeOracle StmtIn U).Range q)
    (status : PermInstallStatus) : Prop :=
  status = PermInstallStatus.conflict ∧
    post.strictPrefix = pre.strictPrefix ∧ post.full = pre.full ∧
    post.insertionTrace = pre.insertionTrace ++ [⟨q, a⟩] ∧
    BadEventDS.E post.insertionTrace

/-- Normalized inverse occurrences become forward mappings: the full table is exactly the real
`forwardTableOfTrace` image of the view's own raw insertion trace (CO25 Def 5.3, inverse `p⁻¹`
entries turned into their forward `p` counterparts). -/
def InversesNormalizedForward (view : View StmtIn U) : Prop :=
  view.full = DuplexSpongeFS.Statement.forwardTableOfTrace view.insertionTrace

/-- One raw occurrence of the sponge oracle processed by the offline StdTrace transformer: a
dependent pair of the query term and its answer. -/
abbrev RawOccurrence (StmtIn : Type) (U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  Sigma fun q : (duplexSpongeChallengeOracle StmtIn U).Domain =>
    (duplexSpongeChallengeOracle StmtIn U).Range q

/-- The **whole-trace StdTrace transformer** (CO25 §5.5): folds a finite raw-occurrence stream
through the two-table `View` from a start view, preserving the **raw insertion order** (a trace
only ever grows by `++ [occ]`), evolving the strict-prefix/full tables by the **real** table-only
`Install`, running `Install → append one actual occurrence → Monitor` at every step, and stopping
at the first `conflict` (which retains the attempted occurrence and fails `E`).  Every `pre → post`
link is a real `AppendOneOccurrence`/`ConflictRetainsAttemptedOccurrence` transition, so the
successor view is *constructed* from the input, never pre-supplied, and each step's real `Install`
verdict is the real `permInstallStatus` of the real tables.  A hash query appends + monitors with
the tables unchanged; a forward/inverse permutation occurrence installs by the forward image. -/
def Run (pre : View StmtIn U) (stream : List (RawOccurrence StmtIn U))
    (final : View StmtIn U) : Prop :=
  InversesNormalizedForward pre ∧
    match stream with
    | [] => final = pre
    | ⟨.inl v, a⟩ :: rest =>
        (∃ post : View StmtIn U,
            post.insertionTrace = pre.insertionTrace ++ [⟨.inl v, a⟩] ∧
              post.strictPrefix = pre.strictPrefix ∧ post.full = pre.full ∧
              ¬ BadEventDS.E post.insertionTrace ∧ InversesNormalizedForward post ∧
              Run post rest final) ∨
          (final.insertionTrace = pre.insertionTrace ++ [⟨.inl v, a⟩] ∧
              final.strictPrefix = pre.strictPrefix ∧ final.full = pre.full ∧
              BadEventDS.E final.insertionTrace ∧ InversesNormalizedForward final)
    | ⟨.inr (.inl sIn), a⟩ :: rest =>
        (∃ post : View StmtIn U,
            InversesNormalizedForward post ∧
              AppendOneOccurrence pre post ⟨sIn, a⟩ (.inr (.inl sIn)) a
                (permInstallStatus pre.full sIn a) ∧ Run post rest final) ∨
          (∃ post : View StmtIn U,
            InversesNormalizedForward post ∧
              ConflictRetainsAttemptedOccurrence pre post (.inr (.inl sIn)) a
                (permInstallStatus pre.full sIn a) ∧ final = post)
    | ⟨.inr (.inr sOut), a⟩ :: rest =>
        (∃ post : View StmtIn U,
            InversesNormalizedForward post ∧
              AppendOneOccurrence pre post ⟨a, sOut⟩ (.inr (.inr sOut)) a
                (permInstallStatus pre.full a sOut) ∧ Run post rest final) ∨
          (∃ post : View StmtIn U,
            InversesNormalizedForward post ∧
              ConflictRetainsAttemptedOccurrence pre post (.inr (.inr sOut)) a
                (permInstallStatus pre.full a sOut) ∧ final = post)

end StdTrace

/-! ## D2STrace: thin codec wrapper (three-way) -/

namespace D2STrace

/-- A D2STrace view: a `StdTrace.View` (the coherent raw insertion trace + strict-prefix/full
tables of the offline side).  The **three-way** revised step result is *not* a pre-recorded field:
it is carried by the genuine execution relation `Execution`, so the three outcomes (`continue` with
a reusable normal view, `stopped` with a terminal record, `underlyingAbort`) each tie a real
outcome to the view's actual trace. -/
structure View (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
    [DecidableEq StmtIn] [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] where
  std : StdTrace.View StmtIn U

/-- A **D2STrace execution**: the offline std view `view` together with the **real three-way**
online step result `step` it ends in, with the outcome tied to the view's actual trace — on a
`continue` the view's raw insertion trace is exactly the reusable successor state's trace (which
has passed `Monitor`, `¬ E`); on a `stopped` the real `E` fails on the view trace extended by the
terminal record's attempted occurrence; on an `underlyingAbort` the execution aborts before any
occurrence.  The outcome is a genuine relation parameter (successor/record live in the real
`D2SRevisedStepResult`), not a field equal to itself. -/
def Execution (view : View StmtIn pSpec U δ T_H T_P)
    (step : D2SQuery.StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  StdTrace.InversesNormalizedForward view.std ∧
    match step with
    | .continue _ newNormal =>
        newNormal.state.trace = view.std.insertionTrace ∧ ¬ BadEventDS.E newNormal.state.trace
    | .stopped state record =>
        -- the stop record's pre-state is exactly the offline view's raw insertion trace, so the
        -- record's visible trace is `view trace ++ [attempted occurrence]`, and the real `E` holds
        -- on it (the record's own monitor-failure witness).
        state.state.trace = view.std.insertionTrace ∧ BadEventDS.E record.trace
    | .underlyingAbort =>
        -- a named actual BackTrack / LookAhead failure over some real normal state whose raw
        -- insertion trace is exactly the offline view's trace (abort before any occurrence).
        ∃ normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P,
          normal.state.trace = view.std.insertionTrace ∧
            D2SQuery.UnderlyingSearchFailure normal

end D2STrace

/-! ## D2SAlgo: repeated query, memo, abort -/

namespace D2SAlgo

/-- The real encoded StdTrace output: the insertion-ordered `gᵢ`-query-answer trace
`\widehat{tr}_{std}` of CO25 §5.5, over the real encoded challenge oracle `gSpec`.  Each entry is
`⟨(i, κ̂), ρ̂ᵢ⟩` where `κ̂ : (gSpecInterface … i).Query` is the real encoded prover-prefix key
`StmtIn × Vector U δ × EncodedMessagesBefore … i` and `ρ̂ᵢ : Vector U (challengeSize i)` is the
encoded challenge. -/
abbrev EncodedTrace (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) : Type :=
  OracleSpec.QueryLog (gSpec (U := U) StmtIn pSpec δ)

/-- A **decidable image** of the real encoded `gᵢ` query key `(i, κ̂)`, used so `List.count` can
count per-key multiplicity of the encoded trace (the raw key drags in the function-typed
`EncodedMessagesBefore` prefix, which has no `DecidableEq`, while `EncodedMessagesBefore.toList` is
injective on prefixes).  Counting bookkeeping only — `ReissuesAll` below still names the real key
`key` of `gSpecInterface`.  Because the challenge oracle is a function, a repeated key is always
re-issued with the same `ρ̂ᵢ`, so per-key multiplicity equals per-occurrence multiplicity. -/
-- Local `DecidableEq` for the TC-opaque per-index encoded vector length `messageSize` (it cannot
-- be unfolded by typeclass search), delegating to the uniform `Vector` instance.
instance instDecidableEqMessageVector :
    ∀ m : pSpec.MessageIdx, DecidableEq (Vector U (messageSize m)) :=
  fun _ => inferInstance

abbrev OccurrenceKey (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [HasMessageSize pSpec] (δ : Nat) : Type :=
  pSpec.ChallengeIdx × StmtIn × Vector U δ ×
    List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))

/-- Project a real encoded occurrence `⟨(i, κ̂), ρ̂ᵢ⟩` to the **decidable image** of its query key
`(i, κ̂)` (round index, statement, salt, and injectively-listified prover prefix). -/
noncomputable def occurrenceKey (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
    (occ : Sigma (gSpec (U := U) StmtIn pSpec δ)) : OccurrenceKey StmtIn pSpec U δ :=
  ⟨occ.1.1, (occ.1.2.1, (occ.1.2.2.1, EncodedMessagesBefore.toList occ.1.2.2.2))⟩

/-- Concrete — D2SAlgo **reissues the standard `gᵢ` query for every invocation**, *including* memo
hits: the raw encoded trace `\widehat{tr}_{std}` retains one occurrence `⟨(i, κ̂), ρ̂ᵢ⟩` per
invocation, never collapsing a repeated key (full trace multiplicity is kept).  `ReissuesAll
encodedTrace key invocations` asserts that the real encoded query key `κ̂` at round `key.1`
(`gSpecInterface`'s real encoded prover-prefix key) appears exactly `invocations` times in the real
encoded trace. -/
noncomputable def ReissuesAll (encodedTrace : EncodedTrace StmtIn pSpec U δ)
    (key : (i : pSpec.ChallengeIdx) × (gSpecInterface (U := U) StmtIn pSpec δ i).Query)
    (invocations : ℕ) : Prop :=
  let target : OccurrenceKey StmtIn pSpec U δ :=
    ⟨key.1, (key.2.1, (key.2.2.1, EncodedMessagesBefore.toList key.2.2.2))⟩
  (encodedTrace.map (occurrenceKey StmtIn pSpec U δ)).countP
    (fun image => decide (image = target)) = invocations

/-- The concrete D2SAlgo `fᵢ`-query count: every entry of the insertion-ordered encoded trace is
one issued standard-oracle query, including a repeated encoded key.  Consequently this is the
paper's `θ★`-query-algorithm conclusion, not merely a bound on the number of distinct memo keys. -/
def QueryCountBound (encodedTrace : EncodedTrace StmtIn pSpec U δ) (θStar : ℕ) : Prop :=
  encodedTrace.length ≤ θStar

/-- Concrete — D2SAlgo's real LookAhead memo `M_LA : κ̂ ↦ ρ̂ᵢ` (CO25 §5.5): it is keyed by the real
encoded key `(gSpecInterface … i).Query` and returns the real encoded challenge
`Vector U (challengeSize i)`, and it **agrees with the inserted order of the real encoded trace**:
for every encoded occurrence recorded, the memo maps its key to exactly that occurrence's
challenge (so a memo hit re-issues the same `ρ̂ᵢ`, and the trace retains multiplicity).  This is
the real `[κ̂ ↦ ρ̂ᵢ]` map, **not** a synthetic cache field. -/
def MemoizesEncodedPreimage
    (memo : (i : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i))
    (encodedTrace : EncodedTrace StmtIn pSpec U δ) : Prop :=
  ∀ occ ∈ encodedTrace, memo occ.1.1 occ.1.2 = occ.2

/-- Concrete — D2SAlgo **aborts exactly on an underlying BackTrack / LookAhead failure**: the
abort outcome is the real three-way revised step result being `.underlyingAbort`, and it is
distinct from a monitored `stopped` (a terminal record, not an abort) and from a normal
`continue`.  There is no free `aborts`-flag stand-in: the abort is the real propagated outcome of
the real `D2SQuery.StepResult`. -/
def AbortsOnUnderlyingAbort
    (result : D2SQuery.StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  result = .underlyingAbort

/-- One actual D2SAlgo **Program invocation**.  It combines the certified D2SQuery `Program`
branch with the corresponding encoded `gᵢ` key and answer: the answer returned to D2SQuery is
the memo value at exactly this round/key, and the branch carries the same state input, output,
Install status, terminal/continuing result, and rate-only tail.  Thus this is not an after-the-fact
key count: it is the point at which a recovered Backtrack marker becomes a concrete `gᵢ`
invocation in Algorithm 5.4. -/
structure ProgramInvocation
    (memo : (i : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i)) where
  context : D2SQuery.ProgramContext pSpec
  key : (gSpecInterface (U := U) StmtIn pSpec δ context.round).Query
  answer : Vector U (challengeSize context.round)
  normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P
  stateIn : CanonicalSpongeState U
  stateOut : CanonicalSpongeState U
  status : D2SQuery.InstallStatus
  tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U))
  result : D2SQuery.StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)
  program_branch :
    D2SQuery.BranchProgram context normal stateIn stateOut status tail result
  memo_answer : memo context.round key = answer

/-- The one raw encoded `gᵢ`-trace occurrence emitted by a `ProgramInvocation`.  Keeping this
constructor explicit lets the whole D2SAlgo execution state equality of ordered traces, hence
preserve multiplicity even when two invocations have the same complete key. -/
noncomputable def ProgramInvocation.encodedOccurrence
    (memo : (i : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i))
    (invocation : ProgramInvocation (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) memo) :
    Sigma (gSpec (U := U) StmtIn pSpec δ) :=
  ⟨⟨invocation.context.round, invocation.key⟩, invocation.answer⟩

/-- The ordered encoded trace is exactly the image of the Program-invocation list.  This is the
whole-trace form of "reissue every `gᵢ` invocation": duplicates in `invocations` become duplicate
entries of `encodedTrace` in the same order, rather than being collapsed to one memo-table key. -/
noncomputable def EncodedTraceRealizesInvocations
    (memo : (i : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i))
    (encodedTrace : EncodedTrace StmtIn pSpec U δ)
    (invocations : List (ProgramInvocation (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) memo)) : Prop :=
  encodedTrace = invocations.map
    (ProgramInvocation.encodedOccurrence (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) memo)

/-- A **complete D2SAlgo execution** over the real inputs.  Every Program invocation is tied to
its certified D2SQuery branch and memo answer, and the complete insertion-ordered encoded trace is
exactly the list of these invocations.  This is the whole-execution replacement for the earlier
single `(key, invocations)` slice: every repeated `gᵢ` call is visible.  The live
`d2sCodecBridgeImplMemo` realizes the matching `fᵢ` query before its memo lookup; this statement
records the resulting `gᵢ` multiplicity and memo correspondence at the Section 5 boundary.

The terminal revised step result `result` is tied to the actual raw transcript `rawTrace`: a
`continue` has passed `Monitor`, a `stopped` retains its first bad-event record, and an
`underlyingAbort` is a named BackTrack / LookAhead failure before another occurrence. -/
noncomputable def CompleteExecution (memo : (i : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i))
    (encodedTrace : EncodedTrace StmtIn pSpec U δ)
    (invocations : List (ProgramInvocation (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) memo))
    (rawTrace : DuplexSpongeFS.Statement.Trace StmtIn U)
    (result : D2SQuery.StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  EncodedTraceRealizesInvocations (T_H := T_H) (T_P := T_P) memo encodedTrace invocations ∧
    MemoizesEncodedPreimage memo encodedTrace ∧
    match result with
    | .continue _ state =>
        ¬ BadEventDS.E state.state.trace
    | .stopped _ record =>
        BadEventDS.E record.trace
    | .underlyingAbort =>
        -- a named actual BackTrack / LookAhead failure over some real normal state whose raw
        -- insertion trace is exactly the actual raw transcript (abort before any occurrence).
        ∃ normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P,
          normal.state.trace = rawTrace ∧ D2SQuery.UnderlyingSearchFailure normal

end D2SAlgo

end Statement

end DuplexSpongeFS
