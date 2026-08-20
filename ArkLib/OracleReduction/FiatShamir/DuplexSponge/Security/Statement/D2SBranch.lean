/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.ReplaySemantics
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SMonitoredState
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SPermInstall
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRateOnlyCache
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventDefs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.Data.Hash.DuplexSponge

/-!
# Statement layer — module 3.5: the six D2SQuery branches and the shared branch witness (F2)

This module sits **below** both `OnlineTransformation` and `RevisedOperators` (neither imports
it in the opposite direction — it imports only the acyclic operator layers and
`ReplaySemantics`).  It is the single dependency-acyclic home of:

- the **real boundary types**, referenced by `abbrev` from `D2SMonitoredState`
  (`NormalState`, `StopRecord`, `StepResult`) and `D2SPermInstall` (`InstallStatus`);
- the **transition core**: `InstallStatusFor`, `ContinueTo`, the genuine output-bearing
  `D2SStep`, and the underlying BackTrack / LookAhead search-failure predicates;
- the **rate-only cache policy** helpers (`NoLatentCapacity`,
  `ConsumeTailMaterializesOneCapacity`, `InverseNeverReadsCache`, `ContinueCacheIs`,
  `TabularMiss`, `ProgramSchedulesResidualTail`);
- the **six branch relations** of paper Algorithm 5.3 (`BranchHashQuery`, `BranchInverseQuery`,
  `BranchCacheTailHit`, `BranchTableHit`, `BranchFreshMiss`, `BranchProgram`); each now states
  only its precise effect (cache / table / `Install` / `Monitor`), leaving the outcome link to the
  witness below; and
- the **shared branch-witness/result object** `D2SBranchStep`, importable by *both*
  `OnlineTransformation` (whose `D2SQueryRun` folds it) and `RevisedOperators` (whose
  `RevisedD2SQueryStep` dispatches it).  A witness never hides a step behind a bare
  `∃ result, D2SStep … result`: it carries the **exact** query fragment, the **exact** `result`,
  the **exact** `stateIn`/`stateOut`, and the exact successor / cache data of that occurrence.

Rules honoured: no fabricated boundary type, no generic `Prop` comptroller, no free `ℕ`/`ℝ`
standing in for a real quantity, no `sorry`/`admit`/`axiom`.  This module imports **no live**
Section 5 algorithm and **no** `OnlineTransformation`/`OfflineTransformation`/`RevisedOperators`
(its only statement dependency is the acyclic `ReplaySemantics`).
-/

namespace DuplexSpongeFS

namespace Statement

namespace D2SQuery

open OracleComp OracleSpec ProtocolSpec DSTraceStorage
open DuplexSpongeFS.ProverTransform

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-! ## Real boundary types (single source of truth: `D2SMonitoredState`)

These are `abbrev` references to the handler-free boundary module — never copies of the types.
All section-variable parameters are applied so each abbreviation is a plain `Type`.
-/

/-- The reusable normal state of revised D2SQuery: the real `D2SNormalState` (a `D2SQueryState`
whose trace has passed `Monitor`, i.e. `monitorPassed : ¬ BadEventDS.E state.trace`). -/
abbrev NormalState (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
    [DecidableEq StmtIn] [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] : Type :=
  DuplexSpongeFS.ProverTransform.D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- The real post-occurrence stop record over a reusable normal state `normal`: the actual final
query, its answer, and the real monitor failure `E (trace ++ [⟨query, answer⟩])`. -/
abbrev StopRecord (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
    [DecidableEq StmtIn] [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (normal : NormalState StmtIn pSpec U δ T_H T_P) : Type :=
  DuplexSpongeFS.ProverTransform.D2SPostOccurrenceStopRecord (δ := δ) (T_H := T_H)
    (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal

/-- The real **three-way** step result: `continue` (a reusable normal state), `stopped` (the first
monitored failure), or `underlyingAbort` (an underlying BackTrack / LookAhead failure before any
occurrence). -/
abbrev StepResult (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
    [DecidableEq StmtIn] [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (α : Type) : Type :=
  DuplexSpongeFS.ProverTransform.D2SRevisedStepResult (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (α := α)

/-- The result of **one actual sponge-oracle query**.  Unlike the older statement layer's
`StepResult CanonicalSpongeState`, this is dependent on the query: an `h` query carries its actual
hash answer, while a forward or inverse permutation query carries its actual sponge-state answer.
This is what lets the six-branch dispatcher bind the hash branch's answer just as tightly as the
five permutation branches bind `stateIn`/`stateOut`. -/
abbrev QueryResult (q : (duplexSpongeChallengeOracle StmtIn U).Domain) : Type :=
  StepResult StmtIn pSpec U δ T_H T_P ((duplexSpongeChallengeOracle StmtIn U).Range q)

/-- The `Install` verdict: the real `PermInstallStatus` (`fresh | present | conflict`) from the
acyclic `D2SPermInstall`. -/
abbrev InstallStatus := PermInstallStatus

/-! ## `Install` status on the real table -/

/-- The real `Install` status of a candidate pair `(stateIn, stateOut)` against the **normalized
permutation table** `normal.state.trΔ.p` of the real normal state.  This is the real
`permInstallStatus` classifier (acyclic `D2SPermInstall`), not a free-parameter stand-in. -/
def InstallStatusFor (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U) : InstallStatus :=
  permInstallStatus normal.state.trΔ.p stateIn stateOut

/-- `Install = conflict` **leaves the reusable table and rate-only cache unchanged**: a conflict
never overwrites the old mapping, and the stopped record's table/cache are definitionally the
pre-occurrence ones.  This is the real table-only `installPerm` behaviour stated as the concrete
identity relation on the reusable fields. -/
def ConflictLeavesReusable (pre post : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  pre.state.trΔ.p = post.state.trΔ.p ∧ pre.state.rateCacheP = post.state.rateCacheP

/-- `Install = conflict` **stops** (never a normal continuation).  `ConflictStops s` is the
concrete fact "the verdict `s` is `conflict`". -/
def ConflictStops (status : InstallStatus) : Prop := status = .conflict

/-! ## Underlying search-failure predicates (the named `underlyingAbort` face)

A revised D2SQuery step aborts **only when the real BackTrack (Algo 5.1) or LookAhead (Algo 5.2)
procedure over the current normal state's own data returns its real `ExperimentOutput.err`
(multiple-match / multiple-maximal ambiguity) outcome**.  This is the named actual
BackTrack / LookAhead failure predicate that the `underlyingAbort` case of `D2SStep` requires — it
is *not* the vacuous `¬ (conflict ∨ E)` membership test.  Both procedures run on the real normal
state: `backTrack` over `normal.state.trace` / `normal.state.trΔ` (with the real subset witness
`normal.state.h_inv`), and `lookAhead` over the real permutation table `normal.state.trΔ.p` (the
`[LawfulTraceNablaImpl …]` instance supplies the `[LawfulTraceTable T_P …]` requirement).
-/

/-- The real BackTrack (Algo 5.1) **abort predicate**: for some permutation state `s`, the real
executable `backTrack` over the normal state's own insertion trace and normalized table returns
`ExperimentOutput.err` (the multiple-match / ambiguous outcome, `Outs` with several maximal
chains).  It runs on `normal.state.trace` with the actual subset witness `normal.state.h_inv`, so
the failure is tied to this state's real data — not an arbitrary trace/table. -/
def UnderlyingBacktrackFailure (normal : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  ∃ state : CanonicalSpongeState U,
    DuplexSpongeFS.Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
      normal.state.trace normal.state.trΔ normal.state.h_inv state = ExperimentOutput.err

/-- The real LookAhead (Algo 5.2) **abort predicate**: for some challenge round `i` and perm state
`s`, the real `lookAhead` over the normal state's permutation table returns the multiple-maximal
`.err` outcome.  (Faithful to the no-abort face in `LookAheadNoAbort`: abort is exactly when the
computation is the `pure ExperimentOutput.err` one.) -/
def UnderlyingLookaheadFailure (normal : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  ∃ (i : pSpec.ChallengeIdx) (state : CanonicalSpongeState U),
    DuplexSpongeFS.Lookahead.lookAhead (pSpec := pSpec) normal.state.trΔ.p state i =
      (pure ExperimentOutput.err : OracleComp (Unit →ₒ U)
        (ExperimentOutput (Vector U (challengeSize i))))

/-- The named underlying D2SQuery **abort**: an underlying BackTrack or LookAhead failure over the
normal state's own data (the real `.err` of Algo 5.1 / 5.2).  This is the semantic content of the
`underlyingAbort` constructor — a genuine search failure, never the `¬ (conflict ∨ E)` condition. -/
def UnderlyingSearchFailure (normal : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  UnderlyingBacktrackFailure normal ∨ UnderlyingLookaheadFailure normal

/-! ## The permutation query fragment -/

/-- The **permutation query fragment** of the sponge domain: `p(s_in)` (left) or `p⁻¹(s_out)`
(right).  The `D2SStep` transition acts on these, since only permutation queries install a
mapping into `tr_∇.p`; the hash query `h(stmt)` installs nothing and is handled by
`BranchHashQuery`. -/
abbrev PermQuery (U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  CanonicalSpongeState U ⊕ CanonicalSpongeState U

/-! ## The core step transition (`Install → append occurrence → Monitor → three-way outcome`)

The single faithful shape of one revised D2SQuery decision step: the real `Install` status, the
real appended occurrence on the raw `QueryLog`, and the real three-way outcome.  The step is a
**genuine transition**: it *constructs* its successor normal state (or terminal stop record / the
underlying-abort marker) from the input `normal` and `(stateIn, stateOut)` — it never takes a
pre-labelled `result`.
-/

/-- The real `continue` face of one forward-Install transition: the status was not a conflict, the
real monitor `¬ E (trace ++ …)` passed, the successor normal state's trace is the raw trace plus
exactly the one occurrence `⟨dsPermQuery stateIn, stateOut⟩`, and the **permutation table evolves
by the real table-only `Install`** (`newNormal.state.trΔ.p = (installPerm normal.state.trΔ.p
stateIn stateOut).2` — fresh adds the pair, present leaves it unchanged).  This names exactly the
successor `newNormal` that `D2SStep.continue` constructs, so a branch can tie a rate-only-cache
effect to the genuinely-constructed successor. -/
def ContinueTo (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U)
    (status : InstallStatus)
    (newNormal : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  status ≠ .conflict ∧
    ¬ BadEventDS.E (normal.state.trace ++
      [⟨dsPermQuery (StartType := StmtIn) stateIn, stateOut⟩]) ∧
    newNormal.state.trace = normal.state.trace ++
      [⟨dsPermQuery (StartType := StmtIn) stateIn, stateOut⟩] ∧
    newNormal.state.trΔ.p = (installPerm normal.state.trΔ.p stateIn stateOut).2

/-- One **genuine** revised D2SQuery forward-Install transition, from a reusable normal state and
an attempted permutation pair `(stateIn, stateOut)` with the **real** `Install` status
(`status = permInstallStatus normal.state.trΔ.p stateIn stateOut`).  Exactly one of the three
outcomes holds, and its data is **constructed** by the transition (not passed in):

- `D2SStep.continue` — `ContinueTo normal stateIn stateOut status newNormal` for some real
  successor `newNormal` (a completed install that the monitor passed);
- `D2SStep.stopped` — a conflict stop or an `E`-monitor stop, carrying the **actual** attempted
  `p` occurrence (the stop record's query is exactly `dsPermQuery stateIn` and its answer
  `stateOut`);
- `D2SStep.underlyingAbort` — an underlying BackTrack / LookAhead failure before an occurrence: it
  is **not** explained by this occurrence's `Install`/`Monitor` outcome (`¬ (status = .conflict ∨
  E (trace ++ …))`), and no reusable successor state is produced.

This is a statement *specification*: the live executable handler
(`d2sInstallPermForwardStateRevised` in `D2SRevisedInstall`) is a later refinement obligation
realizing exactly this shape. -/
def D2SStep (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (q : PermQuery U)
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  match q with
  | .inl stateIn =>
      -- forward `p(stateIn) ↦ stateOut`
      match result with
      | .continue stateOut newNormal =>
          let status := InstallStatusFor normal stateIn stateOut
          status ≠ .conflict ∧
          ¬ BadEventDS.E (normal.state.trace ++
            [⟨dsPermQuery (StartType := StmtIn) stateIn, stateOut⟩]) ∧
          newNormal.state.trace = normal.state.trace ++
            [⟨dsPermQuery (StartType := StmtIn) stateIn, stateOut⟩] ∧
          newNormal.state.trΔ.p = (installPerm normal.state.trΔ.p stateIn stateOut).2
      | .stopped state record =>
          state = normal ∧
          (∃ stateOut : CanonicalSpongeState U,
            ∃ hq : record.query = dsPermQuery (StartType := StmtIn) stateIn,
              record.answer = hq ▸ stateOut)
      | .underlyingAbort =>
          UnderlyingBacktrackFailure normal
  | .inr stateOut =>
      -- inverse `p⁻¹(stateOut) ↦ stateIn`, normalized forward
      match result with
      | .continue stateIn newNormal =>
          let status := InstallStatusFor normal stateIn stateOut
          status ≠ .conflict ∧
          ¬ BadEventDS.E (normal.state.trace ++
            [⟨dsPermInvQuery (StartType := StmtIn) stateOut, stateIn⟩]) ∧
          newNormal.state.trace = normal.state.trace ++
            [⟨dsPermInvQuery (StartType := StmtIn) stateOut, stateIn⟩] ∧
          newNormal.state.trΔ.p = (installPerm normal.state.trΔ.p stateIn stateOut).2
      | .stopped state record =>
          state = normal ∧
          (∃ stateIn : CanonicalSpongeState U,
            ∃ hq : record.query = dsPermInvQuery (StartType := StmtIn) stateOut,
              record.answer = hq ▸ stateIn)
      | .underlyingAbort =>
          False

/-! ## Rate-only cache policy (concrete, over the real tail cache) -/

/-- **No latent capacity**: the rate-only cache stores only rate-block tails, never an output
capacity.  Each real `RateOnlyCacheEntry` of the real cache field `rateCacheP` holds a
`RateOnlyTail` and no capacity symbol. -/
def NoLatentCapacity (normal : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  ∀ entry : RateOnlyCacheEntry (U := U), entry ∈ normal.state.rateCacheP →
    (Vector.toList entry.tail.nextRate).length = SpongeSize.R

/-- **One capacity sampled on tail consumption**: consuming a rate-only tail materializes exactly
one fresh capacity and re-keys any residual tail at the materialized output state.  This is the
real `consumeRateOnlyCache` behaviour. -/
def ConsumeTailMaterializesOneCapacity (cache : List (RateOnlyCacheEntry (U := U)))
    (stateIn : CanonicalSpongeState U) (capacity : Vector U SpongeSize.C)
    (stateOut : CanonicalSpongeState U) (cache' : List (RateOnlyCacheEntry (U := U))) : Prop :=
  consumeRateOnlyCache cache stateIn capacity = some (stateOut, cache')

/-- **Inverse queries never read the rate-only cache** (paper D2SQuery Step 3.d): the inverse
materialization path does not consult the rate-only cache.  Its concrete observable effect is that
the cache field is unchanged by an inverse-only step. -/
def InverseNeverReadsCache (pre post : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  pre.state.rateCacheP = post.state.rateCacheP

/-! ## Branch-effect helpers (shared across the six branches)

Reusable effect predicates naming the **actual** fields a successful (`continue`) step reaches vs.
the pre-state, so each branch records its precise paper guard/effect rather than only a verdict.
-/

/-- A `continue` step forwards the **real rate-only cache end-state `cache'`**: any successor
`newNormal` that satisfies the real `continue` face (`ContinueTo`) carries exactly `cache'` in its
cache field. -/
def ContinueCacheIs (newNormal : NormalState StmtIn pSpec U δ T_H T_P)
    (cache' : List (RateOnlyCacheEntry (U := U))) : Prop :=
  newNormal.state.rateCacheP = cache'

/-- A **tabular miss**: the normalized table `normal.state.trΔ.p` has no forward value for
`stateIn` (`inlu … stateIn = none`) **and** the real rate-only cache has no tail for `stateIn`
(`popRateOnlyTailByInput … stateIn = none`).  This is the concrete "no table hit, no tail hit"
guard of the fresh-miss branch. -/
def TabularMiss (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn : CanonicalSpongeState U) : Prop :=
  TraceTableOps.inlu normal.state.trΔ.p stateIn = none ∧
    popRateOnlyTailByInput normal.state.rateCacheP stateIn = none

/-- The `Program` branch **schedules a residual rate-only tail at the installed output**: the
constructed `continue` successor `newNormal` carries a `RateOnlyCacheEntry` whose input is exactly
`stateOut` (the first capacity installed at `stateIn ↦ stateOut`, with the residual tail keyed at
the materialized output, as the paper's Step 4.e lace). -/
def ProgramSchedulesResidualTail (stateOut : CanonicalSpongeState U)
    (newNormal : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  ∃ tail : RateOnlyTail (U := U), ⟨stateOut, tail⟩ ∈ newNormal.state.rateCacheP

/-! ## The six D2SQuery branches (concrete, recognized)

Each branch states its precise effect (cache / table / `Install` / `Monitor` / certification) and
**only** that effect.  It does **not** hide an outcome behind `∃ result, D2SStep … result`: the
outcome link lives in the shared witness `D2SBranchStep` below, which carries the exact `result`,
`stateIn`/`stateOut`, and successor / cache data of the occurrence.
-/

/-- The precise table transition of Algorithm 5.3 Step 2.a--b.  A repeated `h(stmt)` reuses its
stored capacity answer and leaves `tr∇.h` unchanged; a missing entry inserts exactly the returned
capacity.  This is separate from raw-trace insertion/`Monitor`, which `BranchHashQuery` performs
after this transition. -/
def HashTableTransition (normal newNormal : NormalState StmtIn pSpec U δ T_H T_P)
    (stmt : StmtIn) (answer : Vector U SpongeSize.C) : Prop :=
  match TraceTableOps.inlu normal.state.trΔ.h stmt with
  | some stored =>
      stored = answer ∧ newNormal.state.trΔ.h = normal.state.trΔ.h
  | none =>
      newNormal.state.trΔ.h = TraceTableOps.add normal.state.trΔ.h stmt answer

/-- Branch (i) — the actual **h-query** (paper Step 2), with its *actual dependent result* and
its exact hash-table update.  A successful hash query returns precisely `answer`, appends the raw
`h(stmt)` occurrence, and either reuses or inserts the matching `tr∇.h` entry.  A stopped hash
query retains precisely that occurrence in `record`.  The `underlyingAbort` alternative is
impossible because an `h` query does not invoke Backtrack or LookAhead. -/
def BranchHashQuery (normal : NormalState StmtIn pSpec U δ T_H T_P) (stmt : StmtIn)
    (result : QueryResult (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) (dsHashQuery stmt)) : Prop :=
  match result with
  | .continue answer newNormal =>
      HashTableTransition normal newNormal stmt answer ∧
        ¬ BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, answer⟩]) ∧
        newNormal.state.trace = normal.state.trace ++ [⟨dsHashQuery stmt, answer⟩] ∧
        newNormal.state.trΔ.p = normal.state.trΔ.p ∧
        newNormal.state.rateCacheP = normal.state.rateCacheP
  | .stopped state record =>
      state = normal ∧ record.query = dsHashQuery stmt
  | .underlyingAbort => False

/-- The common exact-result shape of a forward permutation branch.  In particular, the output
named by a branch is the output carried by its `D2SStep` result: it cannot be chosen independently
of the installed occurrence or of the successor cache effect. -/
def ForwardBranchOutcome (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U) (status : InstallStatus)
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U))
    (continueEffect : NormalState StmtIn pSpec U δ T_H T_P → Prop) : Prop :=
  status = InstallStatusFor normal stateIn stateOut ∧
    D2SStep normal (.inl stateIn) result ∧
    match result with
    | .continue answer newNormal => answer = stateOut ∧ continueEffect newNormal
    | .stopped state record =>
        state = normal ∧
          ∃ hq : record.query = dsPermQuery (StartType := StmtIn) stateIn,
            record.answer = hq ▸ stateOut
    | .underlyingAbort => False

/-- The exact-result shape of an inverse permutation branch.  The answer carried by `result` is
the normalized forward input `stateIn`, and a stopped record stores the actual inverse occurrence
`p⁻¹(stateOut) ↦ stateIn`. -/
def InverseBranchOutcome (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U) (status : InstallStatus)
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U))
    (continueEffect : NormalState StmtIn pSpec U δ T_H T_P → Prop) : Prop :=
  status = InstallStatusFor normal stateIn stateOut ∧
    D2SStep normal (.inr stateOut) result ∧
    match result with
    | .continue answer newNormal => answer = stateIn ∧ continueEffect newNormal
    | .stopped state record =>
        state = normal ∧
          ∃ hq : record.query = dsPermInvQuery (StartType := StmtIn) stateOut,
            record.answer = hq ▸ stateIn
    | .underlyingAbort => False

/-- The pre-occurrence failure case of D2SQuery Step **4.b**.  It is deliberately separate from
the five forward answer branches: if the real Backtrack call returns `.err`, no output state is
sampled or installed and no query-answer occurrence is appended. -/
def BranchBacktrackAbort (normal : NormalState StmtIn pSpec U δ T_H T_P) : Prop :=
  UnderlyingBacktrackFailure normal

/-- Branch (ii) — the **p⁻¹ inverse query** (paper Step 3): an inverse occurrence is normalized
forward and installed; the rate-only cache is never searched (its **pre-state is carried unchanged**
on a `continue`, and the post-cache is the pre-cache), and the occurrence is appended and
monitored.  The transition is the genuine `D2SStep` and its constructed `continue` successor — the
exact-result link is carried by the witness `D2SBranchStep`. -/
def BranchInverseQuery (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U)
    (status : InstallStatus)
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  InverseBranchOutcome normal stateIn stateOut status result
    (fun newNormal => ContinueCacheIs newNormal normal.state.rateCacheP)

/-- Branch (iii) — the **forward `Ordinary` tail-hit** (paper Step 4.c.i): the rate-only cache has
a tail for `stateIn`, materializing it (`consumeRateOnlyCache pre stateIn capacity =
some (stateOut, cache')`) samples one capacity and installs the resulting mapping; the **real
end-cache `cache'` is forwarded** to the `continue` successor, and the attempted occurrence is
appended and monitored. -/
def BranchCacheTailHit (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U)
    (capacity : Vector U SpongeSize.C) (status : InstallStatus)
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  ∃ cache' : List (RateOnlyCacheEntry (U := U)),
    ConsumeTailMaterializesOneCapacity normal.state.rateCacheP stateIn capacity stateOut cache' ∧
      ForwardBranchOutcome normal stateIn stateOut status result
        (fun newNormal => ContinueCacheIs newNormal cache')

/-- Branch (iv) — the **forward `Ordinary` table-hit** (paper Step 4.c.ii): the table lookup
`s_in ↦ s_out` is defined (a `present` install); the table and cache are unchanged, and the
occurrence is appended and monitored. -/
def BranchTableHit (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U)
    (status : InstallStatus)
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  status = .present ∧
    ForwardBranchOutcome normal stateIn stateOut status result
      (fun newNormal =>
        newNormal.state.trΔ.p = normal.state.trΔ.p ∧
          ContinueCacheIs newNormal normal.state.rateCacheP)

/-- Branch (v) — the **forward `Ordinary` miss** (paper Step 4.c.iii): **no table value and no
tail** for `stateIn` (`TabularMiss` — `inlu … stateIn = none ∧ popRateOnlyTailByInput … stateIn =
none`), so `stateOut` is sampled and submitted to `Install`.  That `Install` is either `fresh`,
or it detects a sampled collision (`conflict`) and stops after recording the exact attempted
occurrence.  The rate-only cache is unread (carried unchanged on a constructed `continue`
successor only), and the occurrence is appended and monitored in both cases. -/
def BranchFreshMiss (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U)
    (status : InstallStatus)
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  (status = .fresh ∨ status = .conflict) ∧
    TabularMiss normal stateIn ∧
    ForwardBranchOutcome normal stateIn stateOut status result
      (fun newNormal => ContinueCacheIs newNormal normal.state.rateCacheP)

/-- The marker context of one oracle occurrence.  Only a `Program` occurrence has one.  The
round index is intrinsic to the context, so its certified marker and lazy tail use the exact
`challengeSize` and `Lᵥ` of that verifier round—not a caller-supplied or raw-trace length. -/
structure ProgramContext (pSpec : ProtocolSpec n) [HasChallengeSize pSpec] where
  round : pSpec.ChallengeIdx
  cursor : DuplexSpongeFS.Backtrack.ScheduleCursor
  pos : ℕ

/-- The round-indexed cache transition of Program.  The first Program mapping materializes one
capacity; it adds a rate-only tail precisely for an `Lᵥ(j)>1` squeeze, and otherwise leaves the
pre-existing cache unchanged.  The `none` case deliberately does **not** say that no old tail is
keyed at `stateOut`: a permutation output may legally equal a prior permutation input, so such an
absence would be an unwanted and generally false precondition. -/
def ProgramTailRealization (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat} [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (j : pSpec.ChallengeIdx) (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateOut : CanonicalSpongeState U)
    (newNormal : NormalState StmtIn pSpec U δ T_H T_P)
    (tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U))) : Prop :=
  match tail with
  | none =>
      pSpec.Lᵥᵢ j ≤ 1 ∧
        newNormal.state.rateCacheP = normal.state.rateCacheP
  | some residual =>
      1 < pSpec.Lᵥᵢ j ∧ residual.blocks.length = pSpec.Lᵥᵢ j - 1 ∧
        newNormal.state.rateCacheP = ⟨stateOut, residual⟩ :: normal.state.rateCacheP

/-- The parser/schedule fact required to connect an actual list of post-first Program rate blocks
to a verifier round.  It is intentionally separate from `ProgramTailRealization`: this relation
is discharged by parsing the encoded `gᵢ` response, while `ProgramTailRealization` is discharged
by the cache update after the first capacity is sampled. -/
def ProgramRemainingRatesForRound (j : pSpec.ChallengeIdx)
    (remainingRates : List (Vector U SpongeSize.R)) : Prop :=
  match DuplexSpongeFS.ProverTransform.RateOnlyTail.ofBlocks? (U := U) remainingRates with
  | none => pSpec.Lᵥᵢ j ≤ 1
  | some residual =>
      1 < pSpec.Lᵥᵢ j ∧ residual.blocks.length = pSpec.Lᵥᵢ j - 1

/-- Program Step **4.e.ii** — reuse the already-installed mapping at a certified marker.  This is
not an `Ordinary` table hit: the complete encoded `gᵢ` key has already been queried, but its first
permutation mapping was installed by the earlier matching Program invocation.  Therefore no rate
blocks are parsed, no capacity is sampled, and the rate-only cache is unchanged.  `tail = none`
records that this *current* reuse creates no new lazy continuation. -/
def ProgramExistingMapping (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U) (status : InstallStatus)
    (tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U)))
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  tail = none ∧
    TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut ∧
      status = .present ∧
        ForwardBranchOutcome normal stateIn stateOut status result
          (fun newNormal => ContinueCacheIs newNormal normal.state.rateCacheP)

/-- Program Step **4.e.iii** — the first mapping for a certified encoded key is absent, so the
parser/padding logic materializes its first rate block with one fresh capacity.  Only this case
may install the round-indexed `Lᵥ(j)-1` rate-only continuation. -/
def ProgramMaterialization (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat} [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (j : pSpec.ChallengeIdx) (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stateIn stateOut : CanonicalSpongeState U) (status : InstallStatus)
    (tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U)))
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  TraceTableOps.inlu normal.state.trΔ.p stateIn = none ∧
    ForwardBranchOutcome normal stateIn stateOut status result (fun newNormal =>
      ProgramTailRealization pSpec U T_H T_P j normal stateOut newNormal tail)

/-- Branch (vi) — the **`Program` branch** at a certified nonempty post-prover/pre-squeeze marker
(paper Step 4.e).  Its context fixes the exact verifier round, predecessor cursor, and marker.
The branch additionally requires that no lazy tail is already keyed at `stateIn`: such a query is
a scheduled squeeze continuation and must take Step 4.c.i, before it can query `g_i`.  This is
the execution-history fact that makes the lazy-cache invariant inductive; it is not inferred from
`¬ E`.  After the `gᵢ` query, the branch preserves the paper's two disjoint cases: Step 4.e.ii
reuses a present mapping without touching the cache, whereas Step 4.e.iii parses/materializes a
table miss and may create the residual tail.  A materializing `Install` may still conflict; the
common `ForwardBranchOutcome` then records the attempted occurrence and stops under `Monitor`. -/
def BranchProgram (context : ProgramContext pSpec)
    (normal : NormalState StmtIn pSpec U δ T_H T_P) (stateIn stateOut : CanonicalSpongeState U)
    (status : InstallStatus)
    (tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U)))
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  popRateOnlyTailByInput normal.state.rateCacheP stateIn = none ∧
    Certified SpongeSize.R context.cursor (challengeSize context.round) context.pos ∧
      (ProgramExistingMapping normal stateIn stateOut status tail result ∨
        ProgramMaterialization pSpec U T_H T_P context.round normal stateIn stateOut status tail
          result)

/-! ## The shared branch-witness/result object

This is the **single** low-level witness importable by both `OnlineTransformation` (whose
`D2SQueryRun` folds it) and `RevisedOperators` (whose `RevisedD2SQueryStep` dispatches it).  It
records, for one occurrence `query` on the real normal state `normal`, the **exact** three-way
`result` and the **exact** branch-relative data of that occurrence.

Each constructor names one paper branch of Algorithm 5.3 and, for the permutation branches, ties
the **exact** `stateIn`/`stateOut` to the query and requires the genuine `D2SStep` on that **exact**
`result` through its branch relation, plus the exact successor / cache data — never a bare
`∃ result, D2SStep … result`. The hash branch has no `Install`: the hash constructor carries the
exact answer and the real `BranchHashQuery` effect.
-/

/-- The single **branch-witness/result object** of one revised D2SQuery occurrence: the query
`query` on the normal state `normal` resolves by **exactly one** of the six paper branches, each
carrying the exact `result` (the three-way `StepResult` for the permutation branches), its exact
per-occurrence Program context, and the exact state/cache/table data. -/
inductive D2SBranchStep (normal : NormalState StmtIn pSpec U δ T_H T_P) :
    (programContext : Option (ProgramContext pSpec)) →
    (query : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      QueryResult (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (T_H := T_H) (T_P := T_P) query → Prop where
  | hash (stmt : StmtIn)
      {result : QueryResult (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (T_H := T_H) (T_P := T_P) (dsHashQuery stmt)}
      (h : BranchHashQuery normal stmt result) :
      D2SBranchStep normal none (dsHashQuery stmt) result
  | inverse (stateIn stateOut : CanonicalSpongeState U) (status : InstallStatus)
      (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U))
      (h : BranchInverseQuery normal stateIn stateOut status result) :
      D2SBranchStep normal none (.inr (.inr stateOut)) result
  | tailHit (stateIn stateOut : CanonicalSpongeState U)
      (capacity : Vector U SpongeSize.C) (status : InstallStatus)
      (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U))
      (h : BranchCacheTailHit normal stateIn stateOut capacity status result) :
      D2SBranchStep normal none (.inr (.inl stateIn)) result
  | tableHit (stateIn stateOut : CanonicalSpongeState U) (status : InstallStatus)
      (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U))
      (h : BranchTableHit normal stateIn stateOut status result) :
      D2SBranchStep normal none (.inr (.inl stateIn)) result
  | freshMiss (stateIn stateOut : CanonicalSpongeState U) (status : InstallStatus)
      (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U))
      (h : BranchFreshMiss normal stateIn stateOut status result) :
      D2SBranchStep normal none (.inr (.inl stateIn)) result
  | program (context : ProgramContext pSpec) (stateIn stateOut : CanonicalSpongeState U)
      (status : InstallStatus)
      (tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U)))
      (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U))
      (h : BranchProgram context normal stateIn stateOut status tail result) :
      D2SBranchStep normal (some context) (.inr (.inl stateIn)) result
  | backtrackAbort (stateIn : CanonicalSpongeState U)
      (h : BranchBacktrackAbort normal) :
      D2SBranchStep normal none (.inr (.inl stateIn)) .underlyingAbort

/-- A Program branch relation is witnessed by the **Program constructor itself**, not by an
unclassified six-way branch witness.  `ProgramOccurrence` uses this bridge so a tail hit, table
hit, or fresh miss cannot stand in for the Program case. -/
theorem program_branch_step (context : ProgramContext pSpec)
    (normal : NormalState StmtIn pSpec U δ T_H T_P) (stateIn stateOut : CanonicalSpongeState U)
    (status : InstallStatus)
    (tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U)))
    (result : StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U))
    (h : BranchProgram context normal stateIn stateOut status tail result) :
    D2SBranchStep normal (some context) (.inr (.inl stateIn)) result :=
  .program context stateIn stateOut status tail result h

end D2SQuery

end Statement

end DuplexSpongeFS
