/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.Bounds
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.ReplaySemantics
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.OnlineTransformation
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.OfflineTransformation
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.StatefulReplay
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.RevisedOperators
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# Statement layer — module 5: events & analysis (Lemma 5.8 / 5.1, hybrids, no-abort)

This module is the dependency-acyclic home of the final *analysis-level* statement surface:

- the **hybrids** Hyb₀–Hyb₄ and their pairwise-distance bound shapes;
- the **section-wide** bridge facts: `nV_eq_query_count` and the base-trace-length consequence
  `baseTraceLength ≤ T + 1 + N_𝒱`;
- the **total Lemma 5.8** bound shape (`perr ≤ ηStar …`, eq. 5), assembled from the module-1
  cores `Lemma58Core` / `Lemma58StoppedCore`;
- the **no-abort** shapes (re-exported from module 2, tied to `¬ E`);
- Claims 5.21 / 5.24 core shapes (from module 1);
- **Lemma 5.1**'s exact statement shape (the Key-Lemma analysis-level bound).

As everywhere in this statement layer, these are named `Prop` specifications — nothing is
claimed here; the concrete `E`, distributions, and probabilities come from the executable
executor and hybrid wiring.
-/

namespace DuplexSpongeFS

namespace Statement

open OracleComp OracleSpec ProtocolSpec DSTraceStorage

/-! ## Definitions 5.9/5.11/5.13/5.15 and Lemmas 5.10/5.12/5.14/5.16

The four topology events are not reimplemented in this statement layer.  Their single concrete
source is `BadEventDS`, whose predicates are already formulated over the symmetric normalized
forward/inverse base trace.  The aliases below place the exact updated paper names beside the
stateful-replay and hybrid statements, so every Section 5 declaration has one discoverable
statement-layer entry point.
-/

/-- Definition 5.9: permutation partial-bijection failure in the concrete symmetric base trace. -/
abbrev BadEventPrp {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) : Prop :=
  BadEventDS.E_prp trace

/-- Definition 5.11: a Backtrack family contains an inverse-represented predecessor. -/
abbrev BadEventInv {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) (state : CanonicalSpongeState U)
    (family : DuplexSpongeFS.Backtrack.S_BT trace state) : Prop :=
  BadEventDS.E_inv trace state family

/-- Definition 5.13: the concrete Backtrack family forks. -/
abbrev BadEventFork {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) (state : CanonicalSpongeState U)
    (family : DuplexSpongeFS.Backtrack.S_BT trace state) : Prop :=
  BadEventDS.E_fork trace state family

/-- Definition 5.15: a Backtrack index family violates temporal order. -/
abbrev BadEventTime {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) (state : CanonicalSpongeState U)
    (family : DuplexSpongeFS.Backtrack.S_BT trace state) : Prop :=
  BadEventDS.E_time trace state family

/-- Lemma 5.10: outside the combined bad event, the normalized permutation relation is a partial
bijection. -/
def Lemma510 {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) : Prop :=
  ¬ BadEvent trace → ¬ BadEventPrp trace

/-- Lemma 5.12: outside the combined bad event, no Backtrack representative is inverse. -/
def Lemma512 {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) (state : CanonicalSpongeState U)
    (family : DuplexSpongeFS.Backtrack.S_BT trace state) : Prop :=
  ¬ BadEvent trace → ¬ BadEventInv trace state family

/-- Lemma 5.14: outside the combined bad event, the Backtrack family has at most one maximal
candidate. -/
def Lemma514 {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) (state : CanonicalSpongeState U)
    (family : DuplexSpongeFS.Backtrack.S_BT trace state) : Prop :=
  ¬ BadEvent trace → ¬ BadEventFork trace state family

/-- Lemma 5.16: outside the combined bad event, every Backtrack index sequence is temporally
ordered. -/
def Lemma516 {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) (state : CanonicalSpongeState U)
    (family : DuplexSpongeFS.Backtrack.S_BT trace state) : Prop :=
  ¬ BadEvent trace → ¬ BadEventTime trace state family

/-! ## Hybrids (paper §5.5, Hyb₀–Hyb₄) -/

/-- The hybrid index type: `Fin 5` selecting one of Hyb₀, Hyb₁, Hyb₂, Hyb₃, Hyb₄.  Their
concrete distributions are supplied by the hybrid layer (plan M4 / M6); the index type is the
statement-level home of the hybrid family. -/
abbrev HybridIndex := Fin 5

/-- The **real hybrid result type**: the concrete transcript `Trace StmtIn U`
(= `(duplexSpongeChallengeOracle StmtIn U).QueryLog`) sampled by each Hybᵢ.  Hybrids live over
this concrete transcript, never over a bare real. -/
abbrev HybTranscript {StmtIn U : Type} [SpongeUnit U] [SpongeSize] : Type := Trace StmtIn U

/-- A pairwise hybrid bound: the **real** statistical distance `HybridTVDist expᵢ expⱼ` (the
VCVio `tvDist`) between the two concrete experiments `expᵢ`, `expⱼ` is at most `bound`.  There is
no free `ℝ` standing in for a distribution — the distance is the concrete `tvDist` of two real
`ProbComp` experiments. -/
noncomputable def HybridDistanceBound {α : Type} (expᵢ expⱼ : ProbComp α) (bound : ℝ) : Prop :=
  HybridTVDist expᵢ expⱼ ≤ bound

/-! ## Section-wide bridges (BF-1) -/

/-- `nV_eq_query_count`: a runtime verifier permutation-call count `nV` (supplied by M1 wiring)
equals the paper's exact `N_𝒱`, i.e. the **canonical schedule-layer count**
`DuplexSpongeFS.verifierPermCallCount pSpec δ`.  This is the single canonical `N_𝒱` — no mirrored
schedule count is introduced here (see `BacktrackSchedule.lean`). -/
noncomputable def NVEqQueryCount {n : Nat} [SpongeSize]
    (pSpec : ProtocolSpec n) [ProtocolSpec.HasMessageSize pSpec]
    [ProtocolSpec.HasChallengeSize pSpec] (nV δ : ℕ) : Prop :=
  nV = DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)

/-- The base-trace-length consequence (paper eq. 44b, `N := T + 1 + N_𝒱`): a real execution
whose base trace has at most `records` entries, with the verifier making `nV` (`N_𝒱`) forward calls
over at most `T` good-prefix entries, satisfies `records ≤ T + 1 + nV` (the `-1` accounted for by
the `Start`/hash query).  A pure count inequality over the real quantities — not a stand-in for a
distribution. -/
def BaseTraceLengthLe (records T nV : ℕ) : Prop := records ≤ T + 1 + nV

/-! ## Lemma 5.8: stateful extension, core, stopped core, total -/

/-- One **completed stateful verifier extension** for Lemma 5.8.  This packages the hypotheses
that the paper uses in its first-bad-event calculation instead of leaving them in prose around a
generic transcript distribution:

- `history` is the actual salt-plus-`Act_𝒱` replay, with partial-block cursors, raw trace prefixes,
  and the separate absorb/squeeze frame laws;
- every `ReplayHistory` derives its own ordered forward-call realization at every prefix and at
  the end (`ReplayHistory.scheduleRealizesTrace`);
- `priorTrace` is the arbitrary preceding oracle trace, with at most `T` base entries and no bad
  event; and
- `canonical_count` identifies the history's actual final forward-call count with the canonical
  `verifierPermCallCount pSpec δ = N_𝒱`.

Thus a value of this type is a completed execution witness, not a caller-supplied count or an
unrelated list of phases.  Proving that the live verifier produces this witness is the subsequent
stateful-replay refinement theorem. -/
structure CompletedVerifierExtension (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n)
    (U : Type) [SpongeUnit U] [SpongeSize] [ProtocolSpec.HasMessageSize pSpec]
    [ProtocolSpec.HasChallengeSize pSpec] (δ T : ℕ) where
  history : ReplayHistory StmtIn U SpongeSize.R δ
    (DuplexSpongeFS.protocolPhases (pSpec := pSpec))
  priorTrace : Trace StmtIn U
  priorTrace_is_prefix : List.IsPrefix priorTrace history.trace
  priorTrace_good : ¬ BadEvent priorTrace
  priorTrace_base_bound : (getBaseTrace priorTrace).length ≤ T
  canonical_count : (history.cursors
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)).length).queryIndex =
    DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)

/-- The output type of a stopped or unstopped Lemma-5.8 experiment.  Every sampled value carries
its own completed stateful extension witness, so an event probability over this type cannot silently
range over traces that did not execute the salt and complete verifier action list. -/
abbrev CompletedVerifierTrace (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n)
    (U : Type) [SpongeUnit U] [SpongeSize] [ProtocolSpec.HasMessageSize pSpec]
    [ProtocolSpec.HasChallengeSize pSpec] (δ T : ℕ) : Type :=
  CompletedVerifierExtension StmtIn pSpec U δ T

/-- The actual `E`-probability of a completed verifier-extension experiment. -/
noncomputable def CompletedExtensionEventProbability
    {StmtIn U : Type} {n : Nat} {pSpec : ProtocolSpec n} [SpongeUnit U] [SpongeSize]
    [ProtocolSpec.HasMessageSize pSpec] [ProtocolSpec.HasChallengeSize pSpec] {δ T : ℕ}
    (exp : ProbComp (CompletedVerifierTrace StmtIn pSpec U δ T)) : ℝ :=
  (Pr[ fun outcome => BadEvent outcome.history.trace | exp ]).toReal

/-- The **total Lemma 5.8** bound shape (paper eq. 5): over base entries `T = tₕ+tₚ+tₚᵢ` and
the exact verifier count `nV`, the **real** bad-event measure `EventProbability exp` of the
concrete transcript experiment `exp` is at most `ηStar U tₕ tₚ tₚᵢ nV codec` — the algebraic
first term plus the codec term.  The LHS is the real `Pr[BadEvent | exp]`, not a free `perr`. -/
noncomputable def Lemma58Total {StmtIn U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    (exp : ProbComp (Trace StmtIn U)) (tₕ tₚ tₚᵢ nV : ℕ) (codec : ℝ) : Prop :=
  EventProbability exp ≤ etaStar U tₕ tₚ tₚᵢ nV codec

/-- The Lemma 5.8 first-event (`E`-good prefix) shape — the concrete module-1 core (BF-2). -/
noncomputable def Lemma58Stopped {StmtIn U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    {n : Nat} {pSpec : ProtocolSpec n} [ProtocolSpec.HasMessageSize pSpec]
    [ProtocolSpec.HasChallengeSize pSpec] {δ T : ℕ}
    (exp : ProbComp (CompletedVerifierTrace StmtIn pSpec U δ T)) : Prop :=
  (ExceptionalEmpty T (DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)) →
    CompletedExtensionEventProbability exp = 0) ∧
  (¬ ExceptionalEmpty T (DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)) →
    CompletedExtensionEventProbability exp ≤ Dcap U T
      (DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)))

/-- The public stateful Lemma 5.8 interface.  Unlike `Lemma58Core`, this requires each sampled
output to carry the completed-extension witness above; its count is therefore definitionally the
canonical exact `N_𝒱`, never the former rounded scalar `L`.  `Lemma58Core` remains the useful
arithmetic/probability subgoal after the executor-refinement theorem has unpacked that witness. -/
noncomputable def Lemma58 {StmtIn U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    {n : Nat} {pSpec : ProtocolSpec n} [ProtocolSpec.HasMessageSize pSpec]
    [ProtocolSpec.HasChallengeSize pSpec] {δ T : ℕ}
    (exp : ProbComp (CompletedVerifierTrace StmtIn pSpec U δ T)) : Prop :=
  CompletedExtensionEventProbability exp ≤ badEventBound U
    (T + 1 + DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ))

/-! ## Claims 5.19 / 5.20, Corollary 5.20a, Lemmas 5.17 / 5.18 (no-abort), concrete

The corrected no-abort statements of §5.7, named over the **real** operators and their **real
`.err` outcomes** (module 2).  Nothing here is a vacuous `Nonempty`; each names the trace, the bad
event, the certification, and the concrete operator/result the paper guards.  `BacktrackNoAbort` /
`LookAheadNoAbort` are the real module-2 facts (cited, not redefined); the claims, corollary, and
lemmas pack them with the paper's `E`/certification guards.
-/

/-- The real revised-D2S no-abort core used by Claims 5.19/5.20 → Lemmas 5.17/5.18: absent the bad
event, the stateful `BackTrack` is not `.err` at every addressable state **and** the real
`LookAhead` is not `.err` at every certified nonempty marker of `tr∇.p` (the `pos ↝ i` marker
reconciliation and
the executable full-table `Monitor` pass are M1/S3a refinements).  Names the real trace, the bad
event, one round-local `ProgramContext`, and the real `.err` outcomes. -/
def RevisedD2SNoAbort {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq StmtIn]
    [DecidableEq U] {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec] [HasChallengeSize pSpec]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trace : Trace StmtIn U) (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (context : D2SQuery.ProgramContext pSpec) : Prop :=
  ¬ BadEvent trace →
    (∀ state : CanonicalSpongeState U,
      DuplexSpongeFS.Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
        trace trΔ h_trΔ state ≠ ExperimentOutput.err) ∧
    (∀ state : CanonicalSpongeState U,
      Certified SpongeSize.R context.cursor (challengeSize context.round) context.pos →
        DuplexSpongeFS.Lookahead.lookAhead (pSpec := pSpec) trΔ.p state context.round ≠
          (pure ExperimentOutput.err : OracleComp (Unit →ₒ U)
            (ExperimentOutput (Vector U (challengeSize context.round)))))

/-! ## Lemma 5.25 (stateful replay) and Claims 5.22 / 5.23 -/

/-- The **round-indexed marker**: `pos` is the certified marker of round `j` — the real
`firstSqueezeQuery?` position at the **predecessor cursor** of round-`j`'s squeeze phase
(`phaseCursors[ j.1 ]`).  Only a verifier-challenge round can be marked, and the marker is the
first query of that round's nonempty squeeze at a rate boundary — an absorb, an empty squeeze, and
all later calls are excluded by construction. -/
noncomputable def RoundMarker {n : ℕ} (pSpec : ProtocolSpec n) [HasChallengeSize pSpec]
    (R δ : ℕ) (phases : List ReplayPhase) (j : pSpec.ChallengeIdx) (pos : ℕ) : Prop :=
  ∃ hj : j.1.1 < phases.length,
    DuplexSpongeFS.Backtrack.ScheduleCursor.firstSqueezeQuery? R
      (List.get (DuplexSpongeFS.Statement.phaseCursors R δ phases) ⟨j.1.1,
        by simpa [DuplexSpongeFS.Statement.phaseCursors, List.length_scanl] using hj⟩)
      (challengeSize j) = some pos

/-- **Lemma 5.25 core** — the part of Lemma 5.25 (items 4 and the marker/no-abort projection of
items 5–7) expressible as a standalone interface over the real operators: absent `E` on the raw
trace, the real stateful `BackTrack` is not `.err` at every state (item 4) and the real `LookAhead`
is not `.err` at every certified marker (item 5/7 projection); the real `D2SAlgo` LookAhead memo
agrees with the insertion order of the real encoded-`gᵢ` trace (items 5–7, via
`MemoizesEncodedPreimage` and `EncodedTraceRealizesInvocations`).  This is the **core**;
the complete 7-item interface is `Lemma525` below. -/
structure Lemma525Core {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat} [DecidableEq StmtIn]
    [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (trace : Trace StmtIn U) (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (encodedTrace : D2SAlgo.EncodedTrace StmtIn pSpec U δ)
    (memo : (i : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i)) : Prop where
  good : ¬ BadEventDS.E trace
  backtrack_no_abort : ∀ state : CanonicalSpongeState U,
    @BacktrackNoAbort StmtIn U _ _ _ _ T_H T_P _ n pSpec δ _ _ trace trΔ h_trΔ state
  /-- Every LookAhead invocation is tied to its own round's predecessor marker, rather than to
  one unrelated global cursor (in particular, never to the terminal replay cursor). -/
  lookahead_no_abort : ∀ (pos : ℕ) (i : pSpec.ChallengeIdx) (state : CanonicalSpongeState U),
    RoundMarker pSpec SpongeSize.R δ (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) i pos →
      @LookAheadNoAbort U _ _ _ n pSpec _ T_P _ trΔ.p state i
  memoizes : D2SAlgo.MemoizesEncodedPreimage memo encodedTrace


/-! ## Faithful Lemma 5.25 items: Program, uniqueness, key reconciliation -/

/-- The encoded-answer part of the **Program-branch realization** (`ProgramSucceeds`): a
`challengeSize j`-unit challenge is split into its first encoded symbol `first` and exactly
`challengeSize j - 1` remaining encoded symbols `lazySucc`.  This is independent of the first
*capacity* and rate-only tail recorded separately by `ProgramOccurrence`; the `+1` is only the
structural vector split of the memoized answer. -/
def ProgramSucceeds {n : ℕ} {pSpec : ProtocolSpec n} [HasChallengeSize pSpec] {U : Type}
    (j : pSpec.ChallengeIdx) (answer : Vector U (challengeSize j))
    (first : U) (lazySucc : Vector U (challengeSize j - 1)) : Prop :=
  Vector.toList answer = first :: Vector.toList lazySucc

/-- Functionality of the actual `h` occurrences in one raw duplex trace.  This is the explicit
additional premise used only by Lemma 5.25 item 7: two hash anchors for the same statement have
the same capacity answer.  The hybrid executions satisfy this because their hash oracle is
memoized; it is not smuggled in as an unconditional global hypothesis of the lemma. -/
def HashFunctionalOnTrace {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) : Prop :=
  ∀ (stmt : StmtIn) (cap₁ cap₂ : Vector U SpongeSize.C),
    (⟨dsHashQuery stmt, cap₁⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace →
      (⟨dsHashQuery stmt, cap₂⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace →
        cap₁ = cap₂

/-- The **F2 Program-branch witness** packaged for an execution-derived `ProgramOccurrence`: at the
scheduling `cursor` and certified marker `pos`, the actual `program` branch constructs a forward
mapping `(stateIn,stateOut)` and its exact reusable successor `newNormal`.  The fields expose the
installed output and successor so the round-indexed tail/capacity realization below can refer to
the same occurrence, rather than to an unrelated existential. -/
structure ProgramBranchWitness {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (cursor : DuplexSpongeFS.Backtrack.ScheduleCursor) (pos : ℕ)
    (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P) where
  /-- The concrete verifier round recovered by Backtrack for this Program occurrence. -/
  round : pSpec.ChallengeIdx
  stateIn : CanonicalSpongeState U
  stateOut : CanonicalSpongeState U
  newNormal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P
  status : D2SQuery.InstallStatus
  /-- The exact tail installed (or absent) by this occurrence. -/
  tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U))
  branch : D2SQuery.BranchProgram ⟨round, cursor, pos⟩ normal stateIn stateOut status tail
    (.continue stateOut newNormal)

/-- The Program witness gives the *actual Program constructor* of the shared dispatcher.  This
bridge is definitionally built with `D2SBranchStep.program`; it prevents a tail-hit, table-hit, or
fresh-miss witness from being used as a Program occurrence. -/
def ProgramBranchWitness.toBranchStep {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    {cursor : DuplexSpongeFS.Backtrack.ScheduleCursor} {pos : ℕ}
    {normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P}
    (w : ProgramBranchWitness pSpec U δ T_H T_P cursor pos normal) :
    D2SQuery.D2SBranchStep normal
      (some ⟨w.round, cursor, pos⟩) (.inr (.inl w.stateIn))
      (.continue w.stateOut w.newNormal) :=
  D2SQuery.program_branch_step ⟨w.round, cursor, pos⟩ normal w.stateIn w.stateOut
    w.status w.tail (.continue w.stateOut w.newNormal) w.branch

/-- The current Program occurrence is the Step **4.e.ii** reuse case.  Its `tail = none`, table
hit, present Install, and unchanged-cache continuation are all part of the branch relation. -/
def ProgramBranchWitness.Reuses {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    {cursor : DuplexSpongeFS.Backtrack.ScheduleCursor} {pos : ℕ}
    {normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P}
    (w : ProgramBranchWitness pSpec U δ T_H T_P cursor pos normal) : Prop :=
  D2SQuery.ProgramExistingMapping normal w.stateIn w.stateOut w.status w.tail
    (.continue w.stateOut w.newNormal)

/-- The current Program occurrence is the Step **4.e.iii** materialization case.  Its table miss,
first-capacity transition, and exact round-indexed residual-tail policy are all part of the branch
relation. -/
def ProgramBranchWitness.Materializes {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n)
    (U : Type) [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
    [DecidableEq StmtIn] [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    {cursor : DuplexSpongeFS.Backtrack.ScheduleCursor} {pos : ℕ}
    {normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P}
    (w : ProgramBranchWitness pSpec U δ T_H T_P cursor pos normal) : Prop :=
  D2SQuery.ProgramMaterialization pSpec U T_H T_P w.round normal w.stateIn w.stateOut w.status
    w.tail (.continue w.stateOut w.newNormal)

/-- A per-occurrence Program context is anchored at a particular challenge round of one coherent
stateful replay: its cursor is that round's predecessor boundary, its length is exactly the
round's verifier-challenge length, and its position is the certified first-squeeze marker. -/
def ProgramContextAtRound {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    {n : Nat} (pSpec : ProtocolSpec n) [codec : CodecCore pSpec U] (R δ : ℕ)
    (phases : List ReplayPhase)
    (history : ReplayHistory StmtIn U R δ phases) (j : pSpec.ChallengeIdx)
    (context : D2SQuery.ProgramContext pSpec) : Prop :=
  context.round = j ∧
    context.cursor = history.cursors j.1.1 ∧
    RoundMarker pSpec R δ phases j context.pos

/-- Every nonempty Program context in a query stream must be justified by a concrete verifier
round of the same replay history.  This closes the former global-marker loophole: a stream cannot
silently attach an arbitrary `(cursor, length, pos)` triple to a forward query. -/
def QueryStreamRespectsHistory {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    {n : Nat} (pSpec : ProtocolSpec n) [codec : CodecCore pSpec U] (δ : ℕ)
    (history : ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (stream : D2SQuery.QueryStream StmtIn pSpec U) : Prop :=
  ∀ occurrence ∈ stream, ∀ context : D2SQuery.ProgramContext pSpec,
    occurrence.programContext = some context →
      ∃ j : pSpec.ChallengeIdx,
        ProgramContextAtRound pSpec SpongeSize.R δ
          (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) history j context

/-- A Program context is compatible with the **current** D2S normal state when the state contains
the replayed prefix selected by its BackTrack candidate at the context's own round.  The selected
prefix is an order-preserving subtrace, not necessarily the entire normal trace: the ambient
oracle trace may contain earlier unrelated queries and a later repeated Program call may reuse an
already installed mapping.  This rules out attaching a marker from an unrelated replay while
preserving the paper's selected-chain semantics. -/
def ProgramContextMatchesNormal {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (history : ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (context : D2SQuery.ProgramContext pSpec) : Prop :=
  ∃ j : pSpec.ChallengeIdx,
    ProgramContextAtRound pSpec SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) history j context ∧
    (history.tracePrefix j.1.1).Sublist normal.state.trace

/-- The history-indexed whole D2SQuery runner.  It folds the genuine per-occurrence transitions;
each Program occurrence is checked against the **current** normal-state trace and its own replay
round. This is deliberately a recursive runner, rather than the old loose conjunction of a generic
run with a global context-membership property. -/
def D2SQueryRunOnHistory {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (history : ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (stream : D2SQuery.QueryStream StmtIn pSpec U)
    (terminal : D2SQuery.D2SRunTerminal StmtIn pSpec U δ T_H T_P) : Prop :=
  match stream with
  | [] =>
      match terminal with
      | .finished state => state = normal
      | _ => False
  | occurrence :: rest =>
      (match occurrence.programContext with
      | none => True
      | some context => ProgramContextMatchesNormal pSpec U δ T_H T_P history normal context) ∧
      ∃ result : D2SQuery.QueryResult (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          (T_H := T_H) (T_P := T_P) occurrence.query,
        D2SQuery.D2SBranchStep normal occurrence.programContext occurrence.query result ∧
          match result with
          | .continue _ newNormal =>
              D2SQueryRunOnHistory pSpec U δ T_H T_P history newNormal rest terminal
          | .stopped state record =>
              state = normal ∧ terminal = .stopped state record
          | .underlyingAbort =>
              terminal = .aborted normal

/-- The round-indexed lazy-tail part of Program.  Program materializes one initial output capacity
now.  It stores a rate-only continuation at that *same* output precisely when the verifier squeeze
needs more than one permutation block, and that continuation has exactly `Lᵥ(i)-1` pending blocks.
For `Lᵥ(i) ≤ 1`, it leaves the pre-existing cache unchanged; it does not forbid a pre-existing
tail whose key happens to equal the new permutation output. -/
abbrev ProgramTailRealization {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat} [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (j : pSpec.ChallengeIdx) (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (stateOut : CanonicalSpongeState U)
    (newNormal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (tail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U))) : Prop :=
  D2SQuery.ProgramTailRealization pSpec U T_H T_P j normal stateOut newNormal tail

/-- The complete encoded `gᵢ` key reconstructed from a real successful Backtrack output.  The
equality is dependent because the encoded-message prefix is indexed by the returned challenge
round.  This is the direct formal counterpart of Algorithm 5.3 Step **4.e.i--ii**:
`κ̂ = (i, x, τ, α̂₁, …, α̂ᵢ)`. -/
def BacktrackOutputMatchesKey {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [HasMessageSize pSpec] [HasChallengeSize pSpec] (δ : Nat)
    (j : pSpec.ChallengeIdx)
    (out : DuplexSpongeFS.Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U))
    (key : (gSpecInterface (U := U) StmtIn pSpec δ j).Query) : Prop :=
  ∃ h : out.roundIdx = j,
    h ▸ (out.stmt, out.salt, out.encodedMessages) = key

/-- One concrete **Program occurrence** (paper D2SAlgo Step 4.e), execution-derived and anchored
at a real certified round-`j` marker.  It records the complete encoded `gᵢ` key and answer at
that marker, together with the exact shared Program-branch witness.  The current occurrence is
explicitly classified as either Step **4.e.ii** reuse or Step **4.e.iii** materialization:

- reuse records the existing output capacity but samples no capacity and creates no new tail; or
- materialization samples the first capacity and records the exact `Lᵥ(j)-1` rate-only tail.

The replayed marker prefix is an order-preserving subtrace of the current normal trace, rather
than being falsely equated with the entire ambient trace.  Thus a later reuse can refer to the
earlier materializing occurrence which installed its mapping. -/
structure ProgramOccurrence {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (history : DuplexSpongeFS.Statement.ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (memo : (j : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ j).Query → Vector U (challengeSize j)) where
  j : pSpec.ChallengeIdx
  pos : ℕ
  key : (gSpecInterface (U := U) StmtIn pSpec δ j).Query
  /-- First encoded verifier-challenge symbol, not a capacity. -/
  first : U
  lazySucc : Vector U (challengeSize j - 1)
  nonempty : 0 < challengeSize j
  at_marker : DuplexSpongeFS.Statement.RoundMarker pSpec SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) j pos
  -- The scheduling cursor and the real normal state on which the Program branch runs.  The
  -- round-j replay prefix is selected from this ambient trace; it need not equal it.
  cursor : DuplexSpongeFS.Backtrack.ScheduleCursor
  normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P
  round_index : j.1.1 < (DuplexSpongeFS.protocolPhases (pSpec := pSpec)).length
  normal_contains_marker_replay :
    (history.tracePrefix j.1.1).Sublist normal.state.trace ∧ cursor = history.cursors j.1.1
  cursor_is_marker_predecessor :
    cursor = List.get (DuplexSpongeFS.Statement.phaseCursors SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec))) ⟨j.1.1,
        by simpa [DuplexSpongeFS.Statement.phaseCursors,
          List.length_scanl] using round_index⟩
  -- the corresponding F2 Program-branch witness (the exact occurrence on `normal` at cursor/pos)
  program_witness : ProgramBranchWitness (StmtIn := StmtIn) pSpec U δ T_H T_P cursor pos normal
  /-- The low-level Program branch is recovered for this exact verifier round. -/
  program_round : program_witness.round = j
  /-- The Program branch was selected by the real Backtrack invocation over the current normal
  trace.  Its selected replay prefix is recorded above, and its tuple reconstructs this key. -/
  backtrackOutput : DuplexSpongeFS.Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn)
    (pSpec := pSpec) (U := U)
  backtrack_recovers : statefulBackTrackAt (pSpec := pSpec) history j normal
    program_witness.stateIn backtrackOutput
  backtrack_key : BacktrackOutputMatchesKey pSpec U δ j backtrackOutput key
  /-- The capacity of this Program output state.  It is freshly sampled only in the materializing
  case; the reuse case simply reads the capacity already present in the existing mapping. -/
  initialCapacity : Vector U SpongeSize.C
  initial_capacity_matches_output :
    CanonicalSpongeState.capacitySegment program_witness.stateOut = initialCapacity
  /-- The current Program occurrence's residual tail.  It is `none` in the reuse case; in the
  materializing case it is exactly the round-indexed `Lᵥ(j)-1` continuation when nonempty. -/
  lazyTail : Option (DuplexSpongeFS.ProverTransform.RateOnlyTail (U := U))
  /-- The high-level lazy tail is exactly the tail supplied to the low-level Program transition. -/
  lazy_tail_is_branch_tail : lazyTail = program_witness.tail
  program_case :
    ProgramBranchWitness.Reuses pSpec U δ T_H T_P program_witness ∨
      ProgramBranchWitness.Materializes pSpec U δ T_H T_P program_witness
  -- the actual memo key/answer and the lazy-tail record realizing it
  realizes : ProgramSucceeds j (memo j key) first lazySucc

/-- The Step 4.e.ii face of a concrete Program occurrence. -/
def ProgramOccurrence.Reuses {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    {history : ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec))}
    {memo : (j : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ j).Query → Vector U (challengeSize j)}
    (occ : ProgramOccurrence pSpec U δ T_H T_P history memo) : Prop :=
  ProgramBranchWitness.Reuses pSpec U δ T_H T_P occ.program_witness

/-- The Step 4.e.iii face of a concrete Program occurrence. -/
def ProgramOccurrence.Materializes {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat) [DecidableEq StmtIn]
    [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    {history : ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec))}
    {memo : (j : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ j).Query → Vector U (challengeSize j)}
    (occ : ProgramOccurrence pSpec U δ T_H T_P history memo) : Prop :=
  ProgramBranchWitness.Materializes pSpec U δ T_H T_P occ.program_witness

/-- The Program branch's low-level occurrence context is exactly the replay-history context of its
recorded round.  This bridge is the point at which the generic D2SQuery stream is tied back to the
specific stateful replay that recovered the marker. -/
theorem ProgramOccurrence.context_at_round {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n)
    (U : Type) [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
    [DecidableEq StmtIn] [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    {history : ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec))}
    {memo : (j : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ j).Query → Vector U (challengeSize j)}
    (occ : ProgramOccurrence pSpec U δ T_H T_P history memo) :
    ProgramContextAtRound pSpec SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) history occ.j
      ⟨occ.program_witness.round, occ.cursor, occ.pos⟩ := by
  exact ⟨occ.program_round, occ.normal_contains_marker_replay.2, occ.at_marker⟩

/-- **Lemma 5.25 (stateful replay, complete, faithful)** — the seven items of the updated paper,
over a **concrete stateful replay witness** (a `ReplayExecution` built from the real
`protocolPhases` and run by the real `ScheduleCursor` transitions), the real whole operators
(`Backtrack.backTrack`, `Lookahead.lookAhead`), the real two-table split, and the real encoded
memo/trace.  Suppose `E(tr) = 0` (`good`).  Then:

1. **cursor is the concrete duplex cursor**: the replayed final cursor's `queryIndex` is exactly
   the canonical verifier count `N_𝒱 = verifierPermCallCount pSpec δ` (`item1_cursor`, tied to the
   folded `ReplayExecution.final`).
2. **separate frame checks over the genuine replay**: the absorb-side (11a) check uses the real
   salt/message write locations and all recorded forward inputs, so it also covers a partial salt
   or message which emits no call at its own boundary; every squeeze carries the separate (11b)
   `SqueezeFrame` at its successor-linked transition (`item2_replay_frames`, via
   `AbsorbFrameCheck` + `replaySqueezeFramesHeld`).
3. **exact marker**: `pos` is a certified marker exactly when it is the real `firstSqueezeQuery?`
   of a nonempty challenge round at a rate boundary — never an absorb, an empty squeeze, or a later
   call (`item3_marker`, via `ReplayHasMarker` ↔ `RoundMarker`).
4. **separate search tables and no-abort**: BackTrack is not `.err` on the current strict replay
   prefix, while LookAhead is not `.err` on a table mirroring the complete trace; the calls cannot
   be interchanged. The encoded memo agrees with the encoded-`gᵢ` trace insertion order
   (`item4_search_tables` and `core = Lemma525Core`).
5. **Program realizes the encoded answer**: at a round-`j` marker, the Program branch reissues the
   complete encoded `gᵢ` answer and realizes its first challenge symbol plus exactly
   `challengeSize j - 1` remaining symbols.  It either reuses the existing first mapping or
   materializes it; only the latter stores the `Lᵥ(j)-1` rate-only continuation
   (`item5_program`, via `ProgramOccurrence`).
6. **unique earlier `Program` mapping**: a Step 4.e.ii reuse is tied to an earlier Step 4.e.iii
   materialization with the same complete key and same mapping.  That origin is unique at the
   mapping-data level (`item6_unique_program`), so no provenance table is needed.
7. **marker/key reconciliation**: the same complete encoded key determines one marker position
   (a marker input determines at most one decoded key); the memo's agreement with the real
   encoded-trace insertion order is the core's `memoizes` (`item7_key_reconciliation`).

Every item is tied to a concrete execution/position with real predecessor/successor links — no
globally-quantified placeholder, no `x = x`, no generic list/schedule fact standing in for a paper
item. -/
structure Lemma525 {StmtIn : Type} {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat} [DecidableEq StmtIn]
    [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (replay : DuplexSpongeFS.Statement.ReplayExecution StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (history : DuplexSpongeFS.Statement.ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog replay.trace)
    (encodedTrace : D2SAlgo.EncodedTrace StmtIn pSpec U δ)
    (memo : (i : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i)) : Prop where
  good : ¬ BadEventDS.E replay.trace
  -- `history` is not an auxiliary arbitrary trace: it is the ordered realization of *this* replay.
  history_trace : history.trace = replay.trace
  /-- The history and replay also have the same terminal cursor.  Thus the round-indexed marker
  contexts used by Program/LookAhead and the replay's exact `N_𝒱` count describe one execution. -/
  history_final :
    history.cursors (DuplexSpongeFS.protocolPhases (pSpec := pSpec)).length = replay.final
  core : Lemma525Core pSpec U replay.trace trΔ h_trΔ encodedTrace memo
  -- Item 1: the replayed final cursor is the concrete duplex cursor whose count is the exact N_𝒱.
  item1_cursor :
    replay.final.queryIndex = DuplexSpongeFS.verifierPermCallCount (pSpec := pSpec) (δ := δ)
  -- Item 2: separate, trace-derived frames over this actual replay.  The leading salt and all
  -- prover absorbs use the scheduler's complete source-write set in (11a), which is valid even
  -- when an absorb ends inside the current rate block and emits no query.  The (11b) squeeze run
  -- remains a separate successor-linked check over actual emitted forward calls.
  item2_replay_frames :
    DuplexSpongeFS.Statement.AbsorbFrameCheck (U := U) SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) replay.trace ∧
      DuplexSpongeFS.Statement.replaySqueezeFramesHeld (U := U) SpongeSize.R replay.trace
        (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) replay.salt_start
  -- Item 3: a certified marker is the exact first-squeeze query of a nonempty challenge round.
  item3_marker :
    ∀ pos : ℕ,
      DuplexSpongeFS.Statement.ReplayHasMarker SpongeSize.R δ
        (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) pos ↔
        ∃ j : pSpec.ChallengeIdx, 0 < challengeSize j ∧
          DuplexSpongeFS.Statement.RoundMarker pSpec SpongeSize.R δ
            (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) j pos
  -- Item 4: the two search procedures receive different, exact table views. Backtrack sees the
  -- current strict-prefix `normal` state at round `j`; LookAhead sees a table mirroring the whole
  -- replay trace. Neither call may silently substitute the other table.
  item4_search_tables :
    ∀ (j : pSpec.ChallengeIdx) (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
      (fullDelta : TraceNabla T_H T_P StmtIn U) (state : CanonicalSpongeState U),
      j.1.1 < (DuplexSpongeFS.protocolPhases (pSpec := pSpec)).length →
      (history.tracePrefix j.1.1).Sublist normal.state.trace →
      fullDelta.MirrorsQueryLog replay.trace →
        DuplexSpongeFS.Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
          normal.state.trace normal.state.trΔ normal.state.h_inv state ≠ ExperimentOutput.err ∧
        DuplexSpongeFS.Lookahead.lookAhead (pSpec := pSpec) fullDelta.p state j ≠
          (pure ExperimentOutput.err : OracleComp (Unit →ₒ U)
            (ExperimentOutput (Vector U (challengeSize j))))
  -- Item 5: the Program branch realizes the full memoized answer at the round-`j` marker.  Its
  -- encoded answer has `challengeSize j - 1` residual symbols.  The Program call is explicitly
  -- either a Step 4.e.ii reuse or a Step 4.e.iii materialization; only the latter has the
  -- `Lᵥ(j)-1` residual rate-block continuation.
  item5_program :
    ∀ j : pSpec.ChallengeIdx, 0 < challengeSize j →
      ∀ pos : ℕ,
        DuplexSpongeFS.Statement.RoundMarker pSpec SpongeSize.R δ
          (DuplexSpongeFS.protocolPhases (pSpec := pSpec)) j pos →
          ∃ occ : ProgramOccurrence (StmtIn := StmtIn) pSpec U δ T_H T_P history memo,
            occ.j = j ∧ occ.pos = pos ∧
              (occ.Reuses ∨ occ.Materializes)
  -- Item 6: an existing mapping at a Program call has the unique earlier materializing Program
  -- origin required by the paper.  We state uniqueness at the semantic mapping-data level rather
  -- than as equality of proof records: it is exactly the output/capacity/tail identity needed to
  -- remove a provenance table and is substantially easier to prove from the base-trace events.
  item6_unique_program :
    ∀ reuse : ProgramOccurrence (StmtIn := StmtIn) pSpec U δ T_H T_P history memo,
      reuse.Reuses →
        ∃ origin : ProgramOccurrence (StmtIn := StmtIn) pSpec U δ T_H T_P history memo,
          origin.Materializes ∧
            ∃ h : origin.j = reuse.j,
              origin.key = h.symm ▸ reuse.key ∧
                origin.program_witness.stateIn = reuse.program_witness.stateIn ∧
                  origin.program_witness.stateOut = reuse.program_witness.stateOut ∧
                    origin.normal.state.trace.length < reuse.normal.state.trace.length ∧
                      ∀ origin' : ProgramOccurrence (StmtIn := StmtIn) pSpec U δ T_H T_P
                        history memo,
                        origin'.Materializes →
                        ∀ h' : origin'.j = reuse.j,
                          origin'.key = h'.symm ▸ reuse.key →
                            origin'.program_witness.stateIn = reuse.program_witness.stateIn →
                              origin'.program_witness.stateOut = reuse.program_witness.stateOut →
                              origin'.normal.state.trace.length <
                                reuse.normal.state.trace.length →
                                  origin'.initialCapacity = origin.initialCapacity ∧
                                    origin'.lazyTail = origin.lazyTail
  -- Item 7: the same complete encoded key determines one marker position (one marker input — at
  -- most one decoded key); the memo insertion-order agreement is the core's `memoizes`.
  item7_key_reconciliation :
    ∀ (occ₁ occ₂ : ProgramOccurrence (StmtIn := StmtIn) pSpec U δ T_H T_P history memo),
      ∀ h : occ₁.j = occ₂.j, occ₁.key = h.symm ▸ occ₂.key →
        HashFunctionalOnTrace replay.trace → occ₁.pos = occ₂.pos

end Statement

end DuplexSpongeFS
