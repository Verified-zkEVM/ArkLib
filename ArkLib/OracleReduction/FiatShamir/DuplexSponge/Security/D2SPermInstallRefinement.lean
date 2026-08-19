/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedInstall
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedForward
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.D2SBranch

/-!
# Revised permutation-Install refinement

This is the intentionally narrow bridge between the executable revised `Install` handlers and
the acyclic Section 5 statement layer.  It proves the common tail of Algorithm 5.3:

```text
Install → append the actual occurrence → Monitor → continue | stopped
```

for both forward and inverse permutation queries.  The bridge is deliberately below the
BackTrack/LookAhead branch selection: a resolved pair has already selected its input/output
states, so it cannot report an underlying search abort.  This lets the later first-event proof
reuse one proved transition contract rather than re-open the three Install cases at every caller.
-/

noncomputable section

namespace DuplexSpongeFS

namespace ProverTransform

open OracleComp OracleSpec ProtocolSpec DSTraceStorage
open DuplexSpongeFS.Statement

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [codec : Codec pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- The executable forward `Install` handler realizes the statement-layer forward transition.

In particular, this rules out the legacy ambiguity where a table conflict and an underlying
BackTrack failure both appeared as `none`: conflict is an actual post-occurrence `stopped`
result, while this resolved handler never reaches `underlyingAbort`. -/
theorem d2sInstallPermForwardStateRevised_refines_D2SStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U) :
    D2SQuery.D2SStep normal (.inl stateIn)
      (d2sInstallPermForwardStateRevised normal stateIn stateOut) := by
  classical
  generalize hresult :
    d2sInstallPermForwardStateRevised normal stateIn stateOut = result
  cases result
  next _ _ =>
    simp only [D2SQuery.D2SStep]
    unfold d2sInstallPermForwardStateRevised at hresult
    split at hresult
    · simp_all
    · split at hresult
      · simp_all
      · injection hresult with hanswer hstate
        subst_vars
        simp [D2SQuery.InstallStatusFor, *]
    · split at hresult
      · simp_all
      · injection hresult with hanswer hstate
        subst_vars
        simp [D2SQuery.InstallStatusFor, *]
  next _ _ =>
    simp only [D2SQuery.D2SStep]
    unfold d2sInstallPermForwardStateRevised at hresult
    split at hresult
    · injection hresult with hpre hrecord
      subst_vars
      exact ⟨rfl, stateOut, rfl, rfl⟩
    · split at hresult
      · injection hresult with hpre hrecord
        subst_vars
        exact ⟨rfl, stateOut, rfl, rfl⟩
      · simp_all
    · split at hresult
      · injection hresult with hpre hrecord
        subst_vars
        exact ⟨rfl, stateOut, rfl, rfl⟩
      · simp_all
  next =>
    simp only [D2SQuery.D2SStep]
    unfold d2sInstallPermForwardStateRevised at hresult
    split at hresult
    · simp_all
    · split at hresult <;> simp_all
    · split at hresult <;> simp_all

/-- The executable inverse `Install` handler realizes the statement-layer normalized inverse
transition.  The terminal occurrence is `p⁻¹(stateOut) ↦ stateIn`, while the installed relation
remains the forward pair `stateIn ↦ stateOut`. -/
theorem d2sInstallPermInverseStateRevised_refines_D2SStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U) :
    D2SQuery.D2SStep normal (.inr stateOut)
      (d2sInstallPermInverseStateRevised normal stateOut stateIn) := by
  classical
  generalize hresult :
    d2sInstallPermInverseStateRevised normal stateOut stateIn = result
  cases result
  next _ _ =>
    simp only [D2SQuery.D2SStep]
    unfold d2sInstallPermInverseStateRevised at hresult
    split at hresult
    · simp_all
    · split at hresult
      · simp_all
      · injection hresult with hanswer hstate
        subst_vars
        simp [D2SQuery.InstallStatusFor, *]
    · split at hresult
      · simp_all
      · injection hresult with hanswer hstate
        subst_vars
        simp [D2SQuery.InstallStatusFor, *]
  next _ _ =>
    simp only [D2SQuery.D2SStep]
    unfold d2sInstallPermInverseStateRevised at hresult
    split at hresult
    · injection hresult with hpre hrecord
      subst_vars
      exact ⟨rfl, stateIn, rfl, rfl⟩
    · split at hresult
      · injection hresult with hpre hrecord
        subst_vars
        exact ⟨rfl, stateIn, rfl, rfl⟩
      · simp_all
    · split at hresult
      · injection hresult with hpre hrecord
        subst_vars
        exact ⟨rfl, stateIn, rfl, rfl⟩
      · simp_all
  next =>
    simp only [D2SQuery.D2SStep]
    unfold d2sInstallPermInverseStateRevised at hresult
    split at hresult
    · simp_all
    · split at hresult <;> simp_all
    · split at hresult <;> simp_all

/-- The common resolved-action executor refines the shared statement transition for either
direction.  This is the induction entry point for a first-bad-event argument over a list of
already-resolved permutation actions. -/
theorem d2sPermResolvedStep_refines_D2SStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (action : D2SPermResolvedAction U) :
    match action with
    | .forward stateIn _ =>
        D2SQuery.D2SStep normal (.inl stateIn) (d2sPermResolvedStep normal action)
    | .inverse stateOut _ =>
        D2SQuery.D2SStep normal (.inr stateOut) (d2sPermResolvedStep normal action) := by
  cases action with
  | forward stateIn stateOut =>
      simpa using d2sInstallPermForwardStateRevised_refines_D2SStep
        (normal := normal) stateIn stateOut
  | inverse stateOut stateIn =>
      simpa using d2sInstallPermInverseStateRevised_refines_D2SStep
        (normal := normal) stateOut stateIn

/-! ## Branch-outcome packaging

The common resolved transition is deliberately lower-level than the six paper branches: it knows
the selected pair, but not *why* the pair was selected.  These two lemmas package its actual
three-way result as a forward or inverse branch outcome.  A caller supplies only the branch-local
effect that a continuing state must satisfy (for example, the unchanged inverse cache or a
table-hit's unchanged table).  Thus every branch reuses the same conflict/Monitor proof rather
than duplicating it.
-/

/-- A resolved executable forward install has the exact statement-layer forward outcome once its
branch-local continuing effect is supplied.  The stopped face retains the attempted occurrence;
the executable common tail cannot report an underlying search abort. -/
theorem d2sInstallPermForwardStateRevised_refines_ForwardBranchOutcome
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (status : D2SQuery.InstallStatus)
    (continueEffect : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P → Prop)
    (hStatus : status = permInstallStatus normal.state.trΔ.p stateIn stateOut)
    (hContinue : ∀ newNormal,
      d2sInstallPermForwardStateRevised normal stateIn stateOut =
        .continue stateOut newNormal →
        continueEffect newNormal) :
    D2SQuery.ForwardBranchOutcome normal stateIn stateOut status
      (d2sInstallPermForwardStateRevised normal stateIn stateOut) continueEffect := by
  unfold D2SQuery.ForwardBranchOutcome
  constructor
  · simpa [D2SQuery.InstallStatusFor] using hStatus
  constructor
  · exact d2sInstallPermForwardStateRevised_refines_D2SStep normal stateIn stateOut
  generalize hresult : d2sInstallPermForwardStateRevised normal stateIn stateOut = result
  cases result
  next answer newNormal =>
    simp only
    have hanswer : answer = stateOut := by
      unfold d2sInstallPermForwardStateRevised at hresult
      split at hresult
      · simp_all
      · split at hresult
        · simp_all
        · injection hresult with hanswer _
          exact hanswer.symm
      · split at hresult
        · simp_all
        · injection hresult with hanswer _
          exact hanswer.symm
    subst answer
    exact ⟨rfl, hContinue newNormal hresult⟩
  next state record =>
    simp only
    unfold d2sInstallPermForwardStateRevised at hresult
    split at hresult
    · injection hresult with hstate hrecord
      subst_vars
      exact ⟨rfl, ⟨rfl, rfl⟩⟩
    · split at hresult
      · injection hresult with hstate hrecord
        subst_vars
        exact ⟨rfl, ⟨rfl, rfl⟩⟩
      · simp_all
    · split at hresult
      · injection hresult with hstate hrecord
        subst_vars
        exact ⟨rfl, ⟨rfl, rfl⟩⟩
      · simp_all
  next =>
    simp only
    exact False.elim (d2sPermResolvedStep_ne_underlyingAbort normal
      (.forward stateIn stateOut) (by simpa using hresult))

/-- A resolved executable inverse install has the exact statement-layer inverse outcome once its
branch-local continuing effect is supplied.  In particular, the stopped record contains the
actual inverse occurrence, while the installed normalized pair remains forward. -/
theorem d2sInstallPermInverseStateRevised_refines_InverseBranchOutcome
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (status : D2SQuery.InstallStatus)
    (continueEffect : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P → Prop)
    (hStatus : status = permInstallStatus normal.state.trΔ.p stateIn stateOut)
    (hContinue : ∀ newNormal,
      d2sInstallPermInverseStateRevised normal stateOut stateIn =
        .continue stateIn newNormal →
        continueEffect newNormal) :
    D2SQuery.InverseBranchOutcome normal stateIn stateOut status
      (d2sInstallPermInverseStateRevised normal stateOut stateIn) continueEffect := by
  unfold D2SQuery.InverseBranchOutcome
  constructor
  · simpa [D2SQuery.InstallStatusFor] using hStatus
  constructor
  · exact d2sInstallPermInverseStateRevised_refines_D2SStep normal stateOut stateIn
  generalize hresult : d2sInstallPermInverseStateRevised normal stateOut stateIn = result
  cases result
  next answer newNormal =>
    simp only
    have hanswer : answer = stateIn := by
      unfold d2sInstallPermInverseStateRevised at hresult
      split at hresult
      · simp_all
      · split at hresult
        · simp_all
        · injection hresult with hanswer _
          exact hanswer.symm
      · split at hresult
        · simp_all
        · injection hresult with hanswer _
          exact hanswer.symm
    subst answer
    exact ⟨rfl, hContinue newNormal hresult⟩
  next state record =>
    simp only
    unfold d2sInstallPermInverseStateRevised at hresult
    split at hresult
    · injection hresult with hstate hrecord
      subst_vars
      exact ⟨rfl, ⟨rfl, rfl⟩⟩
    · split at hresult
      · injection hresult with hstate hrecord
        subst_vars
        exact ⟨rfl, ⟨rfl, rfl⟩⟩
      · simp_all
    · split at hresult
      · injection hresult with hstate hrecord
        subst_vars
        exact ⟨rfl, ⟨rfl, rfl⟩⟩
      · simp_all
  next =>
    simp only
    exact False.elim (d2sPermResolvedStep_ne_underlyingAbort normal
      (.inverse stateOut stateIn) (by simpa using hresult))

/-- Re-keying the rate-only cache of a continuing result preserves the forward `D2SStep`
contract.  The transition core observes only the inserted occurrence and normalized table; a
terminal record remains unchanged, so a cache replacement cannot turn a monitor stop into a
reusable state. -/
theorem d2sReplaceRateCacheOnContinue_refines_D2SStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (rateCacheP : List (RateOnlyCacheEntry (U := U)))
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hStep : D2SQuery.D2SStep normal (.inl stateIn) result) :
    D2SQuery.D2SStep normal (.inl stateIn)
      (d2sReplaceRateCacheOnContinue rateCacheP result) := by
  cases result
  next answer oldNormal =>
    simp only [d2sReplaceRateCacheOnContinue, D2SQuery.D2SStep] at hStep ⊢
    rcases hStep with ⟨hStatus, hMonitor, hTrace, hTable⟩
    exact ⟨hStatus, hMonitor, by simpa using hTrace, by simpa using hTable⟩
  next oldNormal record =>
    simpa [d2sReplaceRateCacheOnContinue] using hStep
  next =>
    simpa [d2sReplaceRateCacheOnContinue] using hStep

/-- Re-keying a continuing cache transports a forward branch outcome to the exact new-cache
effect.  This is the common proof step for lazy-tail consumption and `Program` residual tails. -/
theorem d2sReplaceRateCacheOnContinue_refines_ForwardBranchOutcome
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (status : D2SQuery.InstallStatus)
    (baseEffect : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P → Prop)
    (rateCacheP : List (RateOnlyCacheEntry (U := U)))
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hOutcome : D2SQuery.ForwardBranchOutcome normal stateIn stateOut status result baseEffect) :
    D2SQuery.ForwardBranchOutcome normal stateIn stateOut status
      (d2sReplaceRateCacheOnContinue rateCacheP result)
      (fun newNormal => newNormal.state.rateCacheP = rateCacheP) := by
  rcases hOutcome with ⟨hStatus, hStep, hOutcome⟩
  unfold D2SQuery.ForwardBranchOutcome
  refine ⟨hStatus, ?_, ?_⟩
  · exact d2sReplaceRateCacheOnContinue_refines_D2SStep normal stateIn rateCacheP result hStep
  cases result
  next answer oldNormal =>
    simp only [d2sReplaceRateCacheOnContinue]
    exact ⟨hOutcome.1, True.intro⟩
  next oldNormal record =>
    exact hOutcome
  next =>
    exact hOutcome

/-- The live inverse handler's resolved transition realizes the exact Step 3 branch: it never
reads the rate-only cache and routes every `Install` conflict through the common Monitor stop. -/
theorem d2sInstallPermInverseStateRevised_refines_BranchInverseQuery
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U) :
    D2SQuery.BranchInverseQuery normal stateIn stateOut
      (permInstallStatus normal.state.trΔ.p stateIn stateOut)
      (d2sInstallPermInverseStateRevised normal stateOut stateIn) := by
  unfold D2SQuery.BranchInverseQuery
  apply d2sInstallPermInverseStateRevised_refines_InverseBranchOutcome
    normal stateOut stateIn
  · rfl
  · intro newNormal hContinue
    exact d2sInstallPermInverseStateRevised_continue_cache normal stateOut stateIn hContinue

/-- The deterministic half of Algorithm 5.3 Step 3.  A reverse-table hit makes no random draw,
and its exact result is already a shared six-branch witness. -/
theorem d2sHandleInversePermQueryRevised_hit_refines_BranchStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = some stateIn) :
    d2sHandleInversePermQueryRevised normal stateOut =
      pure (d2sInstallPermInverseStateRevised normal stateOut stateIn) ∧
      D2SQuery.D2SBranchStep normal none (.inr (.inr stateOut))
        (d2sInstallPermInverseStateRevised normal stateOut stateIn) := by
  constructor
  · exact d2sHandleInversePermQueryRevised_hit normal stateOut stateIn hLookup
  · exact .inverse stateIn stateOut
      (permInstallStatus normal.state.trΔ.p stateIn stateOut)
      (d2sInstallPermInverseStateRevised normal stateOut stateIn)
      (d2sInstallPermInverseStateRevised_refines_BranchInverseQuery normal stateOut stateIn)

/-- The sampling half of Algorithm 5.3 Step 3.  A reverse-table miss exposes exactly one sampled
full preimage, and every sample produces the exact shared inverse-branch witness.  This is the
inverse counterpart to the ordinary forward miss interface below. -/
theorem d2sHandleInversePermQueryRevised_miss_refines_BranchStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none) :
    (d2sHandleInversePermQueryRevised normal stateOut =
      d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun stateIn =>
        pure (d2sInstallPermInverseStateRevised normal stateOut stateIn)) ∧
      ∀ stateIn : CanonicalSpongeState U,
        D2SQuery.D2SBranchStep normal none (.inr (.inr stateOut))
          (d2sInstallPermInverseStateRevised normal stateOut stateIn) := by
  constructor
  · exact d2sHandleInversePermQueryRevised_miss normal stateOut hLookup
  · intro stateIn
    exact .inverse stateIn stateOut
      (permInstallStatus normal.state.trΔ.p stateIn stateOut)
      (d2sInstallPermInverseStateRevised normal stateOut stateIn)
      (d2sInstallPermInverseStateRevised_refines_BranchInverseQuery normal stateOut stateIn)

/-- A selected forward-table hit realizes Algorithm 5.3 Step 4.c.ii: a `present` install leaves
both the normalized table and the rate-only cache unchanged, while still appending and monitoring
the repeated occurrence. -/
theorem d2sInstallPermForwardStateRevised_refines_BranchTableHit
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present) :
    D2SQuery.BranchTableHit normal stateIn stateOut .present
      (d2sInstallPermForwardStateRevised normal stateIn stateOut) := by
  unfold D2SQuery.BranchTableHit
  constructor
  · rfl
  apply d2sInstallPermForwardStateRevised_refines_ForwardBranchOutcome
    normal stateIn stateOut .present
  · simpa [D2SQuery.InstallStatusFor] using hStatus.symm
  · intro newNormal hContinue
    exact ⟨d2sInstallPermForwardStateRevised_continue_table_present normal stateIn stateOut
      hStatus hContinue,
      d2sInstallPermForwardStateRevised_continue_cache normal stateIn stateOut hContinue⟩

/-- The live Step 4.c dispatcher turns its concrete tail-miss/table-hit guards into the exact
table-hit branch atom.  The auxiliary status proof is not an extra assumption: on a monitored
normal state, a successful table lookup is automatically a `present` `Install`. -/
theorem d2sHandleForwardNoResultRevised_tableHit_refines_BranchTableHit
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    d2sHandleForwardNoResultRevised normal stateIn =
      pure (d2sInstallPermForwardStateRevised normal stateIn stateOut) ∧
      D2SQuery.BranchTableHit normal stateIn stateOut .present
        (d2sInstallPermForwardStateRevised normal stateIn stateOut) := by
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present :=
    permInstallStatus_present_of_inlu_eq_some normal stateIn stateOut hLookup
  constructor
  · simp [d2sHandleForwardNoResultRevised, hPop, hLookup]
  · exact d2sInstallPermForwardStateRevised_refines_BranchTableHit normal stateIn stateOut hStatus

/-- The deterministic table-hit selection of Algorithm 5.3 Step 4.c.ii, packaged directly as a
shared branch witness.  The pair is re-recorded and monitored even though `Install` is `present`;
this is what keeps the insertion trace aligned with repeated queries. -/
theorem d2sHandleForwardNoResultRevised_tableHit_refines_BranchStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    d2sHandleForwardNoResultRevised normal stateIn =
      pure (d2sInstallPermForwardStateRevised normal stateIn stateOut) ∧
      D2SQuery.D2SBranchStep normal none (.inr (.inl stateIn))
        (d2sInstallPermForwardStateRevised normal stateIn stateOut) := by
  rcases d2sHandleForwardNoResultRevised_tableHit_refines_BranchTableHit normal stateIn stateOut
    hPop hLookup with ⟨hRun, hBranch⟩
  refine ⟨hRun, ?_⟩
  exact .tableHit stateIn stateOut .present
    (d2sInstallPermForwardStateRevised normal stateIn stateOut) hBranch

/-- A selected ordinary miss realizes Algorithm 5.3 Step 4.c.iii.  `TabularMiss` excludes both a
normalized-table answer and a rate-only-tail answer, so sampling is the only forward selection.
The sampled full state can nevertheless collide with the partial permutation: `fresh` continues
with the unchanged cache, while `conflict` records the exact occurrence and stops. -/
theorem d2sInstallPermForwardStateRevised_refines_BranchFreshMiss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh ∨
      permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict)
    (hMiss : D2SQuery.TabularMiss normal stateIn) :
    D2SQuery.BranchFreshMiss normal stateIn stateOut
      (permInstallStatus normal.state.trΔ.p stateIn stateOut)
      (d2sInstallPermForwardStateRevised normal stateIn stateOut) := by
  unfold D2SQuery.BranchFreshMiss
  constructor
  · exact hStatus
  constructor
  · exact hMiss
  apply d2sInstallPermForwardStateRevised_refines_ForwardBranchOutcome
    normal stateIn stateOut (permInstallStatus normal.state.trΔ.p stateIn stateOut)
  · rfl
  · intro newNormal hContinue
    exact d2sInstallPermForwardStateRevised_continue_cache normal stateIn stateOut hContinue

/-- The complete sampling interface of Algorithm 5.3 Step 4.c.iii.  Once the live dispatcher has
established the two ordinary-miss guards, it makes exactly one full-state sample.  **Every**
possible sampled state is then classified by the same branch atom: a lookup miss excludes only
`present`, so the sample either installs freshly or records a conflicting occurrence and stops.

This packages the sampler equation and the pointwise branch classification together.  The eventual
first-event proof can consequently expose one sample and reason directly by its `fresh | conflict`
classification, without re-opening the table/cache dispatcher. -/
theorem d2sHandleForwardNoResultRevised_fresh_refines_BranchFreshMiss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    (d2sHandleForwardNoResultRevised normal stateIn =
      d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun stateOut =>
        pure (d2sInstallPermForwardStateRevised normal stateIn stateOut)) ∧
      ∀ stateOut : CanonicalSpongeState U,
        D2SQuery.BranchFreshMiss normal stateIn stateOut
          (permInstallStatus normal.state.trΔ.p stateIn stateOut)
          (d2sInstallPermForwardStateRevised normal stateIn stateOut) := by
  constructor
  · exact d2sHandleForwardNoResultRevised_fresh normal stateIn hPop hLookup
  · intro stateOut
    exact d2sInstallPermForwardStateRevised_refines_BranchFreshMiss normal stateIn stateOut
      (permInstallStatus_fresh_or_conflict_of_inlu_eq_none normal stateIn stateOut hLookup)
      ⟨hLookup, hPop⟩

/-- The ordinary fresh-miss sampler, now expressed at the common `D2SBranchStep` boundary used by
the whole query-stream fold.  This is the exact reusable lemma for the fresh-vs-conflict charge in
the eventual stopped-run Lemma 5.8 proof. -/
theorem d2sHandleForwardNoResultRevised_fresh_refines_BranchStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    (d2sHandleForwardNoResultRevised normal stateIn =
      d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun stateOut =>
        pure (d2sInstallPermForwardStateRevised normal stateIn stateOut)) ∧
      ∀ stateOut : CanonicalSpongeState U,
        D2SQuery.D2SBranchStep normal none (.inr (.inl stateIn))
          (d2sInstallPermForwardStateRevised normal stateIn stateOut) := by
  rcases d2sHandleForwardNoResultRevised_fresh_refines_BranchFreshMiss normal stateIn hPop hLookup
    with ⟨hRun, hBranch⟩
  refine ⟨hRun, ?_⟩
  intro stateOut
  exact .freshMiss stateIn stateOut
    (permInstallStatus normal.state.trΔ.p stateIn stateOut)
    (d2sInstallPermForwardStateRevised normal stateIn stateOut) (hBranch stateOut)

/-- A selected rate-only tail realizes Algorithm 5.3 Step 4.c.i.  The capacity is materialized
only at consumption, the residual cache is re-keyed at the resulting output, and the common
forward `Install → append → Monitor` contract is preserved verbatim. -/
theorem d2sConsumePoppedRateOnlyTailRevised_refines_BranchCacheTailHit
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP entry.stateIn =
      some (entry.tail, cacheRest)) :
    D2SQuery.BranchCacheTailHit normal entry.stateIn
      (materializeRateOnlyCacheEntry (U := U) entry capacity).1 capacity
      (permInstallStatus normal.state.trΔ.p entry.stateIn
        (materializeRateOnlyCacheEntry (U := U) entry capacity).1)
      (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity) := by
  let stateOut := (materializeRateOnlyCacheEntry (U := U) entry capacity).1
  let residual := rateOnlyTailResidualCache entry cacheRest capacity
  refine ⟨residual, ?_, ?_⟩
  · unfold D2SQuery.ConsumeTailMaterializesOneCapacity consumeRateOnlyCache
    rw [hPop]
    rfl
  have hBase : D2SQuery.ForwardBranchOutcome normal entry.stateIn stateOut
      (permInstallStatus normal.state.trΔ.p entry.stateIn stateOut)
      (d2sPermResolvedStep normal (.forward entry.stateIn stateOut)) (fun _ => True) := by
    simpa [d2sPermResolvedStep_forward] using
      d2sInstallPermForwardStateRevised_refines_ForwardBranchOutcome normal entry.stateIn stateOut
        (permInstallStatus normal.state.trΔ.p entry.stateIn stateOut) (fun _ => True) rfl
        (fun _ _ => True.intro)
  have hTail : D2SQuery.ForwardBranchOutcome normal entry.stateIn stateOut
      (permInstallStatus normal.state.trΔ.p entry.stateIn stateOut)
      (d2sReplaceRateCacheOnContinue residual
        (d2sPermResolvedStep normal (.forward entry.stateIn stateOut)))
      (fun newNormal => newNormal.state.rateCacheP = residual) :=
    d2sReplaceRateCacheOnContinue_refines_ForwardBranchOutcome normal entry.stateIn stateOut
      (permInstallStatus normal.state.trΔ.p entry.stateIn stateOut) (fun _ => True) residual
      (d2sPermResolvedStep normal (.forward entry.stateIn stateOut)) hBase
  simpa [d2sConsumePoppedRateOnlyTailRevised, stateOut, residual] using hTail

/-- The tail-selected half of Algorithm 5.3 Step 4.c.  The live dispatcher exposes exactly one
capacity sample and maps every sampled capacity to the `tailHit` shared witness.  This is the
critical lazy-sampling interface: capacities for later verifier blocks are absent until the tail
is actually consumed. -/
theorem d2sHandleForwardNoResultRevised_tail_refines_BranchStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = some (tail, cacheRest)) :
    (d2sHandleForwardNoResultRevised normal stateIn =
      d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun capacity =>
        pure (d2sConsumePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest capacity)) ∧
      ∀ capacity : Vector U SpongeSize.C,
        D2SQuery.D2SBranchStep normal none (.inr (.inl stateIn))
          (d2sConsumePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest capacity) := by
  constructor
  · rw [d2sHandleForwardNoResultRevised_tail normal stateIn tail cacheRest hPop]
    exact d2sHandlePoppedRateOnlyTailRevised_eq normal ⟨stateIn, tail⟩ cacheRest
  · intro capacity
    exact .tailHit stateIn
      (materializeRateOnlyCacheEntry (U := U) ⟨stateIn, tail⟩ capacity).1
      capacity
      (permInstallStatus normal.state.trΔ.p stateIn
        (materializeRateOnlyCacheEntry (U := U) ⟨stateIn, tail⟩ capacity).1)
      (d2sConsumePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest capacity)
      (d2sConsumePoppedRateOnlyTailRevised_refines_BranchCacheTailHit normal ⟨stateIn, tail⟩
        cacheRest capacity (by simpa using hPop))

/-- The low-level fresh Program materialization realizes Step 4.e once parsing has certified the
round-indexed residual-rate length.  The theorem deliberately permits a conflicting `Install`:
Program selection precedes `Install`, and a collision is represented by the common post-occurrence
`stopped` result.  Only a continuing result receives the exact round-indexed residual cache. -/
theorem d2sProgramFirstRateRevised_refines_BranchProgram
    (context : D2SQuery.ProgramContext pSpec)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (capacity : Vector U SpongeSize.C)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    (hMarker : Certified SpongeSize.R context.cursor (challengeSize context.round) context.pos)
    (hRates : D2SQuery.ProgramRemainingRatesForRound (pSpec := pSpec) (U := U)
      context.round remainingRates) :
    D2SQuery.BranchProgram context normal stateIn
      (d2sSynthesisState (U := U) firstRate capacity)
      (permInstallStatus normal.state.trΔ.p stateIn
        (d2sSynthesisState (U := U) firstRate capacity))
      (RateOnlyTail.ofBlocks? (U := U) remainingRates)
      (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity) := by
  let stateOut := d2sSynthesisState (U := U) firstRate capacity
  let residualCache := programResidualRateCache normal stateOut remainingRates
  have hBase : D2SQuery.ForwardBranchOutcome normal stateIn stateOut
      (permInstallStatus normal.state.trΔ.p stateIn stateOut)
      (d2sPermResolvedStep normal (.forward stateIn stateOut)) (fun _ => True) := by
    simpa [d2sPermResolvedStep_forward] using
      d2sInstallPermForwardStateRevised_refines_ForwardBranchOutcome normal stateIn stateOut
        (permInstallStatus normal.state.trΔ.p stateIn stateOut) (fun _ => True) rfl
        (fun _ _ => True.intro)
  have hOutcome : D2SQuery.ForwardBranchOutcome normal stateIn stateOut
      (permInstallStatus normal.state.trΔ.p stateIn stateOut)
      (d2sReplaceRateCacheOnContinue residualCache
        (d2sPermResolvedStep normal (.forward stateIn stateOut)))
      (fun newNormal => newNormal.state.rateCacheP = residualCache) :=
    d2sReplaceRateCacheOnContinue_refines_ForwardBranchOutcome normal stateIn stateOut
      (permInstallStatus normal.state.trΔ.p stateIn stateOut) (fun _ => True) residualCache
      (d2sPermResolvedStep normal (.forward stateIn stateOut)) hBase
  unfold D2SQuery.BranchProgram
  refine ⟨hPop, hMarker, Or.inr ⟨hLookup, ?_⟩⟩
  simpa only [d2sProgramFirstRateRevised, stateOut] using
    show D2SQuery.ForwardBranchOutcome normal stateIn stateOut
      (permInstallStatus normal.state.trΔ.p stateIn stateOut)
      (d2sReplaceRateCacheOnContinue residualCache
        (d2sPermResolvedStep normal (.forward stateIn stateOut)))
      (fun newNormal => D2SQuery.ProgramTailRealization pSpec U T_H T_P context.round normal
        stateOut newNormal (RateOnlyTail.ofBlocks? (U := U) remainingRates)) from by
      rcases hOutcome with ⟨hStatus, hStep, hFace⟩
      refine ⟨hStatus, hStep, ?_⟩
      generalize hResult : d2sReplaceRateCacheOnContinue residualCache
          (d2sPermResolvedStep normal (.forward stateIn stateOut)) = result at hFace ⊢
      cases result
      · rcases hFace with ⟨hAnswer, hCache⟩
        refine ⟨hAnswer, ?_⟩
        cases remainingRates with
        | nil =>
            simpa [D2SQuery.ProgramTailRealization,
              D2SQuery.ProgramRemainingRatesForRound, programResidualRateCache,
              RateOnlyTail.ofBlocks?] using ⟨hRates, hCache⟩
        | cons next remaining =>
            rcases hRates with ⟨hLengthPositive, hLength⟩
            simpa [D2SQuery.ProgramTailRealization,
              D2SQuery.ProgramRemainingRatesForRound, programResidualRateCache,
              RateOnlyTail.ofBlocks?, RateOnlyTail.blocks] using
              ⟨hLengthPositive, hLength, hCache⟩
      · exact hFace
      · exact hFace

omit [SpongeUnit U] [DecidableEq U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- The result of the real verifier-challenge parser discharges the rate-count half of the
`Program` branch contract.  Once a `Vector` of exactly `Lᵥ(i)` parsed rate blocks is observed to
have a first block, its remaining list has exactly `Lᵥ(i) - 1` blocks.  This deliberately keeps
parser arithmetic separate from the later cache-update proof in
`d2sProgramFirstRateRevised_refines_BranchProgram`; it is the bridge needed to compose the live
`d2sHandleBacktrackAfterGRevised` dispatcher with that branch theorem. -/
lemma programRemainingRatesForRound_of_parsedBlocks
    (j : pSpec.ChallengeIdx)
    (rateBlocks : Vector (Vector U SpongeSize.R) (pSpec.Lᵥᵢ j))
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (hBlocks : rateBlocks.toList = firstRate :: remainingRates) :
    D2SQuery.ProgramRemainingRatesForRound (pSpec := pSpec) (U := U)
      j remainingRates := by
  have hLength : remainingRates.length = pSpec.Lᵥᵢ j - 1 := by
    have hVectorLength : rateBlocks.toList.length = pSpec.Lᵥᵢ j := by
      simp
    rw [hBlocks, List.length_cons] at hVectorLength
    omega
  cases remainingRates with
  | nil =>
      change pSpec.Lᵥᵢ j ≤ 1
      simp at hLength
      omega
  | cons next rest =>
      change 1 < pSpec.Lᵥᵢ j ∧ (next :: rest).length = pSpec.Lᵥᵢ j - 1
      constructor
      · simp at hLength
        omega
      · simpa using hLength

/-- The live Program continuation's Step **4.e.ii** branch refines the corresponding statement
atom.  Once the re-issued `gᵢ` response has been obtained, an existing forward mapping is returned
before that response is parsed: no capacity is sampled and no rate-only tail is added.  The round
equality is deliberately explicit even though this reuse branch reads no round-indexed rate data:
it binds the certified marker context to the `Backtrack` tuple that caused this exact `gᵢ` query. -/
theorem d2sHandleBacktrackAfterGRevised_hit_refines_ProgramExistingMapping
    (context : D2SQuery.ProgramContext pSpec)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hRound : context.round = backtrackOut.roundIdx)
    (hMarker : Certified SpongeSize.R context.cursor (challengeSize context.round) context.pos)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat =
      pure (d2sPermResolvedStep normal (.forward stateIn stateOut)) ∧
      D2SQuery.BranchProgram context normal stateIn stateOut .present none
        (d2sPermResolvedStep normal (.forward stateIn stateOut)) ∧
      context.round = backtrackOut.roundIdx := by
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present :=
    permInstallStatus_present_of_inlu_eq_some normal stateIn stateOut hLookup
  have hOutcome : D2SQuery.ForwardBranchOutcome normal stateIn stateOut .present
      (d2sPermResolvedStep normal (.forward stateIn stateOut))
      (fun newNormal => D2SQuery.ContinueCacheIs newNormal normal.state.rateCacheP) := by
    simpa [d2sPermResolvedStep_forward] using
      d2sInstallPermForwardStateRevised_refines_ForwardBranchOutcome normal stateIn stateOut
        .present (fun newNormal =>
          D2SQuery.ContinueCacheIs newNormal normal.state.rateCacheP)
        (by simpa [D2SQuery.InstallStatusFor] using hStatus.symm)
        (fun newNormal hContinue =>
          d2sInstallPermForwardStateRevised_continue_cache normal stateIn stateOut hContinue)
  have hRun := d2sHandleBacktrackAfterGRevised_hit normal stateIn stateOut backtrackOut rhoHat
    hLookup
  refine ⟨hRun, ?_, hRound⟩
  unfold D2SQuery.BranchProgram
  refine ⟨hPop, hMarker, Or.inl ?_⟩
  exact ⟨rfl, hLookup, rfl, hOutcome⟩

/-- The same Step **4.e.ii** refinement at the six-way `D2SBranchStep` boundary used by the
whole-query runner.  It is the reuse counterpart of the materializing Program refinement above. -/
theorem d2sHandleBacktrackAfterGRevised_hit_refines_BranchStep
    (context : D2SQuery.ProgramContext pSpec)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hRound : context.round = backtrackOut.roundIdx)
    (hMarker : Certified SpongeSize.R context.cursor (challengeSize context.round) context.pos)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat =
      pure (d2sPermResolvedStep normal (.forward stateIn stateOut)) ∧
      D2SQuery.D2SBranchStep normal (some context) (.inr (.inl stateIn))
        (d2sPermResolvedStep normal (.forward stateIn stateOut)) := by
  rcases d2sHandleBacktrackAfterGRevised_hit_refines_ProgramExistingMapping context normal
      stateIn stateOut backtrackOut rhoHat hPop hRound hMarker hLookup with ⟨hRun, hBranch, _⟩
  refine ⟨hRun, ?_⟩
  exact .program context stateIn stateOut .present none
    (d2sPermResolvedStep normal (.forward stateIn stateOut)) hBranch

/-- A replayed hash-table value realizes Step 2 of D2SQuery: it appends the exact hash
occurrence, leaves the permutation table and rate-only cache unchanged, and either returns the
same stored capacity or exposes the post-occurrence monitor stop. -/
theorem d2sHandleHashPresentRevised_refines_BranchHashQuery
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = some capacity) :
    D2SQuery.BranchHashQuery normal stmt
      (d2sHandleHashPresentRevised normal stmt capacity hLookup) := by
  classical
  unfold D2SQuery.BranchHashQuery d2sHandleHashPresentRevised
  dsimp
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp [hE]
  · simp [hE, D2SQuery.HashTableTransition, hLookup]

/-- A fresh hash-table value realizes the other Step-2 case: the sampled capacity is inserted
into the real hash table before the occurrence is monitored; a monitor failure still preserves the
attempted raw occurrence in its terminal record. -/
theorem d2sHandleHashFreshRevised_refines_BranchHashQuery
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    D2SQuery.BranchHashQuery normal stmt
      (d2sHandleHashFreshRevised normal stmt capacity hLookup) := by
  classical
  unfold D2SQuery.BranchHashQuery d2sHandleHashFreshRevised
  dsimp
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp [hE]
  · simp [hE, D2SQuery.HashTableTransition, hLookup]

/-- The deterministic Step-2 hash-hit dispatcher equation together with its exact shared branch
witness.  This is the hash analogue of the inverse-hit interface: a proof that folds a stream can
consume the handler result without unpacking the hash-table implementation again. -/
theorem d2sHandleHashQueryRevised_hit_refines_BranchStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = some capacity) :
    d2sHandleHashQueryRevised normal stmt =
      pure (d2sHandleHashPresentRevised normal stmt capacity hLookup) ∧
      D2SQuery.D2SBranchStep normal none (dsHashQuery stmt)
        (d2sHandleHashPresentRevised normal stmt capacity hLookup) := by
  constructor
  · exact d2sHandleHashQueryRevised_hit normal stmt capacity hLookup
  · exact .hash stmt
      (d2sHandleHashPresentRevised_refines_BranchHashQuery normal stmt capacity hLookup)

/-- The sampling Step-2 hash-miss interface.  It exposes the single capacity sample and gives a
shared branch witness for every returned capacity, so the first-event analysis has no separate
case split hidden inside the hash handler. -/
theorem d2sHandleHashQueryRevised_miss_refines_BranchStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    (d2sHandleHashQueryRevised normal stmt =
      d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun capacity =>
        pure (d2sHandleHashFreshRevised normal stmt capacity hLookup)) ∧
      ∀ capacity : Vector U SpongeSize.C,
        D2SQuery.D2SBranchStep normal none (dsHashQuery stmt)
          (d2sHandleHashFreshRevised normal stmt capacity hLookup) := by
  constructor
  · exact d2sHandleHashQueryRevised_miss normal stmt hLookup
  · intro capacity
    exact .hash stmt
      (d2sHandleHashFreshRevised_refines_BranchHashQuery normal stmt capacity hLookup)

end ProverTransform

end DuplexSpongeFS
