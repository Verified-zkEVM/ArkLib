/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadHistory
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.AbortAnalysis
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SAmbientLazySampling

/-!
# Live no-abort refinement for revised D2SQuery

The Section 5.7 theorems establish that `Backtrack` and `LookAhead` do not fail from a reusable
monitored state.  This focused bridge transports that fact to the live forward D2S dispatcher.
It is deliberately a support theorem: a later H₀/H₁ coupling can use it to exclude a source
abort without replacing the executable dispatcher by a semantic relation.

The paper scope is `Section5Nonempty`.  In particular, Program's parsed verifier block list is
nonempty, so its old parser-abort arm is unreachable.  Every remaining branch is a resolved
`Install → add occurrence → Monitor` action and hence is either a continuation or a monitored
stop, never an `underlyingAbort`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, VCVCompatible (pSpec.Message i)]

/-- A selected tail is a one-capacity sample of a resolved forward transition, so no sample in
its live support can be the distinguished pre-occurrence abort result. -/
lemma d2sHandlePoppedRateOnlyTailRevised_no_underlyingAbort_of_support
    [VCVCompatible U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (hResult : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) ∈ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest))) : False := by
  rw [d2sHandlePoppedRateOnlyTailRevised_eq normal entry cacheRest, simulateQ_bind,
    mem_support_bind_iff] at hResult
  obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
  have hEq : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) =
      d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity := by
    simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
  exact d2sConsumePoppedRateOnlyTailRevised_ne_underlyingAbort normal entry cacheRest capacity
    hEq.symm

/-- Ordinary Step 4.c has no parser or search failure.  It either materializes a selected tail,
replays an installed pair, or samples one full output for the same resolved transition. -/
lemma d2sHandleForwardNoResultRevised_no_underlyingAbort_of_support
    [VCVCompatible U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (hResult : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) ∈ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sHandleForwardNoResultRevised normal stateIn))) : False := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleForwardNoResultRevised_tail normal stateIn tail cacheRest hPop] at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_no_underlyingAbort_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl hResult
  | none =>
      cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
      | some stateOut =>
          rw [d2sHandleForwardNoResultRevised_table normal stateIn stateOut hPop hLookup]
            at hResult
          have hEq : (.underlyingAbort : D2SRevisedStepResult
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) =
              d2sPermResolvedStep normal (.forward stateIn stateOut) := by
            simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
          exact d2sPermResolvedStep_ne_underlyingAbort normal (.forward stateIn stateOut)
            hEq.symm
      | none =>
          rw [d2sHandleForwardNoResultRevised_fresh normal stateIn hPop hLookup,
            simulateQ_bind, mem_support_bind_iff] at hResult
          obtain ⟨stateOut, _hStateOut, hResult⟩ := hResult
          have hEq : (.underlyingAbort : D2SRevisedStepResult
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) =
              d2sPermResolvedStep normal (.forward stateIn stateOut) := by
            simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
          exact d2sPermResolvedStep_ne_underlyingAbort normal (.forward stateIn stateOut)
            hEq.symm

/-- Under the Section 5 nonempty convention, a recovered Backtrack tuple cannot lead to a live
pre-occurrence abort.  The only potentially partial continuation is Program after the reissued
`gᵢ` answer; its empty-rate branch is impossible because the recovered round has positive
challenge length. -/
lemma d2sHandleBacktrackSomeRevised_no_underlyingAbort_of_support
    [VCVCompatible U] [Section5Nonempty pSpec]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (hResult : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) ∈ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut))) : False := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleBacktrackSomeRevised_tail normal stateIn backtrackOut tail cacheRest hPop]
        at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_no_underlyingAbort_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl hResult
  | none =>
      by_cases hImage : d2sInCodecImagePredicate
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut
      · have hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx :=
          Section5Nonempty.challenge_pos (pSpec := pSpec) backtrackOut.roundIdx
        rw [d2sHandleBacktrackSomeRevised_nonemptyChallenge normal stateIn backtrackOut hPop
          hImage hNonempty, simulateQ_bind, mem_support_bind_iff] at hResult
        obtain ⟨rhoHat, _hRhoHat, hResult⟩ := hResult
        exact d2sHandleBacktrackAfterGRevised_no_underlyingAbort_of_support normal stateIn
          backtrackOut rhoHat gImpl hResult
      · rw [d2sHandleBacktrackSomeRevised_notInImage normal stateIn backtrackOut hPop hImage]
          at hResult
        exact d2sHandleForwardNoResultRevised_no_underlyingAbort_of_support normal stateIn
          gImpl hResult

/-- This is the live-executor form of Claims 5.19--5.20a needed by the H₀/H₁ coupling.  On a
reusable normal state, a scheduled tail and all ordinary/program continuations are resolved
actions, while the remaining Backtrack `.err` branch is excluded by Claim 5.19.  Consequently a
forward query may stop only through `Monitor`, never before it records an occurrence. -/
lemma d2sHandleForwardPermQueryRevised_no_underlyingAbort_of_support
    [VCVCompatible U] [Section5Nonempty pSpec]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (hResult : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) ∈ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sHandleForwardPermQueryRevised normal stateIn))) : False := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleForwardPermQueryRevised_tail normal stateIn tail cacheRest hPop] at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_no_underlyingAbort_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl hResult
  | none =>
      cases hSearch : Backtrack.backTrack
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
          (normal.state.trace.length + 1) with
      | err =>
          exact (AbortAnalysis.claim_5_19_backTrack_noAbort (pSpec := pSpec) normal stateIn)
            hSearch
      | noResult =>
          rw [d2sHandleForwardPermQueryRevised_noResult normal stateIn hPop hSearch] at hResult
          exact d2sHandleForwardNoResultRevised_no_underlyingAbort_of_support normal stateIn
            gImpl hResult
      | some backtrackOut =>
          rw [d2sHandleForwardPermQueryRevised_some normal stateIn backtrackOut hPop hSearch]
            at hResult
          exact d2sHandleBacktrackSomeRevised_no_underlyingAbort_of_support normal stateIn
            backtrackOut gImpl hResult

/-- Hash queries have no search or parser face: their stored and sampled continuations append the
hash occurrence and then either continue or stop at `Monitor`. -/
lemma d2sHandleHashQueryRevised_no_underlyingAbort_of_support
    [VCVCompatible U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (hResult : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Vector U SpongeSize.C)) ∈ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sHandleHashQueryRevised normal stmt))) : False := by
  classical
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt with
  | some capacity =>
      rw [d2sHandleHashQueryRevised_hit normal stmt capacity hLookup] at hResult
      have hEq : (.underlyingAbort : D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Vector U SpongeSize.C)) =
          d2sHandleHashPresentRevised normal stmt capacity hLookup := by
        simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
      by_cases hE : BadEventDS.E
          (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
      · simp [d2sHandleHashPresentRevised, hE] at hEq
      · simp [d2sHandleHashPresentRevised, hE] at hEq
  | none =>
      rw [d2sHandleHashQueryRevised_miss normal stmt hLookup, simulateQ_bind,
        mem_support_bind_iff] at hResult
      obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
      have hEq : (.underlyingAbort : D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Vector U SpongeSize.C)) =
          d2sHandleHashFreshRevised normal stmt capacity hLookup := by
        simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
      by_cases hE : BadEventDS.E
          (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
      · simp [d2sHandleHashFreshRevised, hE] at hEq
      · simp [d2sHandleHashFreshRevised, hE] at hEq

/-- Inverse queries likewise select a concrete preimage before entering the common resolved
inverse action, so they have no pre-occurrence abort branch. -/
lemma d2sHandleInversePermQueryRevised_no_underlyingAbort_of_support
    [VCVCompatible U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (hResult : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) ∈ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sHandleInversePermQueryRevised normal stateOut))) : False := by
  cases hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut with
  | some stateIn =>
      rw [d2sHandleInversePermQueryRevised_hit normal stateOut stateIn hLookup] at hResult
      have hEq : (.underlyingAbort : D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) =
          d2sPermResolvedStep normal (.inverse stateOut stateIn) := by
        simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
      exact d2sPermResolvedStep_ne_underlyingAbort normal (.inverse stateOut stateIn)
        hEq.symm
  | none =>
      rw [d2sHandleInversePermQueryRevised_miss normal stateOut hLookup, simulateQ_bind,
        mem_support_bind_iff] at hResult
      obtain ⟨stateIn, _hStateIn, hResult⟩ := hResult
      have hEq : (.underlyingAbort : D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) =
          d2sPermResolvedStep normal (.inverse stateOut stateIn) := by
        simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
      exact d2sPermResolvedStep_ne_underlyingAbort normal (.inverse stateOut stateIn)
        hEq.symm

/-- The complete live revised D2SQuery step has no support on `underlyingAbort` in the revised
Section 5 scope.  This is the executor-level form of the §5.7 no-abort story: a normal state is
already monitored, and the only formerly partial forward faces are now excluded by Claim 5.19
and positive verifier-challenge length. -/
lemma d2sQueryStepRevised_no_underlyingAbort_of_support
    [VCVCompatible U] [Section5Nonempty pSpec]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (hResult : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        ((duplexSpongeChallengeOracle StmtIn U).Range q)) ∈ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sQueryStepRevised normal q))) : False := by
  cases q with
  | inl stmt =>
      simpa only [d2sQueryStepRevised_hash] using
        d2sHandleHashQueryRevised_no_underlyingAbort_of_support normal stmt gImpl hResult
  | inr q =>
      cases q with
      | inl stateIn =>
          simpa only [d2sQueryStepRevised_forward] using
            d2sHandleForwardPermQueryRevised_no_underlyingAbort_of_support normal stateIn
              gImpl hResult
      | inr stateOut =>
          simpa only [d2sQueryStepRevised_inverse] using
            d2sHandleInversePermQueryRevised_no_underlyingAbort_of_support normal stateOut
              gImpl hResult

/-- A finite live revised-D2S run from a reusable normal state can end only by normal completion
or a post-occurrence monitored stop.  The statement is deliberately at the actual absorbing
runner, not an abstract stream relation, so the H₀/H₁ coupling may use it when completing either
marginal after its first-stop time. -/
lemma d2sQueryRunRevised_no_underlyingAbort_of_support
    [VCVCompatible U] [Section5Nonempty pSpec] :
    ∀ (normal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (qs : List (duplexSpongeChallengeOracle StmtIn U).Domain)
      (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp),
      (.underlyingAbort : D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit) ∉ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sQueryRunRevised normal qs)) := by
  intro normal qs
  induction qs generalizing normal with
  | nil =>
      intro gImpl hResult
      rw [d2sQueryRunRevised_nil] at hResult
      have hEq : (.underlyingAbort : D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit) =
          .continue () normal := by
        simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
      cases hEq
  | cons q qs ih =>
      intro gImpl hResult
      rw [d2sQueryRunRevised_cons, simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨result, hStep, hResult⟩ := hResult
      cases result
      next answer normal' =>
          exact ih normal' gImpl hResult
      next normal' record =>
          have hEq : (.underlyingAbort : D2SRevisedStepResult
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit) =
              .stopped normal' record := by
            simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
          cases hEq
      next =>
          exact d2sQueryStepRevised_no_underlyingAbort_of_support normal q gImpl hStep

/-- The arbitrary ambient residual used by the H₀/H₁ coupling cannot terminate in an underlying
search failure.  This is the whole-program strengthening of the finite-stream result above:
ambient requests preserve the current normal state, and each right-summand request is discharged
by the live one-step no-abort theorem.  A monitor stop remains possible and deliberately remains
distinct from this result. -/
lemma hyb1AmbientDirectResidualRun_no_underlyingAbort_of_support
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Message i)]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [Section5Nonempty pSpec]
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (abortNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (.error (.underlyingAbort abortNormal) : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∉ support
      (KeyLemma.hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma residual normal) := by
  induction residual using OracleComp.inductionOn generalizing normal with
  | pure value =>
      intro hResult
      change (.error (.underlyingAbort abortNormal) : Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((Option StmtOut × D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∈ support
        (pure (.ok ((value, normal), PUnit.unit))) at hResult
      rw [mem_support_pure_iff] at hResult
      cases hResult
  | query_bind request continuation ih =>
      intro hResult
      cases request with
      | inl query =>
          rw [KeyLemma.hyb1AmbientDirectResidualRun_ambient] at hResult
          rw [mem_support_bind_iff] at hResult
          obtain ⟨answer, _hAnswer, hResult⟩ := hResult
          exact ih answer normal hResult
      | inr query =>
          rw [KeyLemma.hyb1AmbientDirectResidualRun_d2s] at hResult
          rw [mem_support_bind_iff] at hResult
          obtain ⟨result, hStep, hResult⟩ := hResult
          cases result with
          | «continue» answer normal' =>
              exact ih answer normal' hResult
          | stopped normal' record =>
              rw [mem_support_pure_iff] at hResult
              cases hResult
          | underlyingAbort =>
              exact d2sQueryStepRevised_no_underlyingAbort_of_support normal query
                ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma) hStep

/-- The fixed total `D_Σ` callback in the H₁ ambient residual cannot create a callback abort.
This is separate from a D2S parser/search abort: the residual runner invokes the total callback
only through `d2sQueryStepRevised`, whose three result constructors have no `oracleAbort` face. -/
lemma hyb1AmbientDirectResidualRun_no_oracleAbort_of_support
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [Section5Nonempty pSpec]
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal abortNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (.error (.oracleAbort abortNormal) : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∉ support
      (KeyLemma.hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma residual normal) := by
  induction residual using OracleComp.inductionOn generalizing normal with
  | pure value =>
      intro hResult
      change (.error (.oracleAbort abortNormal) : Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((Option StmtOut × D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∈ support
          (pure (.ok ((value, normal), PUnit.unit))) at hResult
      rw [mem_support_pure_iff] at hResult
      cases hResult
  | query_bind request continuation ih =>
      intro hResult
      cases request with
      | inl query =>
          rw [KeyLemma.hyb1AmbientDirectResidualRun_ambient] at hResult
          rw [mem_support_bind_iff] at hResult
          obtain ⟨answer, _hAnswer, hResult⟩ := hResult
          exact ih answer normal hResult
      | inr query =>
          rw [KeyLemma.hyb1AmbientDirectResidualRun_d2s] at hResult
          rw [mem_support_bind_iff] at hResult
          obtain ⟨result, hStep, hResult⟩ := hResult
          cases result with
          | «continue» answer normal' =>
              exact ih answer normal' hResult
          | stopped normal' record =>
              rw [mem_support_pure_iff] at hResult
              cases hResult
          | underlyingAbort =>
              rw [mem_support_pure_iff] at hResult
              cases hResult

/-- Any error reachable in the H₁ ambient residual is a monitored post-occurrence stop, rather
than a hidden parser/search error.  This is the exact error classification needed by the first
stop in Claim 5.21: the remaining error face is already the one charged by Lemma 5.8. -/
lemma hyb1AmbientDirectResidualRun_error_isMonitorStop_of_support
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [Section5Nonempty pSpec]
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp
      (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (reason : D2SRevisedStoppingReason
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : (.error reason : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∈ support
      (KeyLemma.hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma residual normal)) :
    KeyLemma.hyb1AmbientStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
      (α := ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit))
      (.error reason) := by
  cases reason with
  | monitorStop stoppedNormal record =>
      trivial
  | underlyingAbort abortNormal =>
      exact False.elim
        (hyb1AmbientDirectResidualRun_no_underlyingAbort_of_support
          (T_H := T_H) (T_P := T_P) oSpecImpl kSigma residual normal abortNormal hResult)
  | oracleAbort abortNormal =>
      exact False.elim
        (hyb1AmbientDirectResidualRun_no_oracleAbort_of_support
          (T_H := T_H) (T_P := T_P) oSpecImpl kSigma residual normal abortNormal hResult)

/-- The actual complete H₁ prover--verifier residual has no search-abort outcome.  This is the
specialization consumed by the H₀/H₁ coupling: it permits either marginal to finish after the
coupling stops without inventing a post-stop `D2SQuery` failure. -/
lemma hyb1AmbientFullResidualRun_no_underlyingAbort_of_support
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [Section5Nonempty pSpec]
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (normal abortNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (.error (.underlyingAbort abortNormal) : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∉ support
      (KeyLemma.hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma (KeyLemma.hyb1AmbientFullResidual V maliciousProver) normal) :=
  hyb1AmbientDirectResidualRun_no_underlyingAbort_of_support
    (T_H := T_H) (T_P := T_P) oSpecImpl kSigma
    (KeyLemma.hyb1AmbientFullResidual V maliciousProver) normal abortNormal

/-- The complete live Hyb₁ residual therefore has exactly one reachable error face: a
post-occurrence `Monitor` stop.  This specialization is the error-classification endpoint used
when the H₀/H₁ coupling completes the Hyb₁ marginal after its common first-stop time. -/
lemma hyb1AmbientFullResidualRun_error_isMonitorStop_of_support
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [Section5Nonempty pSpec]
    {ι : Type} {oSpec : OracleSpec ι} {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (reason : D2SRevisedStoppingReason
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : (.error reason : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∈ support
      (KeyLemma.hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma (KeyLemma.hyb1AmbientFullResidual V maliciousProver) normal)) :
    KeyLemma.hyb1AmbientStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
      (α := ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit))
      (.error reason) :=
  hyb1AmbientDirectResidualRun_error_isMonitorStop_of_support
    (T_H := T_H) (T_P := T_P) oSpecImpl kSigma
    (KeyLemma.hyb1AmbientFullResidual V maliciousProver) normal reason hResult

end DuplexSpongeFS.ProverTransform
