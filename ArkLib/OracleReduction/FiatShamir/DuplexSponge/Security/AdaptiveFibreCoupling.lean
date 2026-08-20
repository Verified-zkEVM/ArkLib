/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.DecodedFibreCoupling
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadAdaptive

/-!
# Adaptive decoded-fibre coupling

This module lifts the fixed-table D2S action coupling to the actual stateful,
response-adaptive revised D2S runner.  It is the proof kernel for the H₂-to-fibre
part of Claim 5.22: the controller may choose its next request from the complete
prior normal state and cache, while a repeated encoded key still reuses precisely
the representative sampled on its first visit.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  /- These fixed-table operators are still the legacy total-fibre implementation.
  The paper-faithful partial codec route is developed separately at the one-cell bridge
  boundary; do not advertise this module as `CodecCore` until its two kernels are replaced. -/
  [codec : Codec pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [Nonempty U] [SampleableType U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

local instance : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain := Classical.decEq _

/-- The fixed-table H₂ decoded bridge as one state-threaded adaptive D2S step.
The controller state is exactly the encoded-key cache; no second memo structure is introduced. -/
noncomputable def decodedBridgeAdaptiveKernel
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (gSpec (U := U) StmtIn pSpec δ).QueryCache where
  step cache normal q :=
    (fun resultAndCache =>
      D2SAdaptiveStepResult.ofRevised resultAndCache.2 resultAndCache.1) <$>
      (simulateQ
        (decodedBridgeD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        (d2sQueryStepRevised normal q)).run cache

/-- The companion adaptive step which samples a representative from the same fixed decoder
fibre on a cache miss and otherwise returns the cached representative. -/
noncomputable def decodedFibreAdaptiveKernel
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (gSpec (U := U) StmtIn pSpec δ).QueryCache where
  step cache normal q :=
    (fun resultAndCache =>
      D2SAdaptiveStepResult.ofRevised resultAndCache.2 resultAndCache.1) <$>
      (simulateQ
        (decodedFibreD2SImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table)
        (d2sQueryStepRevised normal q)).run cache

/-- A pointwise adaptive step has identical output, normal-state, and cache distribution under
the fixed-table decoded bridge and its uniform-fibre realization. -/
theorem evalDist_decodedBridgeAdaptiveKernel_step_eq_decodedFibreAdaptiveKernel
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    𝒟[(decodedBridgeAdaptiveKernel (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) table).step cache normal q] =
      𝒟[(decodedFibreAdaptiveKernel (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (T_H := T_H) (T_P := T_P) table).step cache normal q] := by
  exact evalDist_map_eq_of_evalDist_eq
    (evalDist_simulateQ_decodedBridgeD2SImpl_eq_decodedFibreD2SImpl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) table
      (d2sQueryStepRevised normal q) cache)
    (fun resultAndCache =>
      D2SAdaptiveStepResult.ofRevised resultAndCache.2 resultAndCache.1)

/-- A state-threaded adaptive D2S runner preserves exact distributions under pointwise equality
of its step kernel.  The proof is a fuel induction: after an equal distributed step result, the
dependent controller continuation is literally the same on both sides. -/
theorem evalDist_d2sQueryRunRevisedAdaptiveWithStep_eq_of_step_eq
    {S : Type}
    (kernel₁ kernel₂ : D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    (hstep : ∀ (state : S)
      (normal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain),
      𝒟[kernel₁.step state normal q] = 𝒟[kernel₂.step state normal q])
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    (fuel : ℕ) (controlState : S)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    𝒟[d2sQueryRunRevisedAdaptiveWithStep kernel₁ control fuel controlState normal] =
      𝒟[d2sQueryRunRevisedAdaptiveWithStep kernel₂ control fuel controlState normal] := by
  induction fuel generalizing controlState normal with
  | zero =>
      cases hnext : control.next controlState normal <;>
        simp [d2sQueryRunRevisedAdaptiveWithStep, hnext]
  | succ fuel ih =>
      cases hnext : control.next controlState normal with
      | done => simp [d2sQueryRunRevisedAdaptiveWithStep, hnext]
      | query q advance =>
          simp only [d2sQueryRunRevisedAdaptiveWithStep, hnext, evalDist_bind]
          rw [hstep]
          apply bind_congr
          intro result
          cases result with
          | «continue» answer state' normal' =>
              exact ih (advance state' answer normal') normal'
          | stopped normal' record => rfl
          | underlyingAbort => rfl

/-- **Adaptive fixed-table Claim 5.22.**  The full response-adaptive revised D2S execution has
the same distribution under the H₂ decoded bridge and uniform-fibre sampling.  This covers
arbitrary repeated keys, rate-cache state, and every branch selected by the evolving normal
state; it carries no bad-event charge and loses no query factor. -/
theorem evalDist_decodedBridgeAdaptiveRun_eq_decodedFibreAdaptiveRun
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (fuel : ℕ) (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    𝒟[d2sQueryRunRevisedAdaptiveWithStep
      (decodedBridgeAdaptiveKernel (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (T_H := T_H) (T_P := T_P) table)
      control fuel cache normal] =
      𝒟[d2sQueryRunRevisedAdaptiveWithStep
        (decodedFibreAdaptiveKernel (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          (T_H := T_H) (T_P := T_P) table)
        control fuel cache normal] := by
  apply evalDist_d2sQueryRunRevisedAdaptiveWithStep_eq_of_step_eq
  exact fun state normal q =>
    evalDist_decodedBridgeAdaptiveKernel_step_eq_decodedFibreAdaptiveKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      table state normal q

end DuplexSpongeFS.ProverTransform
