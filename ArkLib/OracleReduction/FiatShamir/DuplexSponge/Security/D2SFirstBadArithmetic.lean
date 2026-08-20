/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.Bounds
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadAdaptive
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Section5Nonempty
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Core

/-!
# Arithmetic bridge for the revised stopped first-bad bound

The revised Section 5 uses the exact stopped-run charge `Ccap U T v` while a completed verifier
extension is uniformly bounded by `Dcap U T nV`.  This file isolates the paper's elementary
monotonicity calculation, including its necessary `(T,nV) = (0,0)` exception, so Claim 5.24 and
the stopped part of Lemma 5.8 need not repeat arithmetic.
-/

namespace DuplexSpongeFS.Statement

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal
open DuplexSpongeFS.ProverTransform DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U] [Nonempty U] [SampleableType U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

omit [VCVCompatible U] [DecidableEq U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- The legacy ideal-permutation spelling of the Lemma-5.8 birthday bound is exactly the
stateful paper spelling `B(T + 1 + N_𝒱)`, once `T = tₕ + tₚ + tₚ⁻¹`.  This is an equality, not
an inequality or a rounded-budget relaxation, and is the arithmetic seam at which the ideal and
revised-D2S first-bad proofs meet. -/
lemma legacyLemma58Bound_eq_badEventBound
    [Fintype U]
    (tₕ tₚ tₚᵢ nV : ℕ) :
    BadEventDS.lemma5_8Bound U tₕ tₚ tₚᵢ nV =
      badEventBound U (tₕ + tₚ + tₚᵢ + 1 + nV) := by
  simp only [BadEventDS.lemma5_8Bound, badEventBound, capacitySize]
  push_cast
  ring

omit [VCVCompatible U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- The same exact adaptive charge is bounded by the stopped-extension numerator `C(T,v)` once
the verifier has at least one forward permutation call.  This is where the revised Section 5
nonempty-round convention is used: the adaptive fuel is `v + 1` because the verifier also makes
its initial hash query. -/
lemma adaptiveVerifierCharge_le_CcapNumerator (T v : ℕ) (hv : 1 ≤ v) :
    2 * (v + 1) * (2 * T + (v + 1)) ≤
      (6 * v + 4) * T + 3 * v ^ 2 + 5 * v := by
  nlinarith [sq_nonneg (v : ℝ)]

/-- CO25 eqs. (28)--(29): in the nonexceptional case, the exact stopped-run charge at any
`v ≤ nV` is bounded by its uniform `N_𝒱` envelope.  No protocol or oracle premise is used.

For `nV > 0`, the difference after first replacing `v` by `nV` is the sum of the nonnegative
terms `(8 nV + 10) T` and `(nV - 1) (4 nV + 3)`.  For `nV = 0`, nonexceptionality forces
`T > 0`, and necessarily `v = 0`. -/
lemma Ccap_le_Dcap {U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    (T v nV : ℕ) (hv : v ≤ nV) (hne : ¬ ExceptionalEmpty T nV) :
    Ccap U T v ≤ Dcap U T nV := by
  have hden : 0 < 2 * capacitySize U := by
    have hcap : 0 < capacitySize U := by
      unfold capacitySize
      positivity
    positivity
  apply (div_le_div_iff_of_pos_right hden).mpr
  have hT : 0 ≤ (T : ℝ) := by positivity
  have hvR : 0 ≤ (v : ℝ) := by positivity
  have hvn : (v : ℝ) ≤ (nV : ℝ) := by exact_mod_cast hv
  have hTv : (v : ℝ) * (T : ℝ) ≤ (nV : ℝ) * (T : ℝ) :=
    mul_le_mul_of_nonneg_right hvn hT
  have hsq : (v : ℝ) ^ 2 ≤ (nV : ℝ) ^ 2 := by
    nlinarith
  rcases Nat.eq_zero_or_pos nV with rfl | hnV
  · have hTpos : 0 < T := Nat.pos_of_ne_zero (by
      intro hTzero
      apply hne
      exact ⟨hTzero, rfl⟩)
    norm_num at hv
    subst v
    norm_num
    have hTR : 1 ≤ (T : ℝ) := by exact_mod_cast hTpos
    nlinarith
  · have hnVR : 1 ≤ (nV : ℝ) := by exact_mod_cast hnV
    have hsucc : ((nV + 1 : ℕ) : ℝ) = (nV : ℝ) + 1 := by norm_num
    rw [hsucc]
    have hCmax :
        (6 * (v : ℝ) + 4) * (T : ℝ) + 3 * (v : ℝ) ^ 2 + 5 * (v : ℝ) ≤
          (6 * (nV : ℝ) + 4) * (T : ℝ) + 3 * (nV : ℝ) ^ 2 + 5 * (nV : ℝ) := by
      nlinarith
    have hquad : 0 ≤ ((nV : ℝ) - 1) * (4 * (nV : ℝ) + 3) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith

/-- The stopped-verifier envelope is already covered by the one global Lemma-5.8 budget at the
end of its verifier segment.  Writing `n = N_𝒱 + 1`, the numerator difference is
`7 T² - 3 T + 7 n`, which is nonnegative for natural `T` and `n ≥ 1`.  This is an algebraic
bridge only: it neither rounds the exact verifier count nor adds a protocol-side hypothesis. -/
lemma Dcap_le_badEventBound {U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]
    (T nV : ℕ) :
    Dcap U T nV ≤ badEventBound U (T + nV + 1) := by
  have hden : 0 < 2 * capacitySize U := by
    have hcap : 0 < capacitySize U := by
      unfold capacitySize
      positivity
    positivity
  unfold Dcap badEventBound
  dsimp only
  apply (div_le_div_iff_of_pos_right hden).mpr
  have hT : 0 ≤ (T : ℝ) := by positivity
  have hn : 1 ≤ ((nV + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le nV)
  push_cast
  nlinarith [sq_nonneg (T : ℝ)]

/-! ## Connecting the executable adaptive charge to paper equation (28) -/

variable {U : Type} [Fintype U] [SpongeUnit U] [SpongeSize]

/-- The adaptive revised-D2S first-stop charge is bounded by the paper's preserved
`B(j + fuel)` expression.  The runner begins with at most `j` already realized base entries
and can reach at most `fuel` further entries; its exact charge is
`fuel (2j + fuel) / Q`.  This elementary bridge is the direct-D2S half of Lemma 5.8a: it keeps
the adaptive execution bound in its useful sharp form while exposing precisely the paper's
common `B` envelope to subsequent hybrid arguments. -/
lemma adaptiveD2SCharge_div_le_badEventBoundENN (j fuel : ℕ) :
    ((fuel * (2 * j + fuel) : ℕ) : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) ≤
      ENNReal.ofReal (badEventBound U (j + fuel)) := by
  have hQpos : 0 < capacitySize U := by
    unfold capacitySize
    positivity
  have hj : 0 ≤ (j : ℝ) := by positivity
  have hfuel : 0 ≤ (fuel : ℝ) := by positivity
  have hjterm : 0 ≤ (j : ℝ) * (7 * (j : ℝ) - 3) := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · norm_num
    · apply mul_nonneg hj
      have hjone : 1 ≤ (j : ℝ) := by exact_mod_cast hjpos
      linarith
  have hfuelterm : 0 ≤ (fuel : ℝ) *
      (10 * (j : ℝ) + 5 * (fuel : ℝ) - 3) := by
    rcases Nat.eq_zero_or_pos fuel with rfl | hfuelpos
    · norm_num
    · apply mul_nonneg hfuel
      have hfuelone : 1 ≤ (fuel : ℝ) := by exact_mod_cast hfuelpos
      linarith
  have hnumerator :
      2 * ((fuel * (2 * j + fuel) : ℕ) : ℝ) ≤
        7 * ((j + fuel : ℕ) : ℝ) ^ 2 - 3 * ((j + fuel : ℕ) : ℝ) := by
    push_cast
    nlinarith [hjterm, hfuelterm]
  have hreal :
      ((fuel * (2 * j + fuel) : ℕ) : ℝ) / capacitySize U ≤
        badEventBound U (j + fuel) := by
    rw [badEventBound]
    field_simp
    nlinarith
  have hQ : BadEventDS.capacitySpaceSize (U := U) = ENNReal.ofReal (capacitySize U) := by
    simp only [BadEventDS.capacitySpaceSize, capacitySize]
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  rw [hQ]
  have hcast :
      ((fuel * (2 * j + fuel) : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal (((fuel * (2 * j + fuel) : ℕ) : ℝ)) := by
    norm_cast
  rw [hcast, ← ENNReal.ofReal_div_of_pos hQpos]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The raw adaptive-run numerator for the complete verifier is at most the numerator of the
paper's stopped bound `C(T,N_𝒱)`.  The left side has `N_𝒱 + 1` requests because it includes
the initial `DS.Start` hash; this is precisely why the factor `2` appears before it. -/
lemma adaptiveVerifierCharge_div_le_CcapENN (T nV : ℕ) (hnV : 1 ≤ nV) :
    (((nV + 1) * (2 * T + (nV + 1)) : ℕ) : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) ≤
      ENNReal.ofReal (Ccap U T nV) := by
  have hcharge := adaptiveVerifierCharge_le_CcapNumerator T nV hnV
  have hchargeR :
      2 * (((nV + 1) * (2 * T + (nV + 1)) : ℕ) : ℝ) ≤
        (((6 * nV + 4) * T + 3 * nV ^ 2 + 5 * nV : ℕ) : ℝ) := by
    exact_mod_cast (show
      2 * ((nV + 1) * (2 * T + (nV + 1))) ≤
        (6 * nV + 4) * T + 3 * nV ^ 2 + 5 * nV by
      simpa [Nat.mul_assoc] using hcharge)
  push_cast at hchargeR
  have hQpos : 0 < capacitySize U := by
    unfold capacitySize
    positivity
  have hreal :
      (((nV + 1) * (2 * T + (nV + 1)) : ℕ) : ℝ) / capacitySize U ≤ Ccap U T nV := by
    rw [Ccap]
    push_cast
    field_simp
    nlinarith
  have hQ : BadEventDS.capacitySpaceSize (U := U) = ENNReal.ofReal (capacitySize U) := by
    simp only [BadEventDS.capacitySpaceSize, capacitySize]
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  rw [hQ]
  have hcast :
      (((nV + 1) * (2 * T + (nV + 1)) : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal (((nV + 1) * (2 * T + (nV + 1)) : ℕ) : ℝ) := by
    norm_cast
  rw [hcast]
  rw [← ENNReal.ofReal_div_of_pos hQpos]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The pure-`Hyb₁` verifier runner obeys paper equation (28) with the exact stateful count.
The only later use of this theorem must additionally prove that the live observed verifier
execution is this runner; no rounded query budget occurs in this statement. -/
lemma hyb1PureVerifierAdaptiveRun_monitorStop_le_Ccap {StmtOut StmtIn : Type}
    {n : ℕ} {pSpec : ProtocolSpec n} {δ : ℕ}
    [VCVCompatible U] [codec : CodecCore pSpec U]
    [DecidableEq StmtIn] [DecidableEq U] [Nonempty U] [SampleableType U]
    {T_H T_P : Type}
    [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [VCVCompatible StmtIn] [Section5Nonempty pSpec]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (normal : ProverTransform.D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (T : ℕ) (hCoherent : ProverTransform.RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ T) :
    Pr[ fun result => result.isMonitorStop |
      ProverTransform.hyb1PureVerifierAdaptiveRun
        (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof
        (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal] ≤
      ENNReal.ofReal (Ccap U T (verifierPermCallCount (pSpec := pSpec) (δ := δ))) := by
  calc
    Pr[ fun result => result.isMonitorStop |
        ProverTransform.hyb1PureVerifierAdaptiveRun
          (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof
          (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal] ≤
        (((verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) *
            (2 * T + (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)) : ℕ) : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) :=
      ProverTransform.hyb1PureVerifierAdaptiveRun_at_verifierPermCallCount_succ_monitorStop_le
        (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof normal T hCoherent hBaseLength
    _ ≤ ENNReal.ofReal (Ccap U T (verifierPermCallCount (pSpec := pSpec) (δ := δ))) :=
      adaptiveVerifierCharge_div_le_CcapENN T
        (verifierPermCallCount (pSpec := pSpec) (δ := δ))
        (Nat.succ_le_iff.mpr (Section5Nonempty.verifierPermCallCount_pos
          (pSpec := pSpec) (δ := δ)))

/-- The stopped pure-`Hyb₁` verifier segment satisfies the final paper envelope
`D(T,N_𝒱)`.  This composes the executable first-bad runner with equations (28)--(29), using
only the explicit nonempty-round scope to rule out the paper's `(T,N_𝒱)=(0,0)` exception. -/
lemma hyb1PureVerifierAdaptiveRun_monitorStop_le_Dcap {StmtOut StmtIn : Type}
    {n : ℕ} {pSpec : ProtocolSpec n} {δ : ℕ}
    [VCVCompatible U] [codec : CodecCore pSpec U]
    [DecidableEq StmtIn] [DecidableEq U] [Nonempty U] [SampleableType U]
    {T_H T_P : Type}
    [DSTraceStorage.LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [VCVCompatible StmtIn] [Section5Nonempty pSpec]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (normal : ProverTransform.D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (T : ℕ) (hCoherent : ProverTransform.RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ T) :
    Pr[ fun result => result.isMonitorStop |
      ProverTransform.hyb1PureVerifierAdaptiveRun
        (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof
        (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal] ≤
      ENNReal.ofReal (Dcap U T (verifierPermCallCount (pSpec := pSpec) (δ := δ))) := by
  let nV := verifierPermCallCount (pSpec := pSpec) (δ := δ)
  have hnV : 0 < nV := Section5Nonempty.verifierPermCallCount_pos
    (pSpec := pSpec) (δ := δ)
  have hCcap : Ccap U T nV ≤ Dcap U T nV :=
    Ccap_le_Dcap (U := U) T nV nV (le_refl nV) (by
      intro hEmpty
      exact (Nat.ne_of_gt hnV) hEmpty.2)
  exact (hyb1PureVerifierAdaptiveRun_monitorStop_le_Ccap
    (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof normal T hCoherent hBaseLength).trans
      (ENNReal.ofReal_le_ofReal hCcap)

end DuplexSpongeFS.Statement
