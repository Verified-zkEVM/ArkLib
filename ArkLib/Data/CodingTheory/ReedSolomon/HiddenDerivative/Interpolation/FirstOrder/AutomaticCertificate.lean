/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.AutomaticRecipe

/-!
# Symbolic interpolation certificate from the automatic first-order recipe

This file identifies the literal automatic parameters with the generic finite-rate interface and
constructs its strict-support symbolic certificate over an arbitrary field. Characteristic and
root-reconstruction hypotheses belong to the later hybrid transfer.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

noncomputable section

set_option autoImplicit false

/-- The two files use the same clean first-order threshold formula. -/
theorem automaticFirstOrderThreshold_eq_firstOrderRateThreshold (rho : ℝ) :
    automaticFirstOrderThreshold rho = firstOrderRateThreshold rho := rfl

/-- The automatic derivative ratio is the generic rate ratio at the capped agreement `a₀`. -/
theorem automaticBeta_eq_firstOrderRateBeta (rho a : ℝ) :
    automaticBeta rho a = firstOrderRateBeta rho (automaticAgreement rho a) := rfl

/-- The raw automatic derivative cap is exactly the generic finite-rate derivative cap. -/
theorem automaticDerivativeCapRaw_eq_firstOrderRateDerivativeCap (rho a : ℝ) :
    automaticDerivativeCapRaw rho a =
      firstOrderRateDerivativeCap rho (automaticAgreement rho a)
        (automaticMultiplicity rho a) := by
  unfold automaticDerivativeCapRaw firstOrderRateDerivativeCap
  rw [automaticBeta_eq_firstOrderRateBeta]

/-- The automatic total jet degree is exactly the generic finite-rate jet degree. -/
theorem automaticJetDegree_eq_firstOrderRateJetDegree (rho a : ℝ) :
    automaticJetDegree rho a =
      firstOrderRateJetDegree rho (automaticAgreement rho a)
        (automaticMultiplicity rho a) := rfl

/-- The literal automatic source count is the generic rate source count at `a₀`. -/
theorem automaticSourceCount_eq_firstOrderRateSourceCount
    {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticSourceCount rho a =
      firstOrderRateSourceCount rho (automaticAgreement rho a)
        (automaticMultiplicity rho a) (automaticDerivativeCapRaw rho a)
        (automaticJetDegree rho a) := by
  rw [automaticSourceCount_eq_raw hrho hrhoOne ha haOne]
  rfl

/-- The literal automatic local rank is the generic all-`M` finite-rate rank. -/
theorem automaticRankCount_eq_firstOrderRateRankCount
    {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticRankCount rho a =
      firstOrderRateRankCount (automaticMultiplicity rho a)
        (automaticDerivativeCapRaw rho a) := by
  rw [automaticRankCount_eq_raw hrho hrhoOne ha haOne]
  rfl

/-- The literal automatic height is the generic rate challenge degree at the capped agreement. -/
theorem automaticChallengeHeight_eq_firstOrderRateChallengeDegree
    {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticChallengeHeight rho a =
      firstOrderRateChallengeDegree rho (automaticAgreement rho a)
        (automaticMultiplicity rho a) := by
  unfold automaticChallengeHeight firstOrderRateChallengeDegree
  rw [← automaticDerivativeCapRaw_eq_firstOrderRateDerivativeCap]
  rw [← automaticRankCount_eq_firstOrderRateRankCount hrho hrhoOne ha haOne]
  rw [← automaticJetDegree_eq_firstOrderRateJetDegree]
  rw [← automaticSourceCount_eq_firstOrderRateSourceCount hrho hrhoOne ha haOne]

/-- The explicit recipe supplies a checked generic finite-rate parameter record. -/
def automaticFirstOrderFiniteRateParameters
    {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    FirstOrderFiniteRateParameters rho (automaticAgreement rho a) where
  multiplicity := automaticMultiplicity rho a
  multiplicity_pos := automaticMultiplicity_pos hrho hrhoOne ha haOne
  surplus := by
    unfold FirstOrderFiniteRateTest
    rw [← automaticDerivativeCapRaw_eq_firstOrderRateDerivativeCap]
    rw [← automaticRankCount_eq_firstOrderRateRankCount hrho hrhoOne ha haOne]
    rw [← automaticJetDegree_eq_firstOrderRateJetDegree]
    rw [← automaticSourceCount_eq_firstOrderRateSourceCount hrho hrhoOne ha haOne]
    exact automaticRankCount_lt_sourceCount hrho hrhoOne ha haOne

/-- Every public finite-code source count dominates the automatic real source lower count. -/
theorem automaticSourceCount_le_dimensionCount
    {rho a : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hD : (D : ℝ) ≤ rho * n) (hA : a * n ≤ A) :
    n * automaticSourceCount rho a ≤
      firstOrderDimensionCount D A (automaticMultiplicity rho a)
        (automaticDerivativeCap rho a) (automaticJetDegree rho a) := by
  have ha₀A := automaticAgreement_mul_le_count (rho := rho) hA
  have hlower := firstOrderRateSourceCount_le_dimensionCount
    (R := rho) (a := automaticAgreement rho a) (n := n) (D := D) (A := A)
    (m := automaticMultiplicity rho a) (M := automaticDerivativeCapRaw rho a)
    (mu := automaticJetDegree rho a) hD ha₀A
  rw [← automaticSourceCount_eq_firstOrderRateSourceCount hrho hrhoOne ha haOne] at hlower
  rw [automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]
  exact hlower

/-- The automatic rank budget is exactly the generic certified first-order local rank. -/
theorem certifiedEnlargedRankBound_one_eq_automaticRankCount
    {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    certifiedEnlargedRankBound 1 (automaticMultiplicity rho a)
        (automaticDerivativeCap rho a) 0 = automaticRankCount rho a := by
  rw [certifiedEnlargedRankBound_one_eq_firstOrderRateRankCount]
  rw [automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]
  exact (automaticRankCount_eq_firstOrderRateRankCount hrho hrhoOne ha haOne).symm

/-- The automatic recipe constructs a complete strict-support symbolic certificate over any
field. All parameters are fixed before the block length, field, centers, or received words. -/
theorem exists_automaticFirstOrder_symbolicCertificate
    {F : Type*} [Field F] {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A)
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (FirstOrderSymbolicCertificate (F := F)
      D A (automaticMultiplicity rho a) (automaticDerivativeCap rho a)
      (automaticJetDegree rho a) k (automaticChallengeHeight rho a) centers f g
      (firstOrderColumns (D := D) (A := A) (m := automaticMultiplicity rho a)
        (M := automaticDerivativeCap rho a) (μ := automaticJetDegree rho a))) := by
  let p := automaticFirstOrderFiniteRateParameters hrho hrhoOne ha haOne
  have hDpos : 0 < D := by omega
  have hApos : 0 < A := by
    have hrhoA := rho_lt_automaticAgreement hrho hrhoOne ha
    have ha₀pos : 0 < automaticAgreement rho a := hrho.trans hrhoA
    have ha₀A := automaticAgreement_mul_le_count (rho := rho) hA
    have hnReal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have : (0 : ℝ) < A := lt_of_lt_of_le (mul_pos ha₀pos hnReal) ha₀A
    exact_mod_cast this
  have hbudget : 0 < automaticMultiplicity rho a * A :=
    Nat.mul_pos (automaticMultiplicity_pos hrho hrhoOne ha haOne) hApos
  have hkD : k ≤ D + 1 := by omega
  have hDrate : (D : ℝ) ≤ rho * n := automatic_degree_le_rate_mul hD hkRate
  have hArate : automaticAgreement rho a * n ≤ A :=
    automaticAgreement_mul_le_count (rho := rho) hA
  have hcert := exists_firstOrderRate_symbolicCertificate p hn hDpos hbudget hkD
    hDrate hArate centers f g
  have hM : automaticDerivativeCap rho a = p.derivativeCap := by
    simp [p, automaticFirstOrderFiniteRateParameters,
      FirstOrderFiniteRateParameters.derivativeCap,
      automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne,
      automaticDerivativeCapRaw_eq_firstOrderRateDerivativeCap]
  have hmu : automaticJetDegree rho a = p.jetDegree := by
    simp [p, automaticFirstOrderFiniteRateParameters,
      FirstOrderFiniteRateParameters.jetDegree,
      automaticJetDegree_eq_firstOrderRateJetDegree]
  have hh : automaticChallengeHeight rho a = p.challengeDegree := by
    simp [p, automaticFirstOrderFiniteRateParameters,
      FirstOrderFiniteRateParameters.challengeDegree,
      automaticChallengeHeight_eq_firstOrderRateChallengeDegree hrho hrhoOne ha haOne]
  rw [hM, hmu, hh]
  exact hcert

end

end ReedSolomon.HiddenDerivative
