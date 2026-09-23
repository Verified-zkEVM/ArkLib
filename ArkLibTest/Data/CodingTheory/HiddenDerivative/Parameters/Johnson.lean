/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.InterpolationBounds
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.WeightedCertificate

/-!
# Concrete Johnson parameter acceptance cases

Small parameter sets exercise the finite bounds, interpolation surplus, and weighted certificate.
-/

namespace ReedSolomon.HiddenDerivative

private theorem rho_4_1 : johnsonRhoMinus 4 1 = 1 / 4 := by
  norm_num [johnsonRhoMinus]

private theorem sqrtRho_4_1 : √(johnsonRhoMinus 4 1) = 1 / 2 := by
  rw [rho_4_1, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem agreement_4_1 : johnsonAgreement 4 1 (1 / 4) = 3 / 4 := by
  rw [johnsonAgreement, sqrtRho_4_1]
  norm_num

private theorem multiplicity_4_1 : johnsonM 4 1 (1 / 4) = 3 := by
  rw [johnsonM, sqrtRho_4_1]
  norm_num

private theorem shiftedMultiplicity_4_1 : johnsonT 4 1 (1 / 4) = 7 / 2 := by
  rw [johnsonT, multiplicity_4_1]
  norm_num

private theorem candidateDegree_4_1 : johnsonMu 4 1 (1 / 4) = 6 := by
  rw [johnsonMu, shiftedMultiplicity_4_1, sqrtRho_4_1]
  norm_num

private theorem challengeHeight_4_1 : johnsonH 4 1 (1 / 4) = 16 := by
  have hceil : ⌈(7 / 2 : ℝ) ^ 2 / (3 * (1 / 4))⌉₊ = 17 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [johnsonH, shiftedMultiplicity_4_1, rho_4_1, hceil]

private theorem cutoff_4_1 : johnsonXCutoff 4 1 (1 / 4) = 7 := by
  rw [johnsonXCutoff, shiftedMultiplicity_4_1, sqrtRho_4_1]
  norm_num

private theorem threshold_4_1 : johnsonAgreement 4 1 (1 / 4) * (4 : ℕ) ≤ (3 : ℕ) := by
  rw [agreement_4_1]
  norm_num

/-- The finite bounds and threshold consequences at `n = 4`, `D = 1`, `η = 1/4`, `A = 3`. -/
example :
    (johnsonMu 4 1 (1 / 4) : ℝ) < 7 ∧ (johnsonH 4 1 (1 / 4) : ℝ) < 49 / 3 ∧
      1 ≤ johnsonMu 4 1 (1 / 4) ∧ 1 ≤ johnsonH 4 1 (1 / 4) ∧
      √(johnsonRhoMinus 4 1) / 2 ≤ johnsonM 4 1 (1 / 4) * (1 / 4) ∧
      1 + 1 ≤ 3 ∧ johnsonTheta 4 1 3 ≤ 3 ∧
      johnsonExceptionCount 4 1 3 (1 / 4) < 5488 / 3 ∧
      johnsonExceptionCount 4 1 3 (1 / 4) / johnsonComparisonEstimate 4 1 (1 / 4) < 16 / 49 ∧
      johnsonExceptionCount 4 1 3 (1 / 4) < johnsonComparisonEstimate 4 1 (1 / 4) := by
  have hD : 1 ≤ (1 : ℕ) := le_rfl
  have hDn : (1 : ℕ) ≤ 4 - 2 := by omega
  have heta : (0 : ℝ) < 1 / 4 := by norm_num
  have ha : johnsonAgreement 4 1 (1 / 4) ≤ 1 := by rw [agreement_4_1]; norm_num
  have hmu := johnsonMu_lt (n := 4) (D := 1) (eta := 1 / 4) hD (by norm_num)
  have hheight := johnsonH_lt (n := 4) (D := 1) (eta := 1 / 4) hD (by norm_num)
  have hgap := johnson_half_gap 4 1 (eta := 1 / 4) heta
  have hdegree := johnson_degree_succ_le_agreement (n := 4) (D := 1) (A := 3)
    (by norm_num) (by norm_num) heta threshold_4_1
  have htheta := johnsonTheta_le_sqrt_envelope (n := 4) (D := 1) (A := 3)
    (by norm_num) (by norm_num) heta threshold_4_1
  have hclosed := johnsonExceptionCount_lt_closed (n := 4) (D := 1) (A := 3)
    hD hDn heta threshold_4_1
  have hratio := johnsonExceptionCount_div_comparisonEstimate_lt hD hDn heta ha threshold_4_1
  have hcomparison := johnsonExceptionCount_lt_comparisonEstimate hD hDn heta ha threshold_4_1
  rw [shiftedMultiplicity_4_1, sqrtRho_4_1] at hmu
  rw [shiftedMultiplicity_4_1, rho_4_1] at hheight
  refine ⟨?_, ?_, ?_, ?_, hgap, hdegree, ?_, ?_, hratio, hcomparison⟩
  · rw [candidateDegree_4_1]
    norm_num at hmu ⊢
  · rw [challengeHeight_4_1]
    norm_num at hheight ⊢
  · simpa [candidateDegree_4_1] using johnsonMu_pos (n := 4) (D := 1) hD (by norm_num)
  · simpa [challengeHeight_4_1] using johnsonH_pos (n := 4) (D := 1) hD (by norm_num)
  · calc
      johnsonTheta 4 1 3 ≤
          (1 + √(johnsonRhoMinus 4 1)) / √(johnsonRhoMinus 4 1) := htheta
      _ ≤ 3 := by rw [sqrtRho_4_1]; norm_num
  · calc
      johnsonExceptionCount 4 1 3 (1 / 4) <
          (8 / 3 : ℝ) * 4 * johnsonT 4 1 (1 / 4) ^ 3 / johnsonRhoMinus 4 1 := hclosed
      _ = 5488 / 3 := by
        rw [shiftedMultiplicity_4_1, rho_4_1]
        norm_num

/-- The interpolation ceilings and slot surplus at the same small parameter set. -/
example :
    johnsonMu 4 1 (1 / 4) + 1 = 7 ∧ johnsonH 4 1 (1 / 4) + 1 = 17 ∧
      johnsonMu 4 1 (1 / 4) ≤ johnsonH 4 1 (1 / 4) ∧
      johnsonM 4 1 (1 / 4) ≤ johnsonH 4 1 (1 / 4) + 1 ∧
      1 * johnsonMu 4 1 (1 / 4) < johnsonXCutoff 4 1 (1 / 4) ∧
      johnsonXCutoff 4 1 (1 / 4) ≤ johnsonM 4 1 (1 / 4) * 3 ∧
      johnsonRowSlotCount 4 3 16 < johnsonSourceSlotCount 7 1 6 16 := by
  have hD : 1 ≤ (1 : ℕ) := le_rfl
  have hDn : (1 : ℕ) < 4 := by norm_num
  have heta : (0 : ℝ) < 1 / 4 := by norm_num
  have hthreshold := threshold_4_1
  have hmuAdd := johnsonMu_add_one (n := 4) (D := 1) (eta := 1 / 4) hD hDn
  have hheightAdd := johnsonH_add_one (n := 4) (D := 1) (eta := 1 / 4) hD hDn
  have hmuH := johnsonMu_le_H (n := 4) (D := 1) (eta := 1 / 4) hD hDn
  have hMHeight := johnsonM_le_H_add_one (n := 4) (D := 1) (eta := 1 / 4) hD hDn
  have hcutoff := johnson_D_mul_mu_lt_XCutoff (n := 4) (D := 1) (eta := 1 / 4) hD hDn
  have hbudget := johnsonXCutoff_le_mul_agreement (n := 4) (D := 1) (A := 3) heta hthreshold
  have hsurplus := johnson_interpolation_slot_surplus (n := 4) (D := 1) (eta := 1 / 4) hD hDn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      johnsonMu 4 1 (1 / 4) + 1 =
          ⌈johnsonT 4 1 (1 / 4) / √(johnsonRhoMinus 4 1)⌉₊ := hmuAdd
      _ = 7 := by rw [shiftedMultiplicity_4_1, sqrtRho_4_1]; norm_num
  · calc
      johnsonH 4 1 (1 / 4) + 1 =
          ⌈johnsonT 4 1 (1 / 4) ^ 2 / (3 * johnsonRhoMinus 4 1)⌉₊ := hheightAdd
      _ = 17 := by
        rw [shiftedMultiplicity_4_1, rho_4_1]
        rw [Nat.ceil_eq_iff (by norm_num)]
        norm_num
  · simpa [candidateDegree_4_1, challengeHeight_4_1] using hmuH
  · simpa [multiplicity_4_1, challengeHeight_4_1] using hMHeight
  · simpa [candidateDegree_4_1, cutoff_4_1] using hcutoff
  · simpa [multiplicity_4_1, cutoff_4_1] using hbudget
  · rw [multiplicity_4_1, candidateDegree_4_1, challengeHeight_4_1, cutoff_4_1] at hsurplus
    exact hsurplus

/-- A negative weighted moment still yields a valid certificate and strict slot surplus. -/
example :
    johnsonWeightedMoment 2 5 3 2 1 = -1 ∧ johnsonWeightedHeight 2 5 3 2 1 = 1 ∧
      johnsonWeightedSourceSlots 5 3 2 1 1 + johnsonWeightedW 5 3 2 1 =
        2 * johnsonWeightedN 5 3 2 1 ∧
      johnsonWeightedRowSlots 2 2 1 1 + 2 * johnsonWeightedT 2 1 =
        2 * 2 * johnsonWeightedR 2 1 ∧
      johnsonWeightedRowSlots 2 2 1 1 < johnsonWeightedSourceSlots 5 3 2 1 1 ∧
      johnsonWeightedMoment 2 5 3 2 1 <
        ((1 + 1 : ℕ) : ℤ) * johnsonWeightedSlope 2 5 3 2 1 := by
  have hcert : IsJohnsonWeightedCertificate 2 5 3 2 1 1 :=
    ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩
  exact ⟨by decide, by decide, johnsonWeightedSourceSlots_add_W le_rfl,
    johnsonWeightedRowSlots_add_nT (by decide), hcert.rowSlots_lt_sourceSlots,
    hcert.strict_scalar_surplus⟩

/-- At positive moment and slope, the selected Johnson height bounds both quantities. -/
example :
    1 ≤ johnsonWeightedHeight 3 1 3 2 1 ∧
    johnsonWeightedMoment 3 1 3 2 1 <
      ((johnsonWeightedHeight 3 1 3 2 1 + 1 : ℕ) : ℤ) * johnsonWeightedSlope 3 1 3 2 1 := by
  have hslope : 3 * johnsonWeightedR 2 1 < johnsonWeightedN 1 3 2 1 := by decide
  exact ⟨johnsonWeightedHeight_ge 3 1 3 2 1,
    johnsonWeightedHeight_strict hslope⟩

end ReedSolomon.HiddenDerivative
