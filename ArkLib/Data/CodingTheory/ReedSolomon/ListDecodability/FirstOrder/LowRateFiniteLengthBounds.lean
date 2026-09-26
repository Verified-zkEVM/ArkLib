/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.LowRateFiniteLength
public import ArkLib.ToMathlib.Algebra.Order.Floor.Ratio

/-!
# Rate-only bounds for low-rate finite-length selectors

This module gives inverse-slack bounds for the multiplicity, derivative cap, jet degree, and
challenge height selected by the low-rate finite-length construction. The estimates use
rate-dependent constants and share one parameter bound.

## Main statements

* `lowRateFiniteLengthSlack_lt_one_of_one_le_rate_mul_length` bounds slack at positive length.
* `lowRateFiniteLengthMultiplicity_le_inv_slack` bounds the multiplicity by inverse slack.
* `lowRateFiniteLengthJetDegree_le_inv_slack` bounds the total jet degree by inverse slack.
* `lowRateFiniteLengthChallengeHeight_le_inv_slack_sq` bounds the challenge height by inverse
  slack squared.
* `lowRateFiniteLength_parameter_bounds` bounds all four interpolation parameters by one
  rate-dependent constant.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder

open ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- Literal low-rate challenge height with the exact floor and `max 1` endpoint. -/
def lowRateFiniteLengthChallengeHeight (rho eta : ℝ) (n : ℕ) : ℕ :=
  max 1 ⌊(lowRateFiniteLengthRankCount rho eta n : ℝ) *
    lowRateFiniteLengthJetDegree rho eta n /
      (lowRateFiniteLengthSourceCount rho eta n - lowRateFiniteLengthRankCount rho eta n)⌋₊

/-- Rate-only coefficient bounding the selected low-rate multiplicity. -/
def lowRateMultiplicityBoundConstant (rho : ℝ) : ℝ :=
  1 + 4 * lowRateFiniteLengthRankRoundingConstant rho / lowRateFiniteLengthSlope rho

/-- Rate-only coefficient bounding the low-rate derivative cap. -/
def lowRateDerivativeCapBoundConstant (rho : ℝ) : ℝ :=
  firstOrderLowRateBeta rho * lowRateMultiplicityBoundConstant rho

/-- Rate-only coefficient bounding the low-rate total jet degree. -/
def lowRateJetBoundConstant (rho : ℝ) : ℝ :=
  2 * lowRateMultiplicityBoundConstant rho / rho + 1

/-- Rate-only coefficient bounding the low-rate local rank count. -/
def lowRateRankBoundConstant (rho : ℝ) : ℝ :=
  firstOrderRankDensity (firstOrderLowRateBeta rho) +
    lowRateFiniteLengthRankRoundingConstant rho

/-- Rate-only coefficient bounding the low-rate challenge height. -/
def lowRateHeightBoundConstant (rho : ℝ) : ℝ :=
  1 + 4 * lowRateRankBoundConstant rho * lowRateJetBoundConstant rho /
    (3 * lowRateFiniteLengthSlope rho)

/-- One rate-only constant dominating the low-rate finite-length parameters. -/
def lowRateParameterBoundConstant (rho : ℝ) : ℝ :=
  max 1 (max (lowRateMultiplicityBoundConstant rho)
    (max (lowRateDerivativeCapBoundConstant rho)
      (max (lowRateJetBoundConstant rho) (lowRateHeightBoundConstant rho))))

/-- The finite-length slack is below one when the low-rate threshold plus slack is below one. -/
theorem lowRateFiniteLengthSlack_lt_one
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    finiteLengthSlack eta n < 1 := by
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hregime
  exact finiteLengthSlack_lt_one_of_threshold hthreshold haOne hn

/-- The finite-length slack is below one when the rate times length is at least one. -/
theorem lowRateFiniteLengthSlack_lt_one_of_one_le_rate_mul_length
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : 1 ≤ rho * n) :
    finiteLengthSlack eta n < 1 := by
  have hnPos : (0 : ℝ) < n := by
    have hprod : 0 < rho * (n : ℝ) := lt_of_lt_of_le zero_lt_one hn
    nlinarith [hrho]
  have hinv : 1 / (n : ℝ) ≤ rho := by
    rw [div_le_iff₀ hnPos]
    simpa [mul_comm] using hn
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hregime
  unfold finiteLengthSlack
  linarith

/-- The selected low-rate multiplicity is bounded by inverse slack. -/
theorem lowRateFiniteLengthMultiplicity_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthMultiplicity rho eta n : ℝ) ≤
      lowRateMultiplicityBoundConstant rho / finiteLengthSlack eta n := by
  let c := lowRateFiniteLengthSlope rho
  let s := finiteLengthSlack eta n
  let delta := lowRateFiniteLengthDensityMargin rho eta n
  let crank := lowRateFiniteLengthRankRoundingConstant rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  have hc : 0 < c := lowRateFiniteLengthSlope_pos hrho hlow
  have hs : 0 < s := finiteLengthSlack_pos heta
  have hsOne : s ≤ 1 := (lowRateFiniteLengthSlack_lt_one hrho hlow haOne hn).le
  have hdelta : c * s ≤ delta :=
    lowRateFiniteLengthSlope_mul_slack_le_margin hrho hlow heta haOne hn
  have hdeltaPos : 0 < delta := (mul_pos hc hs).trans_le hdelta
  have hcrank0 : 0 ≤ crank := by
    dsimp only [crank, lowRateFiniteLengthRankRoundingConstant]
    positivity [firstOrderLowRateBeta_pos hrho]
  have hx : 4 * crank / delta ≤ 4 * crank / (c * s) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hcrank0) (mul_pos hc hs) hdelta
  have hm : (m : ℝ) < 4 * crank / delta + 1 := by
    dsimp only [m, crank, delta]
    unfold lowRateFiniteLengthMultiplicity
    exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hcrank0) hdeltaPos.le)
  calc
    (m : ℝ) ≤ 4 * crank / (c * s) + 1 := by linarith
    _ = (4 * crank / c + s) / s := by field_simp [ne_of_gt hc, ne_of_gt hs]
    _ ≤ (4 * crank / c + 1) / s := by gcongr
    _ = lowRateMultiplicityBoundConstant rho / s := by
      dsimp only [c]
      rw [lowRateMultiplicityBoundConstant]
      ring

/-- The selected low-rate derivative cap is bounded by inverse slack. -/
theorem lowRateFiniteLengthDerivativeCap_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthDerivativeCap rho eta n : ℝ) ≤
      lowRateDerivativeCapBoundConstant rho / finiteLengthSlack eta n := by
  have hfloor : (lowRateFiniteLengthDerivativeCap rho eta n : ℝ) ≤
      firstOrderLowRateBeta rho * lowRateFiniteLengthMultiplicity rho eta n := by
    unfold lowRateFiniteLengthDerivativeCap
    exact Nat.floor_le (mul_nonneg (firstOrderLowRateBeta_pos hrho).le (Nat.cast_nonneg _))
  have hm := lowRateFiniteLengthMultiplicity_le_inv_slack hrho hlow heta haOne hn
  have hbeta := firstOrderLowRateBeta_pos hrho
  calc
    _ ≤ firstOrderLowRateBeta rho * lowRateFiniteLengthMultiplicity rho eta n := hfloor
    _ ≤ firstOrderLowRateBeta rho *
        (lowRateMultiplicityBoundConstant rho / finiteLengthSlack eta n) := by gcongr
    _ = lowRateDerivativeCapBoundConstant rho / finiteLengthSlack eta n := by
      rw [lowRateDerivativeCapBoundConstant]
      ring

/-- The selected derivative cap does not exceed the total jet degree. -/
theorem lowRateFiniteLengthDerivativeCap_le_jetDegree
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    lowRateFiniteLengthDerivativeCap rho eta n ≤ lowRateFiniteLengthJetDegree rho eta n := by
  let R := finiteLengthRate rho n
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let beta := firstOrderLowRateBeta rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  have hR : 0 < R := finiteLengthRate_pos hrho hn
  have hRrho : R < rho := finiteLengthRate_lt_rate
    (length_pos_of_two_le_rate_mul_length hn)
  have ha0 : 0 < a := lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le
  have hTa : firstOrderLowRateThreshold rho ≤ a := by
    have h := lowRateFiniteLengthCertifiedAgreement_ge_half_slack
      (rho := rho) heta.le haOne.le
    dsimp only [a] at h ⊢
    linarith
  have hbcut : beta < a / R :=
    (firstOrderLowRateBeta_lt_threshold_div_rate hrho).trans_le
      ((div_le_div_of_nonneg_right hTa hrho.le).trans
        (div_le_div_of_nonneg_left ha0.le hR hRrho.le))
  change ⌊beta * m⌋₊ ≤ ⌈(m : ℝ) * a / R⌉₊
  exact natFloor_mul_le_natCeil_mul_div hbcut.le

/-- The selected low-rate total jet degree is bounded by inverse slack. -/
theorem lowRateFiniteLengthJetDegree_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthJetDegree rho eta n : ℝ) ≤
      lowRateJetBoundConstant rho / finiteLengthSlack eta n := by
  let s := finiteLengthSlack eta n
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let R := finiteLengthRate rho n
  have hs : 0 < s := finiteLengthSlack_pos heta
  have hsOne : s ≤ 1 := (lowRateFiniteLengthSlack_lt_one hrho hlow haOne hn).le
  have hR : 0 < R := finiteLengthRate_pos hrho hn
  have hRhalf : rho / 2 ≤ R := half_rate_le_finiteLengthRate hn
  have ha0 : 0 ≤ a := (lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le).le
  have haOne' : a < 1 := lowRateFiniteLengthCertifiedAgreement_lt_one haOne
  have hm := lowRateFiniteLengthMultiplicity_le_inv_slack hrho hlow heta haOne hn
  change (Nat.ceil ((m : ℝ) * a / R) : ℝ) ≤
    (2 * lowRateMultiplicityBoundConstant rho / rho + 1) / s
  exact Nat.cast_ceil_mul_div_le_inv_slack hrho hs hsOne ha0 (le_of_lt haOne')
    hR hRhalf hm

/-- The selected low-rate challenge height is bounded by inverse slack squared. -/
theorem lowRateFiniteLengthChallengeHeight_le_inv_slack_sq
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthChallengeHeight rho eta n : ℝ) ≤
      lowRateHeightBoundConstant rho / finiteLengthSlack eta n ^ 2 := by
  let s := finiteLengthSlack eta n
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let B := lowRateFiniteLengthJetDegree rho eta n
  let r := lowRateFiniteLengthRankCount rho eta n
  let N := lowRateFiniteLengthSourceCount rho eta n
  let c := lowRateFiniteLengthSlope rho
  let cr := lowRateRankBoundConstant rho
  let cB := lowRateJetBoundConstant rho
  have hs : 0 < s := finiteLengthSlack_pos heta
  have hsOne : s ≤ 1 := (lowRateFiniteLengthSlack_lt_one hrho hlow haOne hn).le
  have hmNat : 0 < m := lowRateFiniteLengthMultiplicity_pos hrho hlow heta haOne hn
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hc : 0 < c := lowRateFiniteLengthSlope_pos hrho hlow
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
  have hrankDensity : 0 ≤ firstOrderRankDensity (firstOrderLowRateBeta rho) := by
    rw [firstOrderRankDensity, ite_eq_right (not_le.mpr
      (half_lt_firstOrderLowRateBeta hrho hregime))]
    positivity [firstOrderLowRateBeta_pos hrho]
  have hcrank : 0 ≤ lowRateFiniteLengthRankRoundingConstant rho := by
    unfold lowRateFiniteLengthRankRoundingConstant
    positivity [firstOrderLowRateBeta_pos hrho]
  have hcr : 0 ≤ cr := by
    dsimp only [cr, lowRateRankBoundConstant]
    positivity
  have hcB : 0 ≤ cB := by
    dsimp only [cB, lowRateJetBoundConstant, lowRateMultiplicityBoundConstant,
      lowRateFiniteLengthRankRoundingConstant]
    positivity
  have hdelta := lowRateFiniteLengthSlope_mul_slack_le_margin
    hrho hlow heta haOne hn
  have hgap := lowRateFiniteLength_count_gap hrho hlow heta haOne hn
  have hgapLower : 3 * (m : ℝ) ^ 3 * (c * s) / 4 ≤ N - r := by
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdelta (by positivity)) (by norm_num)).trans hgap
  have hrank0 := firstOrderRankCount_floor_le_density_add_rounding
    (firstOrderLowRateBeta_pos hrho).le (lowRateFiniteLengthMultiplicity rho eta n)
  have hrank : (lowRateFiniteLengthRankCount rho eta n : ℝ) ≤
      (lowRateFiniteLengthMultiplicity rho eta n : ℝ) ^ 3 *
        firstOrderRankDensity (firstOrderLowRateBeta rho) +
      lowRateFiniteLengthRankRoundingConstant rho *
        (lowRateFiniteLengthMultiplicity rho eta n : ℝ) ^ 2 := by
    simpa only [lowRateFiniteLengthRankCount, lowRateFiniteLengthDerivativeCap,
      lowRateFiniteLengthRankRoundingConstant] using hrank0
  have hr : (r : ℝ) ≤ cr * (m : ℝ) ^ 3 := by
    have hmSqCube : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr (show (1 : ℝ) ≤ m by
        exact_mod_cast hmNat))]
    dsimp only [r, cr, lowRateRankBoundConstant] at hrank ⊢
    nlinarith [mul_le_mul_of_nonneg_left hmSqCube hcrank]
  have hB : (B : ℝ) ≤ cB / s :=
    lowRateFiniteLengthJetDegree_le_inv_slack hrho hlow heta haOne hn
  have hhelper := Nat.cast_max_one_floor_mul_div_le_inv_slack_sq
    hm hs hsOne hc hcr hcB hr hB hgapLower
  have hchallenge : (lowRateFiniteLengthChallengeHeight rho eta n : ℝ) ≤
      (1 + 4 * cr * cB / (3 * c)) / s ^ 2 := by
    simpa only [lowRateFiniteLengthChallengeHeight, B, r, N] using hhelper
  calc
    (lowRateFiniteLengthChallengeHeight rho eta n : ℝ) ≤
        (1 + 4 * cr * cB / (3 * c)) / s ^ 2 := hchallenge
    _ = lowRateHeightBoundConstant rho / s ^ 2 := by
      dsimp only [lowRateHeightBoundConstant, cr, cB, c, s]

/-- One rate-only constant bounds all low-rate finite-length interpolation parameters. -/
theorem lowRateFiniteLength_parameter_bounds
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    let C := lowRateParameterBoundConstant rho
    let s := finiteLengthSlack eta n
    (lowRateFiniteLengthMultiplicity rho eta n : ℝ) ≤ C / s ∧
      (lowRateFiniteLengthDerivativeCap rho eta n : ℝ) ≤ C / s ∧
      (lowRateFiniteLengthJetDegree rho eta n : ℝ) ≤ C / s ∧
      (lowRateFiniteLengthChallengeHeight rho eta n : ℝ) ≤ C / s ^ 2 := by
  dsimp only
  have hs := finiteLengthSlack_pos (n := n) heta
  have hm := lowRateFiniteLengthMultiplicity_le_inv_slack hrho hlow heta haOne hn
  have hM := lowRateFiniteLengthDerivativeCap_le_inv_slack hrho hlow heta haOne hn
  have hB := lowRateFiniteLengthJetDegree_le_inv_slack hrho hlow heta haOne hn
  have hH := lowRateFiniteLengthChallengeHeight_le_inv_slack_sq
    hrho hlow heta haOne hn
  unfold lowRateParameterBoundConstant
  refine ⟨hm.trans (div_le_div_of_nonneg_right ?_ hs.le),
    hM.trans (div_le_div_of_nonneg_right ?_ hs.le),
    hB.trans (div_le_div_of_nonneg_right ?_ hs.le),
    hH.trans (div_le_div_of_nonneg_right ?_ (sq_nonneg _))⟩
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

end

end ReedSolomon.FirstOrder
