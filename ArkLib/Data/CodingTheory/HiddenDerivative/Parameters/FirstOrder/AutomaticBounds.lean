/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.AutomaticParameters
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridRateEnvelope
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Explicit slack bounds for the automatic first-order recipe

This module bounds the multiplicity, derivative cap, jet degree, challenge height, and staircase
moment in terms of the slack above the first-order rate threshold. It also gives cubic and quintic
bounds for the closed list and exceptional-set constants.

## Main statements

* `automaticMultiplicity_le_inv_eta`, `automaticDerivativeCap_le_inv_eta`, and
  `automaticJetDegree_le_inv_eta` bound the rounded interpolation parameters.
* `automaticChallengeHeight_le_inv_eta_sq` and `automaticStaircaseMoment_le_inv_eta_cube` bound the
  challenge height and staircase moment.
* `automaticRateIncidenceJetBounds` supplies the shared rate, incidence-ratio, and jet-degree
  bounds for the automatic recipe.
* `automaticListConstant_le_cubic_slack_envelope` and
  `automaticExceptionConstant_le_quintic_slack_envelope` bound the closed list and exceptional-set
  constants.
* `automaticClosedListAndExceptionBounds` derives both closed bounds from the physical-rate guards.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- The distance from the first-order threshold to agreement one. -/
def automaticRateGap (rho : ℝ) : ℝ := 1 - firstOrderRateThreshold rho

/-- A rate-only linear lower coefficient for the automatic surplus. -/
def automaticSurplusSlope (rho : ℝ) : ℝ := 3 * automaticRateGap rho / 64

/-- Rate-only coefficient bounding the automatic multiplicity by `1 / eta`. -/
def automaticMultiplicityBoundConstant (rho : ℝ) : ℝ :=
  1 + 256 / (3 * automaticRateGap rho)

/-- Rate-only coefficient bounding the total jet degree by `1 / eta`. -/
def automaticJetBoundConstant (rho : ℝ) : ℝ :=
  automaticMultiplicityBoundConstant rho / rho + 1

/-- Rate-only coefficient bounding the automatic challenge height by `1 / eta^2`. -/
def automaticHeightBoundConstant (rho : ℝ) : ℝ :=
  1 + 16 * automaticJetBoundConstant rho / automaticSurplusSlope rho

/-- Rate-only coefficient bounding the staircase moment by `1 / eta^3`. -/
def automaticMomentBoundConstant (rho : ℝ) : ℝ :=
  3 * automaticJetBoundConstant rho ^ 3

/-- A common rate-only budget for the recipe and the retained agreement ratio. -/
def automaticRateEnvelopeConstant (rho : ℝ) : ℝ :=
  max 1 (max (1 / (firstOrderRateThreshold rho - rho))
    (max (automaticJetBoundConstant rho)
      (max (automaticHeightBoundConstant rho) (automaticMomentBoundConstant rho))))

/-- The explicit rate-only coefficient in the cubic list envelope. -/
def automaticListBoundConstant (rho : ℝ) : ℝ :=
  3 * automaticRateEnvelopeConstant rho ^ 2

/-- The explicit rate-only coefficient in the quintic exception envelope. -/
def automaticExceptionBoundConstant (rho : ℝ) : ℝ :=
  45 * automaticRateEnvelopeConstant rho ^ 4

/-- The threshold lies strictly below agreement one for rates in `(0, 1)`. -/
theorem automaticRateGap_pos {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1) :
    0 < automaticRateGap rho := by
  unfold automaticRateGap
  exact sub_pos.mpr ((firstOrderRateThreshold_lt_sqrt hrho hrhoOne).trans
    (by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hrho.le hrhoOne))

/-- The admissible slack is smaller than the distance from threshold to one. -/
theorem automatic_eta_lt_rateGap {rho eta : ℝ}
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    eta < automaticRateGap rho := by
  unfold automaticRateGap
  linarith

/-- Capping the agreement gap loses at most a factor two over its whole public range. -/
theorem half_eta_le_automaticAgreement_sub_threshold {rho eta : ℝ}
    (heta : 0 < eta) (haOne : firstOrderRateThreshold rho + eta < 1) :
    eta / 2 ≤ automaticAgreement rho (firstOrderRateThreshold rho + eta) -
      firstOrderRateThreshold rho := by
  have hetaGap : eta ≤ automaticRateGap rho :=
    (automatic_eta_lt_rateGap haOne).le
  rw [automaticAgreement_eq_min, min_def]
  split_ifs <;> unfold automaticRateGap at hetaGap <;> linarith

/-- The surplus bracket grows at least linearly with slope `1/2` above its root. -/
theorem half_agreement_slack_le_automaticGapBracket {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    (automaticAgreement rho (firstOrderRateThreshold rho + eta) -
        firstOrderRateThreshold rho) / 2 ≤
      automaticGapBracket rho (firstOrderRateThreshold rho + eta) := by
  let a₁ := firstOrderRateThreshold rho
  let a₀ := automaticAgreement rho (firstOrderRateThreshold rho + eta)
  have hroot : a₁ ^ 2 / rho - 1 +
      3 * (1 - a₁) ^ 2 / (4 * (2 - rho)) = 0 := by
    have hclean := firstOrderCleanExpression_threshold_eq_one hrho (by linarith)
    dsimp only [a₁, firstOrderCleanExpression] at hclean
    linarith
  have ha₁rho := rate_lt_firstOrderRateThreshold hrho hrhoOne
  have ha₀a₁ : a₁ ≤ a₀ := by
    exact (automatic_threshold_lt_agreement hrho hrhoOne (by linarith)).le
  have ha₀one : a₀ < 1 := by
    dsimp only [a₀]
    exact automaticAgreement_lt_one haOne
  have hcoef : 1 / 2 ≤ (a₀ + a₁) / rho +
      3 * (a₀ + a₁ - 2) / (4 * (2 - rho)) := by
    have ha₀rho : rho < a₀ := ha₁rho.trans_le ha₀a₁
    have hfirst : 2 ≤ (a₀ + a₁) / rho := by
      apply (le_div_iff₀ hrho).2
      linarith
    have hsecond : -(3 / 4 : ℝ) ≤
        3 * (a₀ + a₁ - 2) / (4 * (2 - rho)) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) (by linarith))).2
      linarith
    linarith
  have hdiff :
      automaticGapBracket rho (firstOrderRateThreshold rho + eta) =
        (a₀ - a₁) * ((a₀ + a₁) / rho +
          3 * (a₀ + a₁ - 2) / (4 * (2 - rho))) := by
    have hroot' : a₁ ^ 2 / rho - 1 +
        3 * (1 - a₁) ^ 2 / (4 * (2 - rho)) = 0 := by
      simpa only [a₁] using hroot
    change firstOrderCleanExpression rho a₀ - 1 = _
    unfold firstOrderCleanExpression
    field_simp [ne_of_gt hrho, ne_of_gt (show 0 < 2 - rho by linarith)]
      at hroot' ⊢
    linear_combination hroot'
  change (a₀ - a₁) / 2 ≤ automaticGapBracket rho
    (firstOrderRateThreshold rho + eta)
  rw [hdiff]
  have hmul := mul_le_mul_of_nonneg_left hcoef (sub_nonneg.mpr ha₀a₁)
  linarith

/-- The normalized surplus is bounded below by a rate-only multiple of the public slack. -/
theorem automaticSurplusSlope_mul_eta_le {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    automaticSurplusSlope rho * eta ≤
      automaticSurplus rho (firstOrderRateThreshold rho + eta) := by
  let a := firstOrderRateThreshold rho + eta
  let a₀ := automaticAgreement rho a
  have hgap := automaticRateGap_pos hrho hrhoOne
  have hslack := half_eta_le_automaticAgreement_sub_threshold heta haOne
  have hG := half_agreement_slack_le_automaticGapBracket hrho hrhoOne heta haOne
  have hbeta : 3 * automaticRateGap rho / 8 ≤ automaticDerivativeRatio rho a := by
    have ha₀mid : a₀ ≤ (1 + firstOrderRateThreshold rho) / 2 := by
      dsimp only [a₀, a]
      rw [automaticAgreement_eq_min]
      exact min_le_right _ _
    have hden : 0 < 2 * (2 - rho) := mul_pos (by norm_num) (by linarith)
    unfold automaticDerivativeRatio
    dsimp only [a₀, a]
    unfold automaticRateGap firstOrderRateBeta
    rw [le_div_iff₀ hden]
    nlinarith
  have hG' : eta / 4 ≤ automaticGapBracket rho a := by
    dsimp only [a, a₀] at hslack hG ⊢
    linarith
  have hb0 : 0 ≤ 3 * automaticRateGap rho / 8 := by positivity
  have hG0 : 0 ≤ automaticGapBracket rho a := by
    unfold automaticGapBracket
    have hthreshold := automatic_threshold_lt_agreement (a := a) hrho hrhoOne
      (by dsimp only [a]; linarith)
    exact (sub_pos.mpr (firstOrderCleanExpression_gt_one hrho hrhoOne hthreshold)).le
  unfold automaticSurplus automaticSurplusSlope
  dsimp only [a] at hbeta hG' hG0 ⊢
  calc
    3 * automaticRateGap rho / 64 * eta =
        (3 * automaticRateGap rho / 8) * (eta / 4) / 2 := by ring
    _ ≤ automaticDerivativeRatio rho (firstOrderRateThreshold rho + eta) *
          automaticGapBracket rho (firstOrderRateThreshold rho + eta) / 2 := by
      gcongr
      exact (automaticDerivativeRatio_pos hrhoOne haOne).le

/-- The rate-only surplus coefficient is positive for rates in `(0, 1)`. -/
theorem automaticSurplusSlope_pos {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1) :
    0 < automaticSurplusSlope rho := by
  unfold automaticSurplusSlope
  positivity [automaticRateGap_pos hrho hrhoOne]

/-- The multiplicity coefficient is positive for rates in `(0, 1)`. -/
theorem automaticMultiplicityBoundConstant_pos {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) :
    0 < automaticMultiplicityBoundConstant rho := by
  unfold automaticMultiplicityBoundConstant automaticRateGap
  positivity [automaticRateGap_pos hrho hrhoOne]

/-- The jet-degree coefficient is positive for rates in `(0, 1)`. -/
theorem automaticJetBoundConstant_pos {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) :
    0 < automaticJetBoundConstant rho := by
  unfold automaticJetBoundConstant
  positivity [automaticMultiplicityBoundConstant_pos hrho hrhoOne]

/-- The literal automatic multiplicity is at most a rate-only constant times `eta⁻¹`. -/
theorem automaticMultiplicity_le_inv_eta {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    (automaticMultiplicity rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
      automaticMultiplicityBoundConstant rho / eta := by
  let a := firstOrderRateThreshold rho + eta
  let S := automaticSurplus rho a
  let c := automaticSurplusSlope rho
  let m := automaticMultiplicity rho a
  have hgap := automaticRateGap_pos hrho hrhoOne
  have hetaOne : eta ≤ 1 := by
    have := automatic_eta_lt_rateGap haOne
    unfold automaticRateGap at this
    have hthresholdPos := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans' hrho
    linarith
  have hc : 0 < c := automaticSurplusSlope_pos hrho hrhoOne
  have hS : c * eta ≤ S := automaticSurplusSlope_mul_eta_le hrho hrhoOne heta haOne
  have hSpos : 0 < S := (mul_pos hc heta).trans_le hS
  have hm : (m : ℝ) < 4 / S + 1 := by
    dsimp only [m, S, a]
    exact Nat.ceil_lt_add_one (by positivity)
  have hfrac : 4 / S ≤ 4 / (c * eta) := by
    exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hc heta) hS
  have hm' : (m : ℝ) ≤ 4 / (c * eta) + 1 := by
    exact hm.le.trans (by simpa only [add_comm] using add_le_add_right hfrac 1)
  calc
    (m : ℝ) ≤ 4 / (c * eta) + 1 := hm'
    _ ≤ automaticMultiplicityBoundConstant rho / eta := by
      change 4 / (automaticSurplusSlope rho * eta) + 1 ≤
        (1 + 256 / (3 * automaticRateGap rho)) / eta
      rw [le_div_iff₀ heta]
      unfold automaticSurplusSlope
      field_simp [ne_of_gt heta, ne_of_gt hgap]
      linarith [mul_le_mul_of_nonneg_left hetaOne hgap.le]

/-- The normalized derivative cap has the same inverse-slack bound as the multiplicity. -/
theorem automaticDerivativeCap_le_inv_eta {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
      automaticMultiplicityBoundConstant rho / eta := by
  let a := firstOrderRateThreshold rho + eta
  have hbeta := automaticDerivativeRatio_lt_three_four (rho := rho) (a := a) hrho hrhoOne
    (by dsimp only [a]; linarith)
  have hbeta0 := (automaticDerivativeRatio_pos hrhoOne haOne).le
  have hfloor : automaticDerivativeCapRaw rho a ≤ automaticMultiplicity rho a := by
    have hm : (0 : ℝ) ≤ automaticMultiplicity rho a := Nat.cast_nonneg _
    have hcast : (automaticDerivativeCapRaw rho a : ℝ) ≤
        (automaticMultiplicity rho a : ℝ) := calc
      (automaticDerivativeCapRaw rho a : ℝ) ≤
          automaticDerivativeRatio rho a * automaticMultiplicity rho a := by
        unfold automaticDerivativeCapRaw
        exact Nat.floor_le (mul_nonneg hbeta0 hm)
      automaticDerivativeRatio rho a * automaticMultiplicity rho a ≤
          1 * automaticMultiplicity rho a :=
        mul_le_mul_of_nonneg_right (hbeta.trans (by norm_num)).le hm
      _ = _ := one_mul _
    exact_mod_cast hcast
  rw [automaticDerivativeCap_eq_raw hrho hrhoOne (by linarith) haOne]
  exact (Nat.cast_le.mpr hfloor).trans
    (automaticMultiplicity_le_inv_eta hrho hrhoOne heta haOne)

/-- The rounded total jet degree is at most a rate-only constant times `eta⁻¹`. -/
theorem automaticJetDegree_le_inv_eta {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    (automaticJetDegree rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
      automaticJetBoundConstant rho / eta := by
  let a := firstOrderRateThreshold rho + eta
  let m := automaticMultiplicity rho a
  let a₀ := automaticAgreement rho a
  have hetaOne : eta ≤ 1 := by
    have := automatic_eta_lt_rateGap haOne
    have hthresholdPos := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans' hrho
    unfold automaticRateGap at this
    linarith
  have ha₀One : a₀ ≤ 1 := by
    unfold a₀ a
    exact (automaticAgreement_lt_one (rho := rho) haOne).le
  have harg : 0 ≤ (m : ℝ) * a₀ / rho := by
    have ha : firstOrderRateThreshold rho < a := by dsimp only [a]; linarith
    have ha₀pos := hrho.trans (rho_lt_automaticAgreement hrho hrhoOne ha)
    positivity
  have hceil : (automaticJetDegree rho a : ℝ) < (m : ℝ) * a₀ / rho + 1 := by
    exact Nat.ceil_lt_add_one harg
  have hm := automaticMultiplicity_le_inv_eta hrho hrhoOne heta haOne
  have hma : (m : ℝ) * a₀ ≤ automaticMultiplicityBoundConstant rho / eta := by
    exact (mul_le_of_le_one_right (Nat.cast_nonneg _) ha₀One).trans hm
  apply (le_div_iff₀ heta).2
  have hdiv : (m : ℝ) * a₀ / rho ≤
      (automaticMultiplicityBoundConstant rho / eta) / rho := by
    exact div_le_div_of_nonneg_right hma hrho.le
  have hscaled' := mul_le_mul_of_nonneg_right
    (hceil.le.trans (by simpa only [add_comm] using add_le_add_right hdiv 1)) heta.le
  unfold automaticJetBoundConstant
  field_simp [ne_of_gt hrho, ne_of_gt heta] at hscaled' ⊢
  linarith [mul_le_mul_of_nonneg_right hetaOne hrho.le]

/-- The continuous rank density stays below one throughout the automatic range. -/
theorem automaticRankDensityEnvelope_le_one {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    automaticRankDensityEnvelope rho a ≤ 1 := by
  let beta := automaticDerivativeRatio rho a
  have hb0 : 0 ≤ beta := (automaticDerivativeRatio_pos hrhoOne haOne).le
  have hb1 : beta ≤ 1 :=
    ((automaticDerivativeRatio_lt_three_four hrho hrhoOne ha).trans
      (by norm_num : (3 / 4 : ℝ) < 1)).le
  have hb3 : beta ^ 3 ≤ 1 := pow_le_one₀ hb0 hb1
  unfold automaticRankDensityEnvelope firstOrderRankCubicEnvelope
  dsimp only [beta] at hb0 hb1 hb3 ⊢
  nlinarith [sq_nonneg (automaticDerivativeRatio rho a)]

/-- The exact local rank is bounded by four multiplicity cubes. -/
theorem automaticRankCount_le_four_mul_cube {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    (automaticRankCount rho a : ℝ) ≤
      4 * (automaticMultiplicity rho a : ℝ) ^ 3 := by
  let m := automaticMultiplicity rho a
  have hmNat : 1 ≤ m := automaticMultiplicity_pos hrho hrhoOne ha haOne
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hmNat
  have hrank := automaticRankCount_le_densityEnvelope_add_rounding
    hrho hrhoOne ha haOne
  have hdensity := automaticRankDensityEnvelope_le_one hrho hrhoOne ha haOne
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmul : (m : ℝ) ^ 3 * automaticRankDensityEnvelope rho a ≤ m ^ 3 :=
    mul_le_of_le_one_right (pow_nonneg hm0 3) hdensity
  dsimp only [m] at hm hrank hmul ⊢
  linarith [mul_nonneg (sq_nonneg (automaticMultiplicity rho a : ℝ))
    (sub_nonneg.mpr hm)]

/-- The literal automatic challenge height is at most a rate-only multiple of `eta⁻²`. -/
theorem automaticChallengeHeight_le_inv_eta_sq {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    (automaticChallengeHeight rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
      automaticHeightBoundConstant rho / eta ^ 2 := by
  let a := firstOrderRateThreshold rho + eta
  let m := automaticMultiplicity rho a
  let mu := automaticJetDegree rho a
  let r := automaticRankCount rho a
  let N₀ := automaticSourceCount rho a
  let S := automaticSurplus rho a
  let c := automaticSurplusSlope rho
  let x := (r : ℝ) * mu / (N₀ - r)
  have ha : firstOrderRateThreshold rho < a := by dsimp only [a]; linarith
  have hmNat : 0 < m := automaticMultiplicity_pos hrho hrhoOne ha haOne
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hmu0 : (0 : ℝ) ≤ mu := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hSpos : 0 < S := automaticSurplus_pos hrho hrhoOne ha haOne
  have hc : 0 < c := automaticSurplusSlope_pos hrho hrhoOne
  have hden : 0 < N₀ - r := automaticChallengeDenominator_pos hrho hrhoOne ha haOne
  have hdenLower : (m : ℝ) ^ 3 * S / 4 ≤ N₀ - r :=
    automaticSurplusQuarter_le_source_sub_rank hrho hrhoOne ha haOne
  have hrank : (r : ℝ) ≤ 4 * (m : ℝ) ^ 3 :=
    automaticRankCount_le_four_mul_cube hrho hrhoOne ha haOne
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hx : x ≤ 16 * (mu : ℝ) / S := by
    have hsmallDen : 0 < (m : ℝ) ^ 3 * S / 4 := by positivity
    calc
      x ≤ (4 * (m : ℝ) ^ 3 * mu) / ((m : ℝ) ^ 3 * S / 4) := by
        dsimp only [x]
        exact div_le_div₀ (mul_nonneg (by positivity) hmu0)
          (mul_le_mul_of_nonneg_right hrank hmu0) hsmallDen hdenLower
      _ = 16 * (mu : ℝ) / S := by
        field_simp [ne_of_gt hm, ne_of_gt hSpos]
        ring
  have hheight : (automaticChallengeHeight rho a : ℝ) ≤ 1 + x := by
    rw [automaticChallengeHeight_eq, Nat.cast_max]
    apply max_le
    · exact_mod_cast (show (1 : ℝ) ≤ 1 + x from le_add_of_nonneg_right hx0)
    · have hfloor :
          (⌊(r : ℝ) * mu / (N₀ - r)⌋₊ : ℝ) ≤ x := by
          dsimp only [x]
          exact Nat.floor_le (by positivity)
      exact hfloor.trans (by linarith)
  have hS : c * eta ≤ S := automaticSurplusSlope_mul_eta_le hrho hrhoOne heta haOne
  have hmu := automaticJetDegree_le_inv_eta hrho hrhoOne heta haOne
  have hfracS : 16 * (mu : ℝ) / S ≤ 16 * mu / (c * eta) := by
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hmu0)
      (mul_pos hc heta) hS
  have hfracMu : 16 * (mu : ℝ) / (c * eta) ≤
      16 * automaticJetBoundConstant rho / (c * eta ^ 2) := by
    rw [div_le_div_iff₀ (mul_pos hc heta) (mul_pos hc (sq_pos_of_pos heta))]
    have := mul_le_mul_of_nonneg_left hmu (by norm_num : (0 : ℝ) ≤ 16)
    field_simp [ne_of_gt heta] at this ⊢
    exact this
  have hetaOne : eta ≤ 1 := by
    have := automatic_eta_lt_rateGap haOne
    have hthresholdPos := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans' hrho
    unfold automaticRateGap at this
    linarith
  calc
    (automaticChallengeHeight rho a : ℝ) ≤ 1 + x := hheight
    _ ≤ 1 + 16 * (mu : ℝ) / S := by linarith
    _ ≤ 1 + 16 * automaticJetBoundConstant rho / (c * eta ^ 2) := by
      linarith [hfracS.trans hfracMu]
    _ ≤ automaticHeightBoundConstant rho / eta ^ 2 := by
      change 1 + 16 * automaticJetBoundConstant rho /
          (automaticSurplusSlope rho * eta ^ 2) ≤
        (1 + 16 * automaticJetBoundConstant rho /
          automaticSurplusSlope rho) / eta ^ 2
      rw [le_div_iff₀ (sq_pos_of_pos heta)]
      have hjet0 := (automaticJetBoundConstant_pos hrho hrhoOne).le
      have hetaSqOne : eta ^ 2 ≤ 1 := pow_le_one₀ heta.le hetaOne
      field_simp [ne_of_gt heta, ne_of_gt hc]
      linarith

/-- The automatic staircase moment is at most a rate-only multiple of `eta⁻³`. -/
theorem automaticStaircaseMoment_le_inv_eta_cube {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    stageStaircase (automaticJetDegree rho (firstOrderRateThreshold rho + eta))
        (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) ≤
      automaticMomentBoundConstant rho / eta ^ 3 := by
  let a := firstOrderRateThreshold rho + eta
  let mu := automaticJetDegree rho a
  let M := automaticDerivativeCap rho a
  have ha : firstOrderRateThreshold rho < a := by dsimp only [a]; linarith
  have hmuNat : 1 ≤ mu := automaticJetDegree_pos hrho hrhoOne ha haOne
  have hMmu : M ≤ mu := by
    unfold M automaticDerivativeCap
    exact min_le_right _ _
  have hT := stageStaircase_le_three_mul_cube hmuNat hMmu
  have hmu := automaticJetDegree_le_inv_eta hrho hrhoOne heta haOne
  have hcube : (mu : ℝ) ^ 3 ≤
      (automaticJetBoundConstant rho / eta) ^ 3 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hmu 3
  calc
    stageStaircase mu M ≤ 3 * (mu : ℝ) ^ 3 := hT
    _ ≤ 3 * (automaticJetBoundConstant rho / eta) ^ 3 := by gcongr
    _ = automaticMomentBoundConstant rho / eta ^ 3 := by
      unfold automaticMomentBoundConstant
      field_simp [ne_of_gt heta]

/-- All literal automatic parameters satisfy the explicit rate-only slack bounds. -/
theorem automaticParameterBounds {rho eta : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1) :
    (automaticMultiplicity rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
        automaticMultiplicityBoundConstant rho / eta ∧
      (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
        automaticMultiplicityBoundConstant rho / eta ∧
      (automaticJetDegree rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
        automaticJetBoundConstant rho / eta ∧
      (automaticChallengeHeight rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
        automaticHeightBoundConstant rho / eta ^ 2 ∧
      stageStaircase (automaticJetDegree rho (firstOrderRateThreshold rho + eta))
          (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) ≤
        automaticMomentBoundConstant rho / eta ^ 3 := by
  exact ⟨automaticMultiplicity_le_inv_eta hrho hrhoOne heta haOne,
    automaticDerivativeCap_le_inv_eta hrho hrhoOne heta haOne,
    automaticJetDegree_le_inv_eta hrho hrhoOne heta haOne,
    automaticChallengeHeight_le_inv_eta_sq hrho hrhoOne heta haOne,
    automaticStaircaseMoment_le_inv_eta_cube hrho hrhoOne heta haOne⟩

/-- The common envelope constant is at least one. -/
theorem automaticRateEnvelopeConstant_one_le (rho : ℝ) :
    1 ≤ automaticRateEnvelopeConstant rho := by
  unfold automaticRateEnvelopeConstant
  exact le_max_left _ _

/-- The common envelope constant dominates the inverse first-order rate gap. -/
theorem automaticRateGapInv_le_rateEnvelopeConstant (rho : ℝ) :
    1 / (firstOrderRateThreshold rho - rho) ≤
      automaticRateEnvelopeConstant rho := by
  unfold automaticRateEnvelopeConstant
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- The common envelope constant dominates the jet-degree coefficient. -/
theorem automaticJetBoundConstant_le_envelope (rho : ℝ) :
    automaticJetBoundConstant rho ≤ automaticRateEnvelopeConstant rho := by
  simp only [automaticRateEnvelopeConstant, le_max_iff]
  exact Or.inr (Or.inr (Or.inl le_rfl))

/-- The common envelope constant dominates the challenge-height coefficient. -/
theorem automaticHeightBoundConstant_le_envelope (rho : ℝ) :
    automaticHeightBoundConstant rho ≤ automaticRateEnvelopeConstant rho := by
  simp only [automaticRateEnvelopeConstant, le_max_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inl le_rfl)))

/-- The common envelope constant dominates the staircase-moment coefficient. -/
theorem automaticMomentBoundConstant_le_envelope (rho : ℝ) :
    automaticMomentBoundConstant rho ≤ automaticRateEnvelopeConstant rho := by
  simp only [automaticRateEnvelopeConstant, le_max_iff]
  tauto

/-- The automatic rate envelope bounds the agreement-incidence ratio and jet degree throughout
the admissible slack range. -/
theorem automaticRateIncidenceJetBounds {rho eta : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hDn : D ≤ n) (hDA : D < A)
    (hD : (D : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A) :
    1 ≤ automaticRateEnvelopeConstant rho ∧
    1 ≤ 1 / eta ∧
    0 ≤ agreementIncidenceRatio n D A ∧
    agreementIncidenceRatio n D A ≤ automaticRateEnvelopeConstant rho ∧
    1 ≤ automaticJetDegree rho (firstOrderRateThreshold rho + eta) ∧
    (automaticJetDegree rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
      automaticRateEnvelopeConstant rho / eta := by
  let a := firstOrderRateThreshold rho + eta
  let C := automaticRateEnvelopeConstant rho
  let q := 1 / eta
  have ha : firstOrderRateThreshold rho < a := by dsimp only [a]; linarith
  have hthresholdGap : 0 < firstOrderRateThreshold rho - rho :=
    sub_pos.mpr (rate_lt_firstOrderRateThreshold hrho hrhoOne)
  have hC : 1 ≤ C := automaticRateEnvelopeConstant_one_le rho
  have hetaOne : eta ≤ 1 := by
    have hgap := automatic_eta_lt_rateGap haOne
    have hthresholdPos := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans' hrho
    unfold automaticRateGap at hgap
    linarith
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact (one_le_div heta).2 hetaOne
  have htheta0 : 0 ≤ agreementIncidenceRatio n D A := by
    unfold agreementIncidenceRatio
    positivity
  have hthetaRate := agreementIncidenceRatio_le_one_div_sub hDn hDA hD hA
    (show rho < a by exact (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans ha)
  have htheta : agreementIncidenceRatio n D A ≤ C := by
    calc
      agreementIncidenceRatio n D A ≤ 1 / (a - rho) := hthetaRate
      _ ≤ 1 / (firstOrderRateThreshold rho - rho) := by
        exact div_le_div_of_nonneg_left zero_le_one hthresholdGap (by dsimp only [a]; linarith)
      _ ≤ C := automaticRateGapInv_le_rateEnvelopeConstant rho
  have hmuPos : 1 ≤ automaticJetDegree rho a := automaticJetDegree_pos hrho hrhoOne ha haOne
  have hmu : (automaticJetDegree rho a : ℝ) ≤ C * q := by
    calc
      (automaticJetDegree rho a : ℝ) ≤ automaticJetBoundConstant rho / eta :=
        automaticJetDegree_le_inv_eta hrho hrhoOne heta haOne
      _ = automaticJetBoundConstant rho * q := by dsimp only [q]; ring
      _ ≤ C * q := by
        gcongr
        exact automaticJetBoundConstant_le_envelope rho
  dsimp only [a, C, q] at hC hq htheta0 htheta hmuPos hmu
  refine ⟨hC, ?_, htheta0, htheta, hmuPos, ?_⟩
  · simpa only [div_eq_mul_inv] using hq
  · simpa only [div_eq_mul_inv, one_mul] using hmu

private theorem automaticClosedEnvelopeInputs {rho eta : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hDn : D ≤ n) (hDA : D < A)
    (hD : (D : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A) :
    1 ≤ automaticRateEnvelopeConstant rho ∧
    1 ≤ 1 / eta ∧
    0 ≤ agreementIncidenceRatio n D A ∧
    agreementIncidenceRatio n D A ≤ automaticRateEnvelopeConstant rho ∧
    1 ≤ automaticJetDegree rho (firstOrderRateThreshold rho + eta) ∧
    (automaticJetDegree rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
      automaticRateEnvelopeConstant rho / eta ∧
    (automaticChallengeHeight rho (firstOrderRateThreshold rho + eta) : ℝ) ≤
      automaticRateEnvelopeConstant rho / eta ^ 2 ∧
    stageStaircase (automaticJetDegree rho (firstOrderRateThreshold rho + eta))
      (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) ≤
        automaticRateEnvelopeConstant rho / eta ^ 3 := by
  let a := firstOrderRateThreshold rho + eta
  let C := automaticRateEnvelopeConstant rho
  let q := 1 / eta
  let mu := automaticJetDegree rho a
  let M := automaticDerivativeCap rho a
  have ha : firstOrderRateThreshold rho < a := by dsimp only [a]; linarith
  obtain ⟨hC, hq, htheta0, htheta, hmuPos, hmuDiv⟩ :=
    automaticRateIncidenceJetBounds hrho hrhoOne heta haOne hDn hDA hD hA
  have hmu : (mu : ℝ) ≤ C * q := by
    calc
      (mu : ℝ) ≤ automaticRateEnvelopeConstant rho / eta := by
        simpa only [a, mu] using hmuDiv
      _ = C * q := by dsimp only [C, q]; ring
  have hh : (automaticChallengeHeight rho a : ℝ) ≤ C * q ^ 2 := by
    calc
      (automaticChallengeHeight rho a : ℝ) ≤ automaticHeightBoundConstant rho / eta ^ 2 :=
        automaticChallengeHeight_le_inv_eta_sq hrho hrhoOne heta haOne
      _ = automaticHeightBoundConstant rho * q ^ 2 := by
        dsimp only [q]
        field_simp [ne_of_gt heta]
      _ ≤ C * q ^ 2 := by
        gcongr
        exact automaticHeightBoundConstant_le_envelope rho
  have hT : stageStaircase mu M ≤ C * q ^ 3 := by
    calc
      stageStaircase mu M ≤ automaticMomentBoundConstant rho / eta ^ 3 :=
        automaticStaircaseMoment_le_inv_eta_cube hrho hrhoOne heta haOne
      _ = automaticMomentBoundConstant rho * q ^ 3 := by
        dsimp only [q]
        field_simp [ne_of_gt heta]
      _ ≤ C * q ^ 3 := by
        gcongr
        exact automaticMomentBoundConstant_le_envelope rho
  dsimp only [a, C, q, mu, M] at hC hq htheta0 htheta hmuPos hmu hh hT
  constructor
  · exact hC
  constructor
  · exact hq
  constructor
  · exact htheta0
  constructor
  · exact htheta
  constructor
  · exact hmuPos
  constructor
  · simpa [div_eq_mul_inv] using hmu
  constructor
  · simpa [div_eq_mul_inv] using hh
  · simpa [div_eq_mul_inv] using hT

/-- The automatic closed list constant has a cubic slack envelope. -/
theorem automaticListConstant_le_cubic_slack_envelope {rho eta : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : 1 ≤ n) (hDn : D ≤ n) (hDA : D < A)
    (hD : (D : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A) :
    firstOrderListConstant (agreementIncidenceRatio n D A) D
        (automaticJetDegree rho (firstOrderRateThreshold rho + eta))
        (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) ≤
      automaticListBoundConstant rho * n / eta ^ 3 := by
  obtain ⟨hC, hq, htheta0, htheta, _, hmu, _, hT⟩ :=
    automaticClosedEnvelopeInputs hrho hrhoOne heta haOne hDn hDA hD hA
  let a := firstOrderRateThreshold rho + eta
  let C := automaticRateEnvelopeConstant rho
  let q := 1 / eta
  let mu := automaticJetDegree rho a
  let M := automaticDerivativeCap rho a
  have hmu' : (mu : ℝ) ≤ C * q := by
    simpa only [a, mu, C, q, div_eq_mul_inv, one_mul, inv_pow] using hmu
  have hT' : stageStaircase mu M ≤ C * q ^ 3 := by
    simpa only [a, mu, M, C, q, div_eq_mul_inv, one_mul, inv_pow] using hT
  have hbound := firstOrderListConstant_le_cubic hC hq hn hDn htheta0 htheta hmu' hT'
  dsimp only [a, C, q, mu, M] at hbound ⊢
  unfold automaticListBoundConstant
  field_simp [ne_of_gt heta] at hbound ⊢
  exact hbound

/-- The automatic closed exceptional-set constant has a quintic slack envelope and quadratic
block-length dependence. -/
theorem automaticExceptionConstant_le_quintic_slack_envelope {rho eta : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : 1 ≤ n) (hDn : D ≤ n) (hDA : D < A)
    (hD : (D : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A) :
    firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D
        (automaticChallengeHeight rho (firstOrderRateThreshold rho + eta))
        (automaticJetDegree rho (firstOrderRateThreshold rho + eta))
        (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) ≤
      automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5 := by
  obtain ⟨hC, hq, htheta0, htheta, hmuPos, hmu, hh, hT⟩ :=
    automaticClosedEnvelopeInputs hrho hrhoOne heta haOne hDn hDA hD hA
  let a := firstOrderRateThreshold rho + eta
  let C := automaticRateEnvelopeConstant rho
  let q := 1 / eta
  let mu := automaticJetDegree rho a
  let M := automaticDerivativeCap rho a
  let h := automaticChallengeHeight rho a
  have hmu' : (mu : ℝ) ≤ C * q := by
    simpa only [a, mu, C, q, div_eq_mul_inv, one_mul, inv_pow] using hmu
  have hh' : (h : ℝ) ≤ C * q ^ 2 := by
    simpa only [a, h, C, q, div_eq_mul_inv, one_mul, inv_pow] using hh
  have hT' : stageStaircase mu M ≤ C * q ^ 3 := by
    simpa only [a, mu, M, C, q, div_eq_mul_inv, one_mul, inv_pow] using hT
  have hbound := firstOrderExceptionConstant_le_quintic hC hq hn hDn htheta0 htheta
    hmuPos hmu' hh' hT'
  dsimp only [a, C, q, mu, M, h] at hbound ⊢
  unfold automaticExceptionBoundConstant
  field_simp [ne_of_gt heta] at hbound ⊢
  exact hbound

/-- The public physical-rate guards imply both explicit automatic closed envelopes at once. -/
theorem automaticClosedListAndExceptionBounds {rho eta : ℝ} {n k D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : 1 ≤ n) (hDdef : D = k - 1)
    (hk : (k : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A) :
    firstOrderListConstant (agreementIncidenceRatio n D A) D
          (automaticJetDegree rho (firstOrderRateThreshold rho + eta))
          (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) ≤
        automaticListBoundConstant rho * n / eta ^ 3 ∧
      firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D
          (automaticChallengeHeight rho (firstOrderRateThreshold rho + eta))
          (automaticJetDegree rho (firstOrderRateThreshold rho + eta))
          (automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) ≤
        automaticExceptionBoundConstant rho * n ^ 2 / eta ^ 5 := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : (D : ℝ) ≤ rho * n := automatic_degree_le_rate_mul hDdef hk
  have hrhoN : rho * (n : ℝ) < n := mul_lt_of_lt_one_left hnReal hrhoOne
  have hDnLt : D < n := by exact_mod_cast hD.trans_lt hrhoN
  have hDn : D ≤ n := hDnLt.le
  have haRho : rho < firstOrderRateThreshold rho + eta :=
    (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans (by linarith)
  have hDAReal : (D : ℝ) < A :=
    (hD.trans_lt (mul_lt_mul_of_pos_right haRho hnReal)).trans_le hA
  have hDA : D < A := by exact_mod_cast hDAReal
  exact ⟨automaticListConstant_le_cubic_slack_envelope hrho hrhoOne heta haOne hn hDn hDA hD hA,
    automaticExceptionConstant_le_quintic_slack_envelope hrho hrhoOne heta haOne hn hDn hDA hD hA⟩

end

end ReedSolomon.HiddenDerivative
