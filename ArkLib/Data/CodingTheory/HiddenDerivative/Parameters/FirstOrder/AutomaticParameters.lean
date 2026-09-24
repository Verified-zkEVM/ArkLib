/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RateBound
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Finite parameters from the first-order rate surplus

For rate `rho` and requested agreement `a` above the first-order threshold, this module tunes the
agreement away from one, chooses the maximizing derivative ratio, and rounds the positive density
surplus into a finite interpolation multiplicity. The source and rank counts reuse the generic
rounded-count API.

## Main statements

* `automaticMultiplicity`, `automaticDerivativeCap`, and `automaticJetDegree` define the rounded
  interpolation parameters.
* `automaticSourceCount` and `automaticRankCount` define the finite source and rank counts.
* `automaticSurplusQuarter_le_source_sub_rank` gives a positive finite surplus after rounding.
* `automaticChallengeHeight` is defined from the resulting source-to-rank quotient.

## References

* [DKT26]
-/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- The tuned agreement, bounded by the requested agreement and the midpoint to one. -/
def automaticAgreement (rho a : ℝ) : ℝ :=
  min a ((1 + firstOrderRateThreshold rho) / 2)

/-- The maximizing derivative ratio at the tuned agreement. -/
def automaticBeta (rho a : ℝ) : ℝ :=
  firstOrderRateBeta rho (automaticAgreement rho a)

/-- The normalized source-minus-rank density bracket at the tuned agreement. -/
def automaticGapBracket (rho a : ℝ) : ℝ :=
  firstOrderCleanExpression rho (automaticAgreement rho a) - 1

/-- The positive normalized source-minus-rank density gap. -/
def automaticSurplus (rho a : ℝ) : ℝ :=
  automaticBeta rho a * automaticGapBracket rho a / 2

/-- The interpolation multiplicity obtained by rounding up four times the inverse surplus. -/
def automaticMultiplicity (rho a : ℝ) : ℕ :=
  ⌈4 / automaticSurplus rho a⌉₊

/-- The raw derivative-degree cap obtained by rounding down the optimized ratio. -/
def automaticDerivativeCapRaw (rho a : ℝ) : ℕ :=
  ⌊automaticBeta rho a * automaticMultiplicity rho a⌋₊

/-- The rounded total jet-degree cap at the tuned agreement. -/
def automaticJetDegree (rho a : ℝ) : ℕ :=
  ⌈automaticMultiplicity rho a * automaticAgreement rho a / rho⌉₊

/-- The derivative-degree cap, normalized to the total jet-degree cap. -/
def automaticDerivativeCap (rho a : ℝ) : ℕ :=
  min (automaticDerivativeCapRaw rho a) (automaticJetDegree rho a)

/-- The source count at the tuned agreement and normalized automatic caps. -/
def automaticSourceCount (rho a : ℝ) : ℝ :=
  firstOrderSourceCount rho (automaticAgreement rho a) (automaticMultiplicity rho a)
    (automaticDerivativeCap rho a) (automaticJetDegree rho a)

/-- The local rank count at the normalized automatic caps. -/
def automaticRankCount (rho a : ℝ) : ℕ :=
  firstOrderRankCount (automaticMultiplicity rho a) (automaticDerivativeCap rho a)

/-- The challenge height from the rounded source count and local rank count. -/
def automaticChallengeHeight (rho a : ℝ) : ℕ :=
  max 1 ⌊(automaticRankCount rho a : ℝ) * automaticJetDegree rho a /
    (automaticSourceCount rho a - automaticRankCount rho a)⌋₊

/-- The source density at the tuned agreement and optimized derivative ratio. -/
def automaticSourceDensity (rho a : ℝ) : ℝ :=
  firstOrderSourceDensity rho (automaticAgreement rho a) (automaticBeta rho a)

/-- The cubic rank-density envelope at the optimized derivative ratio. -/
def automaticRankDensityEnvelope (rho a : ℝ) : ℝ :=
  firstOrderRankCubicEnvelope (automaticBeta rho a)

/-- The tuned agreement equals the smaller of the requested agreement and the safe midpoint. -/
theorem automaticAgreement_eq_min (rho a : ℝ) :
    automaticAgreement rho a = min a ((1 + firstOrderRateThreshold rho) / 2) := rfl

/-- The tuned agreement lies strictly above the first-order threshold. -/
theorem automatic_threshold_lt_agreement {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) :
    firstOrderRateThreshold rho < automaticAgreement rho a := by
  rw [automaticAgreement_eq_min]
  apply lt_min ha
  have hthreshold : firstOrderRateThreshold rho < 1 := by
    exact (firstOrderRateThreshold_lt_sqrt hrho hrhoOne).trans
      (by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hrho.le hrhoOne)
  linarith

/-- The tuned agreement is at most the requested agreement. -/
theorem automaticAgreement_le (rho a : ℝ) : automaticAgreement rho a ≤ a :=
  (automaticAgreement_eq_min rho a).symm ▸ min_le_left _ _

/-- The tuned agreement is strictly below one when the requested agreement is. -/
theorem automaticAgreement_lt_one {rho a : ℝ} (haOne : a < 1) :
    automaticAgreement rho a < 1 :=
  (automaticAgreement_le rho a).trans_lt haOne

/-- The tuned agreement remains strictly above the physical rate. -/
theorem rho_lt_automaticAgreement {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) :
    rho < automaticAgreement rho a :=
  (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans
    (automatic_threshold_lt_agreement hrho hrhoOne ha)

/-- The optimized derivative ratio is positive in the automatic range. -/
theorem automaticBeta_pos {rho a : ℝ} (_hrho : 0 < rho) (hrhoOne : rho < 1)
    (_ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    0 < automaticBeta rho a := by
  unfold automaticBeta
  exact firstOrderRateBeta_pos (automaticAgreement_lt_one haOne) (by linarith)

/-- The optimized derivative ratio is strictly below `3/4` in the automatic range. -/
theorem automaticBeta_lt_three_four {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (_haOne : a < 1) :
    automaticBeta rho a < 3 / 4 := by
  unfold automaticBeta
  apply firstOrderRateBeta_lt_three_four (by linarith)
  have hρa := rho_lt_automaticAgreement hrho hrhoOne ha
  exact hρa.trans (by linarith)

/-- The optimized derivative ratio is below the total-degree cutoff ratio. -/
theorem automaticBeta_lt_agreement_div_rate {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (_haOne : a < 1) :
    automaticBeta rho a < automaticAgreement rho a / rho := by
  unfold automaticBeta
  exact firstOrderRateBeta_lt_agreement_div_rate hrho (by linarith)
    (rho_lt_automaticAgreement hrho hrhoOne ha).le

/-- The normalized automatic density surplus is positive above the first-order threshold. -/
theorem automaticSurplus_pos {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    0 < automaticSurplus rho a := by
  have hbeta := automaticBeta_pos hrho hrhoOne ha haOne
  have hclean := firstOrderCleanExpression_gt_one hrho hrhoOne
    (automatic_threshold_lt_agreement hrho hrhoOne ha)
  unfold automaticSurplus automaticGapBracket
  positivity

/-- The multiplicity choice provides `m * S ≥ 4`. -/
theorem four_le_automaticMultiplicity_mul_surplus {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    4 ≤ (automaticMultiplicity rho a : ℝ) * automaticSurplus rho a := by
  have hsurplus := automaticSurplus_pos hrho hrhoOne ha haOne
  have hceil : 4 / automaticSurplus rho a ≤ (automaticMultiplicity rho a : ℝ) := by
    unfold automaticMultiplicity
    exact Nat.le_ceil _
  have hceil' := (div_le_iff₀ hsurplus).mp hceil
  nlinarith

/-- The literal automatic multiplicity is positive. -/
theorem automaticMultiplicity_pos {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    0 < automaticMultiplicity rho a := by
  unfold automaticMultiplicity
  apply Nat.ceil_pos.mpr
  exact div_pos (by norm_num) (automaticSurplus_pos hrho hrhoOne ha haOne)

/-- The raw derivative cap is at most the rounded total jet-degree cap. -/
theorem automaticDerivativeCapRaw_le_jetDegree {rho a : ℝ} (hrho : 0 < rho)
    (hrhoOne : rho < 1) (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    automaticDerivativeCapRaw rho a ≤ automaticJetDegree rho a := by
  have hbeta := automaticBeta_lt_agreement_div_rate hrho hrhoOne ha haOne
  have hm : 0 ≤ (automaticMultiplicity rho a : ℝ) := Nat.cast_nonneg _
  have hcut : automaticBeta rho a * automaticMultiplicity rho a ≤
      automaticMultiplicity rho a * automaticAgreement rho a / rho := by
    calc
      automaticBeta rho a * automaticMultiplicity rho a ≤
          (automaticAgreement rho a / rho) * automaticMultiplicity rho a :=
        mul_le_mul_of_nonneg_right hbeta.le hm
      _ = automaticMultiplicity rho a * automaticAgreement rho a / rho := by ring
  have hraw : (automaticDerivativeCapRaw rho a : ℝ) ≤
      automaticBeta rho a * automaticMultiplicity rho a := by
    unfold automaticDerivativeCapRaw
    exact Nat.floor_le (mul_nonneg
      (automaticBeta_pos hrho hrhoOne ha haOne).le (Nat.cast_nonneg _))
  have hceil : automaticMultiplicity rho a * automaticAgreement rho a / rho ≤
      (automaticJetDegree rho a : ℝ) := by
    unfold automaticJetDegree
    exact Nat.le_ceil _
  exact_mod_cast hraw.trans (hcut.trans hceil)

/-- In the automatic range, the normalized derivative cap equals the raw cap. -/
theorem automaticDerivativeCap_eq_raw {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    automaticDerivativeCap rho a = automaticDerivativeCapRaw rho a := by
  unfold automaticDerivativeCap
  exact min_eq_left (automaticDerivativeCapRaw_le_jetDegree hrho hrhoOne ha haOne)

/-- The source count equals the count using the raw derivative cap. -/
theorem automaticSourceCount_eq_raw {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    automaticSourceCount rho a =
      firstOrderSourceCount rho (automaticAgreement rho a) (automaticMultiplicity rho a)
        (automaticDerivativeCapRaw rho a) (automaticJetDegree rho a) := by
  rw [automaticSourceCount, automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]

/-- The rank count equals the count using the raw derivative cap. -/
theorem automaticRankCount_eq_raw {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    automaticRankCount rho a =
      firstOrderRankCount (automaticMultiplicity rho a) (automaticDerivativeCapRaw rho a) := by
  rw [automaticRankCount, automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]

/-- The automatic rank count is bounded by the cubic density and its rounding error. -/
theorem automaticRankCount_le_densityEnvelope_add_rounding {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    (automaticRankCount rho a : ℝ) ≤
      (automaticMultiplicity rho a : ℝ) ^ 3 * automaticRankDensityEnvelope rho a +
        3 * automaticMultiplicity rho a ^ 2 := by
  rw [automaticRankCount_eq_raw hrho hrhoOne ha haOne, automaticRankDensityEnvelope]
  exact firstOrderRankCount_floor_le (automaticMultiplicity rho a)
    (automaticBeta_pos hrho hrhoOne ha haOne).le
    (automaticBeta_lt_three_four hrho hrhoOne ha haOne).le

/-- The rounded source count dominates the continuous source-density lower bound. -/
theorem automaticSourceDensity_mul_cube_le_sourceCount {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    (automaticMultiplicity rho a : ℝ) ^ 3 * automaticSourceDensity rho a ≤
      automaticSourceCount rho a := by
  rw [automaticSourceCount_eq_raw hrho hrhoOne ha haOne, automaticSourceDensity]
  apply cube_mul_sourceDensity_le_firstOrderSourceCount hrho
    (rho_lt_automaticAgreement hrho hrhoOne ha).le
    (automaticBeta_pos hrho hrhoOne ha haOne).le
    (automaticBeta_lt_agreement_div_rate hrho hrhoOne ha haOne).le
  unfold automaticJetDegree
  exact Nat.floor_le_ceil _

/-- The source-density gap equals the displayed automatic surplus. -/
theorem automatic_sourceDensity_sub_rankDensityEnvelope {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (_ha : firstOrderRateThreshold rho < a) (_haOne : a < 1) :
    automaticSourceDensity rho a - automaticRankDensityEnvelope rho a =
      automaticSurplus rho a := by
  have hfactor := firstOrderSourceDensity_sub_cubicEnvelope rho
    (automaticAgreement rho a)
    (firstOrderRateBeta rho (automaticAgreement rho a)) (ne_of_gt hrho)
  have hbracket := firstOrderRateBeta_bracket rho (automaticAgreement rho a)
    (ne_of_gt hrho) (by linarith)
  change firstOrderSourceDensity rho (automaticAgreement rho a)
      (firstOrderRateBeta rho (automaticAgreement rho a)) -
      firstOrderRankCubicEnvelope (firstOrderRateBeta rho (automaticAgreement rho a)) =
    firstOrderRateBeta rho (automaticAgreement rho a) *
      (firstOrderCleanExpression rho (automaticAgreement rho a) - 1) / 2
  rw [hfactor, hbracket]
  ring

/-- The choice `m = ceil(4/S)` absorbs the finite rank rounding loss. -/
theorem automatic_rounding_loss_bound {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    (automaticMultiplicity rho a : ℝ) ^ 3 * automaticSurplus rho a -
        3 * automaticMultiplicity rho a ^ 2 ≥
      (automaticMultiplicity rho a : ℝ) ^ 3 * automaticSurplus rho a / 4 := by
  have hfour := four_le_automaticMultiplicity_mul_surplus hrho hrhoOne ha haOne
  have hm : 0 ≤ (automaticMultiplicity rho a : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg (sq_nonneg (automaticMultiplicity rho a : ℝ))
    (sub_nonneg.mpr hfour)]

/-- The finite source-minus-rank gap retains at least one quarter of the density surplus. -/
theorem automaticSurplusQuarter_le_source_sub_rank {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    (automaticMultiplicity rho a : ℝ) ^ 3 * automaticSurplus rho a / 4 ≤
      automaticSourceCount rho a - automaticRankCount rho a := by
  have hfinite := cube_mul_densityGap_sub_le_sourceCount_sub_rankCount
    hrho (rho_lt_automaticAgreement hrho hrhoOne ha).le
    (automaticBeta_pos hrho hrhoOne ha haOne).le
    (automaticBeta_lt_three_four hrho hrhoOne ha haOne).le
    (automaticBeta_lt_agreement_div_rate hrho hrhoOne ha haOne).le
    (m := automaticMultiplicity rho a) (mu := automaticJetDegree rho a)
    (by unfold automaticJetDegree; exact Nat.floor_le_ceil _)
  have hfiniteRaw := hfinite
  change (automaticMultiplicity rho a : ℝ) ^ 3 *
      (automaticSourceDensity rho a - automaticRankDensityEnvelope rho a) -
      3 * (automaticMultiplicity rho a : ℝ) ^ 2 ≤
    firstOrderSourceCount rho (automaticAgreement rho a) (automaticMultiplicity rho a)
        (automaticDerivativeCapRaw rho a) (automaticJetDegree rho a) -
      firstOrderRankCount (automaticMultiplicity rho a) (automaticDerivativeCapRaw rho a)
    at hfiniteRaw
  have hgap := automatic_sourceDensity_sub_rankDensityEnvelope hrho hrhoOne ha haOne
  rw [← automaticSourceCount_eq_raw hrho hrhoOne ha haOne,
    ← automaticRankCount_eq_raw hrho hrhoOne ha haOne, hgap] at hfiniteRaw
  exact (automatic_rounding_loss_bound hrho hrhoOne ha haOne).trans hfiniteRaw

/-- The finite source count strictly exceeds the local rank count. -/
theorem automaticRankCount_lt_sourceCount {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    (automaticRankCount rho a : ℝ) < automaticSourceCount rho a := by
  have hgap := automaticSurplusQuarter_le_source_sub_rank hrho hrhoOne ha haOne
  have hpos := automaticSurplus_pos hrho hrhoOne ha haOne
  have hmpos : 0 < automaticMultiplicity rho a :=
    automaticMultiplicity_pos hrho hrhoOne ha haOne
  have hmargin : 0 <
      (automaticMultiplicity rho a : ℝ) ^ 3 * automaticSurplus rho a / 4 := by
    positivity
  linarith

/-- The denominator of the automatic challenge-height quotient is positive. -/
theorem automaticChallengeDenominator_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    0 < automaticSourceCount rho a - automaticRankCount rho a :=
  sub_pos.mpr (automaticRankCount_lt_sourceCount hrho hrhoOne ha haOne)

/-- The challenge height is the maximum of one and the floored source-to-rank quotient. -/
theorem automaticChallengeHeight_eq (rho a : ℝ) :
    automaticChallengeHeight rho a =
      max 1 ⌊(automaticRankCount rho a : ℝ) * automaticJetDegree rho a /
        (automaticSourceCount rho a - automaticRankCount rho a)⌋₊ := rfl

/-- The rounded total jet-degree cap is positive. -/
theorem automaticJetDegree_pos {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderRateThreshold rho < a) (haOne : a < 1) :
    0 < automaticJetDegree rho a := by
  unfold automaticJetDegree
  apply Nat.ceil_pos.mpr
  have ha0 : 0 < automaticAgreement rho a :=
    hrho.trans (rho_lt_automaticAgreement hrho hrhoOne ha)
  exact div_pos
    (mul_pos (by exact_mod_cast automaticMultiplicity_pos hrho hrhoOne ha haOne) ha0) hrho

/-- The physical degree bound follows from `D = k - 1` and the rate bound on `k`. -/
theorem automatic_degree_le_rate_mul {rho : ℝ} {n k D : ℕ} (hDdef : D = k - 1)
    (hk : (k : ℝ) ≤ rho * n) :
    (D : ℝ) ≤ rho * n := by
  rw [hDdef]
  exact (show ((k - 1 : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.sub_le k 1).trans hk

end

end ReedSolomon.HiddenDerivative
