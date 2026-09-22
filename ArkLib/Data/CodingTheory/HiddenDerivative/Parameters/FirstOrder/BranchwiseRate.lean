/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.LowRateStationary

/-!
# Branchwise first-order rate parameters

This module joins the low-rate stationary optimizer of `LowRateStationary` to the upper-branch
formula of `RateBound`. The switch is `firstOrderRateSwitch = 11 - 3√13`: below it the threshold
and derivative-degree ratio are the stationary low-rate values, and at or above it they are the
upper-branch closed forms. The threshold depends only on the rate. The derivative-degree ratio is
constant on the low branch and depends on the agreement `a` on the upper branch.

## Main statements

- `firstOrderBranchThreshold`, `firstOrderBranchBeta`: the piecewise threshold and ratio, with
  unfolding lemmas `_eq_low` and `_eq_clean` for each branch.
- `firstOrderBranchBeta_pos`, `firstOrderBranchBeta_lt_agreement_div_rate`: the ratio lies in
  `(0, a/ρ)`.
- `firstOrderBranch_surplus_pos`: above the piecewise threshold, the limiting source density
  exceeds the limiting rank density.

-/
@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The piecewise first-order agreement curve `a₁(rho)`.

Below `firstOrderRateSwitch = 11 - 3*sqrt 13`, this is the low-rate stationary value
`sqrt(rho/2) * (1 + u)`, where the positive `u` satisfies
`u^2 * (u + 3) = sqrt(rho/2)`. At and above the cutoff it is the clean upper-branch formula
`(3*rho + 2*sqrt(rho*(5-rho)*(2-rho))) / (8-rho)`. Headline theorems require a strictly positive
gap above this curve. -/
def firstOrderBranchThreshold (rho : ℝ) : ℝ :=
  -- The strict comparison assigns the cutoff itself to the upper branch.
  if rho < firstOrderRateSwitch then firstOrderLowRateThreshold rho
  else firstOrderRateThreshold rho

/-- The piecewise derivative-degree ratio at a certified agreement `a`: the stationary low-rate
ratio below `firstOrderRateSwitch`, and `firstOrderRateBeta ρ a` at or above it. -/
def firstOrderBranchBeta (rho a : ℝ) : ℝ :=
  if rho < firstOrderRateSwitch then firstOrderLowRateBeta rho
  else firstOrderRateBeta rho a

/-- Below the switch, the piecewise threshold is the low-rate stationary threshold. -/
theorem firstOrderBranchThreshold_eq_low {rho : ℝ} (hlow : rho < firstOrderRateSwitch) :
    firstOrderBranchThreshold rho = firstOrderLowRateThreshold rho := by
  simp [firstOrderBranchThreshold, hlow]

/-- At or above the switch, the piecewise threshold is the upper-branch threshold. -/
theorem firstOrderBranchThreshold_eq_clean {rho : ℝ} (hlow : firstOrderRateSwitch ≤ rho) :
    firstOrderBranchThreshold rho = firstOrderRateThreshold rho := by
  simp [firstOrderBranchThreshold, not_lt.mpr hlow]

/-- Below the switch, the piecewise ratio is the low-rate stationary ratio, independent of `a`. -/
theorem firstOrderBranchBeta_eq_low {rho a : ℝ} (hlow : rho < firstOrderRateSwitch) :
    firstOrderBranchBeta rho a = firstOrderLowRateBeta rho := by
  simp [firstOrderBranchBeta, hlow]

/-- At or above the switch, the piecewise ratio is `3(1 - a) / (2(2 - ρ))`. -/
theorem firstOrderBranchBeta_eq_clean {rho a : ℝ} (hlow : firstOrderRateSwitch ≤ rho) :
    firstOrderBranchBeta rho a = firstOrderRateBeta rho a := by
  simp [firstOrderBranchBeta, not_lt.mpr hlow]

/-- Both branches select a strictly positive derivative-degree ratio. The low branch needs only
`ρ > 0`. The upper branch `3(1 - a) / (2(2 - ρ))` needs `a < 1` and `ρ < 2`; at `a = 1` it is
`0`. -/
theorem firstOrderBranchBeta_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoTwo : rho < 2) (haOne : a < 1) :
    0 < firstOrderBranchBeta rho a := by
  by_cases hlow : rho < firstOrderRateSwitch
  · rw [firstOrderBranchBeta_eq_low hlow]
    exact firstOrderLowRateBeta_pos hrho
  · rw [firstOrderBranchBeta_eq_clean (not_lt.mp hlow)]
    exact firstOrderRateBeta_pos haOne hrhoTwo

/-- The selected derivative cap lies strictly inside the coefficient cutoff `a/ρ`. The threshold
hypothesis is used on both branches: on the upper branch it gives `ρ < a` through
`rate_lt_firstOrderRateThreshold`, which needs `0 < ρ < 1`. -/
theorem firstOrderBranchBeta_lt_agreement_div_rate {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderBranchThreshold rho < a) :
    firstOrderBranchBeta rho a < a / rho := by
  by_cases hlow : rho < firstOrderRateSwitch
  · rw [firstOrderBranchBeta_eq_low hlow]
    have hthreshold : firstOrderLowRateThreshold rho < a := by
      simpa [firstOrderBranchThreshold_eq_low hlow] using ha
    exact (firstOrderLowRateBeta_lt_threshold_div_rate hrho).trans
      (div_lt_div_of_pos_right hthreshold hrho)
  · have hthreshold : firstOrderRateThreshold rho < a := by
      simpa [firstOrderBranchThreshold_eq_clean (not_lt.mp hlow)] using ha
    have hRa : rho < a := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans hthreshold
    rw [firstOrderBranchBeta_eq_clean (not_lt.mp hlow)]
    exact firstOrderRateBeta_lt_agreement_div_rate hrho (by linarith) hRa.le

/-- Above the full piecewise curve, the limiting source density strictly exceeds the limiting
rank density at the selected ratio. The upper branch uses `a < 1` and `0 < ρ < 1` through
`firstOrderRate_surplus_pos`; the low branch uses only `ρ > 0` and the threshold. -/
theorem firstOrderBranch_surplus_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderBranchThreshold rho < a) (haOne : a < 1) :
    firstOrderRankDensity (firstOrderBranchBeta rho a) <
      firstOrderSourceDensity rho a (firstOrderBranchBeta rho a) := by
  by_cases hlow : rho < firstOrderRateSwitch
  · have hregime : FirstOrderLowRateRegime rho :=
      (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
    have hthreshold : firstOrderLowRateThreshold rho < a := by
      simpa [firstOrderBranchThreshold_eq_low hlow] using ha
    rw [firstOrderBranchBeta_eq_low hlow]
    exact sub_pos.mp (firstOrderLowRate_margin_pos hrho hregime hthreshold)
  · have hthreshold : firstOrderRateThreshold rho < a := by
      simpa [firstOrderBranchThreshold_eq_clean (not_lt.mp hlow)] using ha
    have hRa : rho < a := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans hthreshold
    rw [firstOrderBranchBeta_eq_clean (not_lt.mp hlow)]
    exact firstOrderRate_surplus_pos hrho hRa haOne hthreshold

end

end ReedSolomon.HiddenDerivative
