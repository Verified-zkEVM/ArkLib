/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.LowRateStationary

/-!
# Low-rate stationary root acceptance tests

The stationary data at a rate where the root is rational, the branch cutoff on both sides, a case
showing the branch condition is needed for `β > 1/2`, and the source-shaped statement of
`rate_lt_firstOrderLowRateThreshold`.
-/

namespace ReedSolomon.HiddenDerivative

/-! ### A rational instance: `ρ = 2 (31/1000)²`, `t = 31/1000`, `u = 1/10` -/

private theorem scale_eq : firstOrderLowRateScale (2 * (31 / 1000) ^ 2) = 31 / 1000 := by
  unfold firstOrderLowRateScale
  rw [show (2 * (31 / 1000 : ℝ) ^ 2) / 2 = (31 / 1000) ^ 2 by ring]
  exact Real.sqrt_sq (by norm_num)

/-- `(1/10)² (1/10 + 3) = 31/1000`, so the stationary root is `1/10`. -/
private theorem u_eq : firstOrderLowRateStationaryU (2 * (31 / 1000) ^ 2) = 1 / 10 :=
  (firstOrderLowRateStationaryU_unique (by norm_num) (by norm_num)
    (by rw [scale_eq]; norm_num [firstOrderStationaryCubic])).symm

private theorem regime : FirstOrderLowRateRegime (2 * (31 / 1000) ^ 2) := by
  unfold FirstOrderLowRateRegime
  rw [scale_eq]
  norm_num

/-- `β = (1/10) / (62/1000) = 50/31`. -/
example : firstOrderLowRateBeta (2 * (31 / 1000) ^ 2) = 50 / 31 := by
  rw [firstOrderLowRateBeta, u_eq, scale_eq]
  norm_num

/-- `a* = (31/1000)(1 + 1/10) = 341/10000`. -/
private theorem threshold_eq :
    firstOrderLowRateThreshold (2 * (31 / 1000) ^ 2) = 341 / 10000 := by
  rw [firstOrderLowRateThreshold_eq_scale_mul_one_add (by norm_num), u_eq, scale_eq]
  norm_num

/-- The margin theorem at this instance for `a = 1/10 > 341/10000`. -/
example : 0 < firstOrderSourceDensity (2 * (31 / 1000) ^ 2) (1 / 10)
      (firstOrderLowRateBeta (2 * (31 / 1000) ^ 2)) -
    firstOrderRankDensity (firstOrderLowRateBeta (2 * (31 / 1000) ^ 2)) :=
  firstOrderLowRate_margin_pos (by norm_num) regime (by rw [threshold_eq]; norm_num)

/-! ### The branch cutoff `11 - 3√13` -/

example : FirstOrderLowRateRegime (1 / 10) := by
  rw [firstOrderLowRateRegime_iff_lt_rateSwitch, firstOrderRateSwitch]
  have : Real.sqrt 13 < 109 / 30 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

example : ¬ FirstOrderLowRateRegime (1 / 5) := by
  rw [firstOrderLowRateRegime_iff_lt_rateSwitch, firstOrderRateSwitch, not_lt]
  have : 18 / 5 < Real.sqrt 13 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

/-- Negative rates are on the branch and below the cutoff. -/
example : FirstOrderLowRateRegime (-1) ∧ (-1 : ℝ) < firstOrderRateSwitch := by
  have h : firstOrderLowRateScale (-1) = 0 := Real.sqrt_eq_zero'.2 (by norm_num)
  refine ⟨by rw [FirstOrderLowRateRegime, h]; norm_num,
    (firstOrderLowRateRegime_iff_lt_rateSwitch _).1 (by rw [FirstOrderLowRateRegime, h]; norm_num)⟩

/-! ### The branch condition is needed for `β > 1/2` -/

/-- At `ρ = 2`, `t = 1` and the root of `u² (u + 3) = 1` is below `1`, so `β = u/2 < 1/2`. -/
example : ¬ 1 / 2 < firstOrderLowRateBeta 2 := by
  have ht : firstOrderLowRateScale 2 = 1 := by
    simp [firstOrderLowRateScale]
  have hcubic := firstOrderLowRateStationaryU_cubic (rho := 2) (by norm_num)
  have hpos := firstOrderLowRateStationaryU_pos (rho := 2) (by norm_num)
  rw [ht, firstOrderStationaryCubic] at hcubic
  rw [firstOrderLowRateBeta, ht, not_lt, div_le_iff₀ (by norm_num)]
  nlinarith

example : ¬ FirstOrderLowRateRegime 2 := by
  simp [FirstOrderLowRateRegime, firstOrderLowRateScale]

/-! ### Source-shaped statement -/

/-- The source statement of `rate_lt_firstOrderLowRateThreshold`, with its extra `ρ < 1`. -/
example {rho : ℝ} (hrho : 0 < rho) (_hrhoOne : rho < 1) (hlow : FirstOrderLowRateRegime rho) :
    rho < firstOrderLowRateThreshold rho :=
  rate_lt_firstOrderLowRateThreshold hrho hlow

/-- The source statement of `firstOrderLowRateRegime_iff_lt_rateSwitch`, with `0 ≤ ρ`. -/
example {rho : ℝ} (_hrho : 0 ≤ rho) :
    FirstOrderLowRateRegime rho ↔ rho < firstOrderRateSwitch :=
  firstOrderLowRateRegime_iff_lt_rateSwitch rho

end ReedSolomon.HiddenDerivative
