/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformGamma

/-!
# Uniform rate-partition margin acceptance tests

Concrete low-rate and high-rate cases for the arbitrary-order base bounds and margins, their
uniform-order specializations, and boundary cases for the small-gap and positive-order hypotheses.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

private theorem order_8192_log_bound :
    3 / (2 * (1 / 5 : ℝ)) ≤ Real.log (8192 : ℝ) := by
  rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
  norm_num
  linarith [Real.log_two_gt_d9]

/-- At gap `1/5` and order `8192`, the arbitrary-order low-rate base bound holds. -/
example :
    Real.exp (3 / 2 - Real.log (40 / 9 : ℝ)) <
      rateGamma (2 * (1 / 5 : ℝ) ^ 2) (1 / 5) 8192 := by
  exact rateGamma_low_base_gt (δ := 1 / 5) (order := 8192) (by norm_num) (by norm_num)
    (by norm_num) order_8192_log_bound

/-- At rate `1/2`, gap `1/5`, and order `8192`, the arbitrary-order high-rate base bound holds. -/
example :
    Real.exp (3 / 2 - Real.log (40 / 9 : ℝ)) <
      rateGamma (1 / 2) (1 / 2 + 1 / 5) 8192 := by
  exact rateGamma_high_base_gt (R := 1 / 2) (δ := 1 / 5) (order := 8192)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    order_8192_log_bound

/-- The uniform order satisfies the low-rate base bound at gap `1/5`. -/
example :
    Real.exp (3 / 2 - Real.log (40 / 9 : ℝ)) <
      rateGamma (2 * (1 / 5 : ℝ) ^ 2) (1 / 5) (uniformDerivativeOrder (1 / 5)) := by
  exact uniformRateGamma_low_base_gt (by norm_num) (by norm_num)

/-- At rate `1/2` and gap `1/5`, the uniform order satisfies the high-rate base bound. -/
example :
    Real.exp (3 / 2 - Real.log (40 / 9 : ℝ)) <
      rateGamma (1 / 2) (1 / 2 + 1 / 5) (uniformDerivativeOrder (1 / 5)) := by
  exact uniformRateGamma_high_base_gt (R := 1 / 2) (δ := 1 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At gap `1/5`, order `8192` gives the low-rate finite-ratio margin. -/
example :
    (151 / 150 : ℝ) <
      rateGamma (2 * (1 / 5 : ℝ) ^ 2) (1 / 5) 8192 * Real.exp (-1 / 1000) := by
  exact rateGamma_low_gt (δ := 1 / 5) (order := 8192) (by norm_num) (by norm_num)
    (by norm_num) order_8192_log_bound

/-- At gap `1/5` and rate `1/2`, order `8192` gives the high-rate finite-ratio margin. -/
example :
    (151 / 150 : ℝ) <
      rateGamma (1 / 2) (1 / 2 + 1 / 5) 8192 * Real.exp (-1 / 1000) := by
  exact rateGamma_high_gt (δ := 1 / 5) (order := 8192) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) order_8192_log_bound

/-- The uniform derivative order reaches the range required by the moment estimate at gap `1/5`.
-/
example : 500 ≤ uniformDerivativeOrder (1 / 5 : ℝ) :=
  uniformDerivativeOrder_ge_500 (by norm_num) (by norm_num)

/-- The low-rate uniform specialization retains the source-shaped margin at gap `1/5`. -/
example :
    (151 / 150 : ℝ) <
      rateGamma (2 * (1 / 5 : ℝ) ^ 2) (1 / 5) (uniformDerivativeOrder (1 / 5)) *
        Real.exp (-1 / 1000) :=
  uniformRateGamma_low_gt (by norm_num) (by norm_num)

/-- The high-rate uniform specialization retains its margin at rate `1/2` and gap `1/5`. -/
example :
    (151 / 150 : ℝ) <
      rateGamma (1 / 2) (1 / 2 + 1 / 5) (uniformDerivativeOrder (1 / 5)) *
        Real.exp (-1 / 1000) :=
  uniformRateGamma_high_gt (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The low-rate margin can fail outside the small-gap range, even when the order satisfies the
logarithmic lower bound: at `δ = 2` and `d = 3`, `3/(2δ) ≤ log d` but `Γ` is below `1`. -/
example :
    3 / (2 * (2 : ℝ)) ≤ Real.log 3 ∧
      ¬ (151 / 150 : ℝ) <
        rateGamma (2 * (2 : ℝ) ^ 2) 2 3 * Real.exp (-1 / 1000) := by
  constructor
  · norm_num
    linarith [Real.log_three_gt_d9]
  · have hgamma : rateGamma (2 * (2 : ℝ) ^ 2) 2 3 < 1 := by
      norm_num [rateGamma]
    have hgammaPos : 0 < rateGamma (2 * (2 : ℝ) ^ 2) 2 3 :=
      rateGamma_pos (by norm_num) (by norm_num)
    have hexp : Real.exp (-1 / 1000 : ℝ) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    have hproduct :
        rateGamma (2 * (2 : ℝ) ^ 2) 2 3 * Real.exp (-1 / 1000) < 1 := by
      calc
        _ ≤ rateGamma (2 * (2 : ℝ) ^ 2) 2 3 * 1 :=
          mul_le_mul_of_nonneg_left hexp.le hgammaPos.le
        _ < 1 := by simpa only [mul_one] using hgamma
    intro h
    linarith

/-- At order `0` the ratio vanishes, so a positive order is necessary for a positive margin. -/
example : rateGamma 1 1 0 = 0 := by
  norm_num [rateGamma]

end ReedSolomon.HiddenDerivative.RatePartition
