/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow

/-!
# Concrete exponential and real-power bounds

Instances of the exponential estimates, the three numerical bounds, and the real-power identity.
-/

/-- At `a = x = 1` and `b = c = H = E = 0`, the logarithmic real-power bound is an equality. -/
example : Real.exp 0 ≤ Real.exp (0 / 1 + 0) * (1 : ℝ) ^ ((1 : ℝ) / 1) :=
  Real.exp_le_exp_mul_rpow_of_le_log_add (a := 1) (b := 0) (c := 0) (E := 0)
    (H := 0) (x := 1) (by positivity) (by positivity) (by simp) (by simp)

/-- At `a = x = 1` and `b = c = H = E = 0`, the weakened logarithmic bound is an equality. -/
example : Real.exp 0 ≤ Real.exp (0 + 0) * (1 : ℝ) ^ ((1 : ℝ) / 1) :=
  Real.exp_le_exp_add_mul_rpow_of_le_log_add (a := 1) (b := 0) (c := 0) (E := 0)
    (H := 0) (x := 1) (by simp) (by simp) (by positivity) (by simp) (by simp)

/-- The form `exp (3 / 5 + 1 / 100) < 37 / 20`. -/
example : Real.exp (3 / 5 + 1 / 100) < 37 / 20 := by
  simpa only [show (3 / 5 + 1 / 100 : ℝ) = 61 / 100 by norm_num] using
    Real.exp_sixtyOne_div_hundred_lt

/-- `48000 < exp (54 / 5)`. -/
example : (48000 : ℝ) < Real.exp (54 / 5) := Real.fortyEightThousand_lt_exp_fiftyFour_div_five

/-- `11 / 4 < exp (81 / 80)`. -/
example : (11 / 4 : ℝ) < Real.exp (81 / 80) := Real.elevenFourths_lt_exp_eightyOne_div_eighty

/-- With `c = -1` and `ρ = 1`, the tangent bound reads `-exp 1 ≤ exp (-1)`. -/
example : Real.exp 1 * (-1) ≤ 1 * Real.exp (-1 / 1) :=
  Real.exp_one_mul_le_mul_exp_div (-1) one_pos

/-- At `x = 9`, `a = 2`: `x ^ (1 / a) / x = 1 / 3`. -/
example : (Real.exp (Real.log 9 * ((2 - 1) / 2)))⁻¹ = 1 / 3 := by
  have hsqrt : (9 : ℝ) ^ ((1 : ℝ) / 2) = 3 := by
    rw [← Real.sqrt_eq_rpow, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← Real.rpow_one_div_div_self (by norm_num) (by norm_num), hsqrt]
  norm_num
