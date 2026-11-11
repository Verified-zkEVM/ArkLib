/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow

/-!
# Concrete exponential and real-power bounds

Instances of the two logarithmic exponential estimates, the tangent bound, and the real-power
identity.
-/

/-- For `a = 2`, `b = c = 1`, and `x = 4`, the logarithmic bound is attained. -/
example : Real.exp ((Real.log 4 + 1) / 2 + 1) ≤
    Real.exp (1 / 2 + 1) * (4 : ℝ) ^ ((1 : ℝ) / 2) :=
  Real.exp_le_exp_mul_rpow_of_le_log_add (a := 2) (b := 1) (c := 1)
    (E := (Real.log 4 + 1) / 2 + 1) (H := Real.log 4 + 1) (x := 4)
    (by norm_num) (by norm_num) le_rfl le_rfl

/-- With `c = 2` and `ρ = 1`, the tangent bound gives `2 * exp 1 ≤ exp 2`. -/
example : Real.exp 1 * 2 ≤ 1 * Real.exp (2 / 1) :=
  Real.exp_one_mul_le_mul_exp_div 2 one_pos

/-- At `x = 9`, `a = 2`, the real-power quotient has its stated exponential form. -/
example : (9 : ℝ) ^ ((1 : ℝ) / 2) / 9 =
    (Real.exp (Real.log 9 * ((2 - 1) / 2)))⁻¹ :=
  Real.rpow_one_div_div_self (by norm_num) (by norm_num)
