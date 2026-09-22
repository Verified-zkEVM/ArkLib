/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.SpecificLimits.GeometricBounds

/-!
# Geometric and exponential bounds

At `q = 1/2` and `m = 2` the closed form gives `(1/2 + 2/4) (1/2)^2 = 1/4`, and the two finite
sums `3/4` and `1` are below their limits `1` and `2`. The exponential ratio bounds hold at a
negative argument, so they need no sign condition on `x`. The finite exponential sum fails at
`x = 0`, and the power bound fails at `W = 0` and when `W + y < 0`, so those hypotheses are
needed. The ceiling bound is checked at `b = 0` and at a value where it is attained.
-/

open Finset

/-- The closed form at `q = 1/2`, `m = 2`. -/
example : (∑ j ∈ range 2, ((j + 1 : ℕ) : ℚ) * (1 / 2) ^ (j + 1)) * (1 - 1 / 2) ^ 2 =
    1 / 2 - (2 + 1) * (1 / 2) ^ (2 + 1) + 2 * (1 / 2) ^ (2 + 2) := by
  exact_mod_cast sum_range_natCast_succ_mul_pow_succ_mul_one_sub_sq (1 / 2 : ℚ) 2

/-- At `q = 1/2` the sum is `1/2 + 1/4 = 3/4`, below `q / (1 - q) = 1`. -/
example : ∑ j ∈ range 2, (1 / 2 : ℚ) ^ (j + 1) = 3 / 4 ∧
    ∑ j ∈ range 2, (1 / 2 : ℚ) ^ (j + 1) ≤ (1 / 2) / (1 - 1 / 2) :=
  ⟨by norm_num [sum_range_succ],
    sum_range_pow_succ_le_div_one_sub 2 (by norm_num) (by norm_num)⟩

/-- At `q = 1/2` the weighted sum is `1/2 + 2/4 = 1`, below `q / (1 - q)^2 = 2`. -/
example : ∑ j ∈ range 2, ((j + 1 : ℕ) : ℚ) * (1 / 2) ^ (j + 1) = 1 ∧
    ∑ j ∈ range 2, ((j + 1 : ℕ) : ℚ) * (1 / 2) ^ (j + 1) ≤ (1 / 2) / (1 - 1 / 2) ^ 2 :=
  ⟨by norm_num [sum_range_succ],
    sum_range_natCast_succ_mul_pow_succ_le 2 (by norm_num) (by norm_num)⟩

/-- No sign hypothesis on `x`: the ratio bound at `x = -1`. -/
example : Real.exp 1 / (1 - Real.exp 1) ≤ -1 := by
  simpa using Real.exp_neg_div_one_sub_exp_neg_le (-1)

/-- The squared ratio bound at `x = -1`. -/
example : Real.exp 1 / (1 - Real.exp 1) ^ 2 ≤ 1 := by
  simpa using Real.exp_neg_div_one_sub_exp_neg_sq_le (-1)

/-- The finite exponential bound needs `0 < x`: at `x = 0`, `m = 1`, `a = b = 1` the sum is `2`
while `a / x^2 + b / x` is `0`. -/
example : ¬ (∑ j ∈ range 1, (1 * ((j + 1 : ℕ) : ℝ) + 1) * Real.exp (-0) ^ (j + 1) ≤
    1 / (0 : ℝ) ^ 2 + 1 / 0) := by
  norm_num

/-- The power bound needs `0 < W`: at `W = 0`, `y = 1`, `n = 1` it would read `1 ≤ 0`. -/
example : ¬ ((0 + 1 : ℝ) ^ 1 ≤ 0 ^ 1 * Real.exp (1 * (1 / 0))) := by
  norm_num

/-- The power bound needs `0 ≤ W + y`: at `W = 1`, `y = -3`, `n = 2` it would read
`4 ≤ exp (-6)`. -/
example : ¬ ((1 + -3 : ℝ) ^ 2 ≤ 1 ^ 2 * Real.exp (2 * (-3 / 1))) := by
  intro h
  have he : Real.exp (-6) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  norm_num at h
  linarith

/-- With `b = 0` the ceiling bound reads `0 ≤ 1`. -/
example (a : ℕ) : ((a ⌈/⌉ 0 : ℕ) : ℚ) ≤ (a : ℚ) / (0 : ℕ) + 1 :=
  Nat.cast_ceilDiv_le_div_add_one a 0

/-- The ceiling bound is nearly tight: `⌈1 / 3⌉ = 1 ≤ 1/3 + 1`. -/
example : ((1 ⌈/⌉ 3 : ℕ) : ℚ) = 1 ∧ ((1 ⌈/⌉ 3 : ℕ) : ℚ) ≤ 1 / 3 + 1 := by
  refine ⟨by norm_num [Nat.ceilDiv_eq_add_pred_div], ?_⟩
  exact_mod_cast Nat.cast_ceilDiv_le_div_add_one (K := ℚ) 1 3
