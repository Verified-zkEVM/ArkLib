/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.SpecificLimits.GeometricBounds

/-!
# Concrete geometric and exponential bounds

Finite geometric sums, exponential ratio bounds, a power estimate, and a natural ceiling bound.
-/

open Finset

/-- The closed form of the weighted geometric sum at `q = 1 / 2`, `m = 2`. -/
example : (∑ j ∈ range 2, ((j + 1 : ℕ) : ℚ) * (1 / 2) ^ (j + 1)) * (1 - 1 / 2) ^ 2 =
    1 / 2 - (2 + 1) * (1 / 2) ^ (2 + 1) + 2 * (1 / 2) ^ (2 + 2) := by
  exact_mod_cast sum_range_natCast_succ_mul_pow_succ_mul_one_sub_sq (1 / 2 : ℚ) 2

/-- At `q = 1 / 2`, the finite geometric sum `3 / 4` is below `q / (1 - q) = 1`. -/
example : ∑ j ∈ range 2, (1 / 2 : ℚ) ^ (j + 1) = 3 / 4 ∧
    ∑ j ∈ range 2, (1 / 2 : ℚ) ^ (j + 1) ≤ (1 / 2) / (1 - 1 / 2) :=
  ⟨by norm_num [sum_range_succ],
    sum_range_pow_succ_le_div_one_sub 2 (by norm_num) (by norm_num)⟩

/-- At `q = 1 / 2`, the weighted sum `1` is below `q / (1 - q)^2 = 2`. -/
example : ∑ j ∈ range 2, ((j + 1 : ℕ) : ℚ) * (1 / 2) ^ (j + 1) = 1 ∧
    ∑ j ∈ range 2, ((j + 1 : ℕ) : ℚ) * (1 / 2) ^ (j + 1) ≤ (1 / 2) / (1 - 1 / 2) ^ 2 :=
  ⟨by norm_num [sum_range_succ],
    sum_range_natCast_succ_mul_pow_succ_le 2 (by norm_num) (by norm_num)⟩

/-- The exponential ratio bound at `x = -1`. -/
example : Real.exp 1 / (1 - Real.exp 1) ≤ -1 := by
  simpa using Real.exp_neg_div_one_sub_exp_neg_le (-1)

/-- The squared exponential ratio bound at `x = -1`. -/
example : Real.exp 1 / (1 - Real.exp 1) ^ 2 ≤ 1 := by
  simpa using Real.exp_neg_div_one_sub_exp_neg_sq_le (-1)

/-- The power estimate at `W = y = 1`, `n = 2`. -/
example : (1 + 1 : ℝ) ^ 2 ≤ 1 ^ 2 * Real.exp (2 * (1 / 1)) := by
  simpa using Real.add_pow_le_pow_mul_exp 2 (W := 1) (y := 1) (by norm_num) (by norm_num)

/-- The ceiling bound at `a = 1`, `b = 3`, where `⌈1 / 3⌉ = 1`. -/
example : ((1 ⌈/⌉ 3 : ℕ) : ℚ) = 1 ∧ ((1 ⌈/⌉ 3 : ℕ) : ℚ) ≤ 1 / 3 + 1 := by
  refine ⟨by norm_num [Nat.ceilDiv_eq_add_pred_div], ?_⟩
  exact_mod_cast Nat.cast_ceilDiv_le_div_add_one (K := ℚ) 1 3
