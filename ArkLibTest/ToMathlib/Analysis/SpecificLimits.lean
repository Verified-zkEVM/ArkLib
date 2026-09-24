/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.SpecificLimits.GeometricBounds

/-!
# Concrete geometric and exponential bounds

Finite geometric sums, exponential ratio bounds, agreement-gap estimates, a power estimate, and a
natural ceiling bound.
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

/-- For `n = K = A = 2`, a gap of `1/2` bounds the geometric ratio by `16`. -/
example :
    ((2 * (1 + 2 * 2 * (2 - 1)) : ℕ) : ℝ) / ((2 - 1 + 1 : ℕ) : ℝ) ≤
      (2 * 2 / (1 / 2 : ℝ)) * 2 := by
  apply agreementGap_geometricRatio_le (F := ℝ) (n := 2) (k := 1) (A := 2) (K := 2)
    (ν := 2) (δ := 1 / 2)
  all_goals norm_num

/-- A rational count of `20` meets the geometric premise and the resulting real bound. -/
example :
    (20 : ℝ) ≤ 4 * (1 : ℝ) ^ 2 * (4 * 1 / (1 / 2 : ℝ)) ^ 1 * 2 ^ 1 := by
  have h := geometricCount_le_of_agreementGap (F := ℝ) (n := 2) (k := 1) (A := 2) (K := 2)
    (ν := 2) (m := 1) (d := 1) (L := 20) (δ := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
