/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.ExponentialStaircase
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Acceptance cases for the exponential staircase bound

A one-term instance, the empty sum, and the necessity of `0 ≤ c` and `0 < t`.
-/

/-- At `m = 1`, `c = 0`, `t = 1` the sum is the single term `1`, and the bound gives
`1 ≤ exp 1 * 2`. -/
example : (1 : ℝ) ≤ Real.exp 1 * 2 := by
  have h := Real.sum_staircase_mul_exp_le 1 (c := 0) (t := 1) le_rfl one_pos
  norm_num at h
  linarith

/-- At `m = 0` the sum is empty and the bound is `0 ≤ (c + 1) / t + 1 / t ^ 2`. -/
example (c t : ℝ) (hc : 0 ≤ c) (ht : 0 < t) : 0 ≤ (c + 1) / t + 1 / t ^ 2 := by
  simpa using Real.sum_staircase_mul_exp_le 0 hc ht

/-- `0 < t` is needed: at `t = 0`, `m = 1`, `c = 0` the left side is `1` and the right side is
`0`. -/
example : ¬ ((∑ s ∈ Finset.range 1, (((1 : ℕ) : ℝ) - s + 0) * Real.exp (0 * s)) ≤
    Real.exp (0 * ((1 : ℕ) : ℝ)) * ((0 + 1) / 0 + 1 / 0 ^ 2)) := by
  norm_num

/-- `0 ≤ c` is needed: at `m = 1`, `t = 1`, `c = -10` the left side is `-9` and the right side is
`-8 * exp 1 < -9`. -/
example : ¬ ((∑ s ∈ Finset.range 1, (((1 : ℕ) : ℝ) - s + (-10)) * Real.exp (1 * s)) ≤
    Real.exp (1 * ((1 : ℕ) : ℝ)) * ((-10 + 1) / 1 + 1 / 1 ^ 2)) := by
  have he := Real.exp_one_gt_d9
  norm_num
  linarith
