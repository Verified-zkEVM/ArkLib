/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.ExponentialStaircase

/-!
# Exponential staircase bound

A one-term instance of the exponential staircase estimate.
-/

/-- At `m = 1`, `c = 0`, `t = 1` the sum is `1`, and the bound gives `1 ≤ exp 1 * 2`. -/
example : (1 : ℝ) ≤ Real.exp 1 * 2 := by
  have h := Real.sum_staircase_mul_exp_le 1 (c := 0) (t := 1) le_rfl one_pos
  norm_num at h
  linarith
