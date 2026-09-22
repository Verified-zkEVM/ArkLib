/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow

/-!
# Acceptance cases for exponentials of logarithmic bounds

A concrete instance with `a = 2`, the case showing that `1 ≤ a` is needed in
`Real.exp_le_exp_add_mul_rpow_of_le_log_add`, and the source's `exp_le_rpow` and
`endpoint_exp_upper`.
-/

/-- `a = 2`, `x = 4`, `b = c = 0`, `H = log 4`, `E = log 4 / 2`: `exp (log 4 / 2) ≤ 4 ^ (1 / 2)`,
that is `exp (log 4 / 2) ≤ 2`. -/
example : Real.exp (Real.log 4 / 2) ≤ 2 := by
  have h := Real.exp_le_exp_mul_rpow_of_le_log_add (a := 2) (b := 0) (c := 0)
    (E := Real.log 4 / 2) (H := Real.log 4) (x := 4) (by norm_num) (by norm_num)
    (by simp) (by simp)
  have hsqrt : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [zero_div, zero_add, Real.exp_zero, one_mul, hsqrt] at h
  exact h

/-- The hypothesis `1 ≤ a` is needed in the weakened form: with `a = 1 / 2`, `b = 1`, `c = 0`,
`x = 1`, `H = 1` and `E = H / a = 2`, the hypotheses hold but `exp 2 ≤ exp 1 * 1 ^ 2` fails. -/
example : 1 ≤ Real.log 1 + 1 ∧ (2 : ℝ) ≤ 1 / (1 / 2) + 0 ∧
    ¬ (Real.exp 2 ≤ Real.exp (1 + 0) * (1 : ℝ) ^ (1 / (1 / 2 : ℝ))) := by
  refine ⟨by simp, by norm_num, ?_⟩
  rw [Real.one_rpow, mul_one, add_zero, Real.exp_le_exp]
  norm_num

/-- The source's `exp_le_rpow`: `b = 3 / 5`, `c = 1 / 100`, `x = d` natural, and any
`C ≥ exp (61 / 100)`. -/
example (a H E C : ℝ) (d : ℕ) (ha : 1 ≤ a) (hd : 0 < d)
    (hH : H ≤ Real.log d + 3 / 5) (hE : E ≤ H / a + 1 / 100)
    (hC : Real.exp (61 / 100) ≤ C) :
    Real.exp E ≤ C * (d : ℝ) ^ (1 / a) := by
  have h := Real.exp_le_exp_add_mul_rpow_of_le_log_add ha (by norm_num) (by exact_mod_cast hd)
    hH hE
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  norm_num at hC ⊢
  exact hC

/-- The source's `WeightedSupportParameters.endpoint_exp_upper`, and the form used by the
normalized rank bound: `exp (3 / 5 + 1 / 100) < 37 / 20`. -/
example : Real.exp (3 / 5 + 1 / 100) < 37 / 20 := by
  norm_num
  exact Real.exp_sixtyOne_div_hundred_lt
