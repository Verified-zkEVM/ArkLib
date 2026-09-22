/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow

/-!
# Acceptance cases for exponentials of logarithmic bounds

A concrete instance with `a = 2`, the case showing that `1 ≤ a` is needed in
`Real.exp_le_exp_add_mul_rpow_of_le_log_add`, its case `b = 3 / 5`, `c = 1 / 100`, `x = d`, and
the bound `exp (3 / 5 + 1 / 100) < 37 / 20`; the constants `exp (54 / 5) > 48000` and
`exp (81 / 80) > 11 / 4`; instances of `Real.exp_one_mul_le_mul_exp_div`, including its equality
case `c = ρ`; and a concrete instance of `Real.rpow_one_div_div_self`.
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

/-- `Real.exp_le_exp_add_mul_rpow_of_le_log_add` at `b = 3 / 5`, `c = 1 / 100`, `x = d` natural,
and any `C ≥ exp (61 / 100)`. -/
example (a H E C : ℝ) (d : ℕ) (ha : 1 ≤ a) (hd : 0 < d)
    (hH : H ≤ Real.log d + 3 / 5) (hE : E ≤ H / a + 1 / 100)
    (hC : Real.exp (61 / 100) ≤ C) :
    Real.exp E ≤ C * (d : ℝ) ^ (1 / a) := by
  have h := Real.exp_le_exp_add_mul_rpow_of_le_log_add ha (by norm_num) (by exact_mod_cast hd)
    hH hE
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  norm_num at hC ⊢
  exact hC

/-- The form of `Real.exp_sixtyOne_div_hundred_lt` used by the normalized rank bound:
`exp (3 / 5 + 1 / 100) < 37 / 20`. -/
example : Real.exp (3 / 5 + 1 / 100) < 37 / 20 := by
  norm_num
  exact Real.exp_sixtyOne_div_hundred_lt

/-- `48000 < exp (54 / 5)`. -/
example : (48000 : ℝ) < Real.exp (54 / 5) := Real.fortyEightThousand_lt_exp_fiftyFour_div_five

/-- `11 / 4 < exp (81 / 80)`. -/
example : (11 / 4 : ℝ) < Real.exp (81 / 80) := Real.elevenFourths_lt_exp_eightyOne_div_eighty

/-- Equality holds in `Real.exp_one_mul_le_mul_exp_div` at `c = ρ`: both sides are `e ρ`. -/
example (ρ : ℝ) (hρ : ρ ≠ 0) : Real.exp 1 * ρ = ρ * Real.exp (ρ / ρ) := by
  rw [div_self hρ, mul_comm]

/-- The bound needs no sign on `c`: at `c = -1`, `ρ = 1` it reads `-e ≤ exp (-1)`. -/
example : Real.exp 1 * (-1) ≤ 1 * Real.exp (-1 / 1) :=
  Real.exp_one_mul_le_mul_exp_div (-1) one_pos

/-- At `x = 9`, `a = 2`: `9 ^ (1 / 2) / 9 = 1 / 3 = (exp (log 9 / 2))⁻¹`. -/
example : (Real.exp (Real.log 9 * ((2 - 1) / 2)))⁻¹ = 1 / 3 := by
  have hsqrt : (9 : ℝ) ^ ((1 : ℝ) / 2) = 3 := by
    rw [← Real.sqrt_eq_rpow, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← Real.rpow_one_div_div_self (by norm_num) (by norm_num), hsqrt]
  norm_num
