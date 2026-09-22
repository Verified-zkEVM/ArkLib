/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponentials of logarithmic bounds as real powers

If `H ≤ log x + b` and `E ≤ H / a + c` with `a, x > 0`, then
`exp E ≤ exp (b / a + c) * x ^ (1 / a)`, because `exp (log x / a) = x ^ (1 / a)`. This is the form
in which a harmonic-number bound `H ≤ log x + b` enters an exponential estimate. For `a ≥ 1` and
`b ≥ 0` the constant `exp (b / a + c)` is at most `exp (b + c)`.

The tangent-line inequality `exp t ≥ exp 1 * t` gives `exp 1 * c ≤ ρ * exp (c / ρ)` for every
`c` and `ρ > 0`, and `exp (log x * ((a - 1) / a))` is the reciprocal of `x ^ (1 / a) / x`. The
file also records three numerical bounds: `exp (61 / 100) < 37 / 20`, from the degree-four Taylor
bound `Real.exp_bound'`; `48000 < exp (54 / 5)`, from the partial sums of the exponential series;
and `11 / 4 < exp (81 / 80)`, from Mathlib's `Real.exp_one_gt_d9`.

## Main statements

* `Real.exp_le_exp_mul_rpow_of_le_log_add`, `Real.exp_le_exp_add_mul_rpow_of_le_log_add`
* `Real.exp_one_mul_le_mul_exp_div`, `Real.rpow_one_div_div_self`
* `Real.exp_sixtyOne_div_hundred_lt`, `Real.fortyEightThousand_lt_exp_fiftyFour_div_five`,
  `Real.elevenFourths_lt_exp_eightyOne_div_eighty`
-/

@[expose] public section

namespace Real

/-- If `H ≤ log x + b` and `E ≤ H / a + c` with `a > 0` and `x > 0`, then
`exp E ≤ exp (b / a + c) * x ^ (1 / a)`. The hypothesis `0 < x` makes `x ^ (1 / a)` equal to
`exp (log x / a)`; the hypothesis `0 < a` makes division by `a` monotone. -/
theorem exp_le_exp_mul_rpow_of_le_log_add {a b c E H x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hH : H ≤ log x + b) (hE : E ≤ H / a + c) :
    exp E ≤ exp (b / a + c) * x ^ (1 / a) := by
  have he : E ≤ b / a + c + log x / a := by
    have := div_le_div_of_nonneg_right hH ha.le
    rw [add_div] at this
    linarith
  rw [rpow_def_of_pos hx, ← exp_add]
  exact exp_le_exp.mpr (by rw [mul_one_div]; exact he)

/-- For `a ≥ 1` and `b ≥ 0`, if `H ≤ log x + b` and `E ≤ H / a + c` then
`exp E ≤ exp (b + c) * x ^ (1 / a)`. This weakens `exp_le_exp_mul_rpow_of_le_log_add` by
`b / a ≤ b`, which needs both `1 ≤ a` and `0 ≤ b`. -/
theorem exp_le_exp_add_mul_rpow_of_le_log_add {a b c E H x : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hx : 0 < x) (hH : H ≤ log x + b) (hE : E ≤ H / a + c) :
    exp E ≤ exp (b + c) * x ^ (1 / a) := by
  have ha0 : 0 < a := by linarith
  refine (exp_le_exp_mul_rpow_of_le_log_add ha0 hx hH hE).trans ?_
  gcongr
  exact div_le_self hb ha

/-- `exp (61 / 100) < 37 / 20`. The Taylor bound with remainder at degree four gives
`exp (61 / 100) ≤ 1.8411`. -/
theorem exp_sixtyOne_div_hundred_lt : exp (61 / 100) < (37 / 20 : ℝ) := by
  have h := exp_bound' (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (61 / 100 : ℝ) ≤ 1) (by norm_num : 0 < (4 : ℕ))
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- For every real `c` and every `ρ > 0`, `exp 1 * c ≤ ρ * exp (c / ρ)`. This is the tangent line
`t ≤ exp (t - 1)` at `t = c / ρ`, multiplied by `ρ * exp 1`. As a function of `ρ` the right side is
minimized at `ρ = c` when `c > 0`, where equality holds. -/
theorem exp_one_mul_le_mul_exp_div (c : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    exp 1 * c ≤ ρ * exp (c / ρ) := by
  have ht : c / ρ ≤ exp (c / ρ - 1) := by linarith [add_one_le_exp (c / ρ - 1)]
  calc
    exp 1 * c = ρ * (exp 1 * (c / ρ)) := by field_simp
    _ ≤ ρ * (exp 1 * exp (c / ρ - 1)) := by gcongr
    _ = ρ * exp (c / ρ) := by rw [← exp_add]; congr 2; ring

/-- For `x > 0` and `a ≠ 0`, `x ^ (1 / a) / x = (exp (log x * ((a - 1) / a)))⁻¹`, since
`1 / a - 1 = -((a - 1) / a)`. The hypothesis `0 < x` is needed for `x ^ (1 / a) = exp (log x / a)`;
`a ≠ 0` for the division identity. -/
theorem rpow_one_div_div_self {a x : ℝ} (hx : 0 < x) (ha : a ≠ 0) :
    x ^ (1 / a) / x = (exp (log x * ((a - 1) / a)))⁻¹ := by
  rw [rpow_def_of_pos hx, ← exp_log hx, ← exp_sub, ← exp_neg, log_exp]
  congr 1
  field_simp
  ring

/-- `48000 < exp (54 / 5)`. The first nineteen terms of the exponential series at `54 / 5` sum to
more than `48000`; the value of `exp (54 / 5)` is about `49021`. -/
theorem fortyEightThousand_lt_exp_fiftyFour_div_five : (48000 : ℝ) < exp (54 / 5) := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 54 / 5) 19
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- `11 / 4 < exp (81 / 80)`. Write `exp (81 / 80) = exp 1 * exp (1 / 80)` and use
`exp 1 > 2.7182818283` and `exp (1 / 80) ≥ 1 + 1 / 80`; the value is about `2.7524`. -/
theorem elevenFourths_lt_exp_eightyOne_div_eighty : (11 / 4 : ℝ) < exp (81 / 80) := by
  rw [show (81 / 80 : ℝ) = 1 + 1 / 80 by norm_num, exp_add]
  have h1 := exp_one_gt_d9
  have h2 := add_one_le_exp (1 / 80 : ℝ)
  nlinarith [exp_pos 1]

end Real
