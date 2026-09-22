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

The file also records the numerical bound `exp (61 / 100) < 37 / 20`, from the degree-four
Taylor bound `Real.exp_bound'`.

## Main statements

* `Real.exp_le_exp_mul_rpow_of_le_log_add`, `Real.exp_le_exp_add_mul_rpow_of_le_log_add`
* `Real.exp_sixtyOne_div_hundred_lt`
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

end Real
