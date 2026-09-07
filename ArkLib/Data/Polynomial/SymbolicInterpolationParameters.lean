/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Real budgets for symbolic interpolation

The arithmetic comparison below is the strict surplus criterion from the proof of
[BCHKS25, Lemma 3.1], with `r = √(k/n)`. It does not assert the ceiling-count lower bound
or construct an interpolant.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
    *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.1.
-/

namespace Polynomial.SymbolicInterpolation

/-- The real comparison guaranteeing strict surplus, once the variable-count lower bound
has been established. The coefficient budget `z` may exceed its prescribed minimum. -/
theorem strict_surplus_of_coefficient_budget (m r z : ℝ) (hm : 1 ≤ m) (hr : 0 < r)
    (hz : (m + 1 / 2) ^ 2 / (3 * r ^ 2) ≤ z) :
    (r ^ 2 * ((m + 1 / 2) / r) * ((m + 1 / 2) / r + 1) - m * (m + 1)) * z >
      (r ^ 2 * (((m + 1 / 2) / r) ^ 3 - (m + 1 / 2) / r) - (m ^ 3 - m)) / 3 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have ht : 0 < m + 1 / 2 := by linarith
  have hc : 0 < 1 / 4 + (m + 1 / 2) * r := by positivity
  have hcoef : r ^ 2 * ((m + 1 / 2) / r) * ((m + 1 / 2) / r + 1) -
      m * (m + 1) = 1 / 4 + (m + 1 / 2) * r := by field_simp; ring
  have hcube : 0 ≤ m ^ 3 - m := by nlinarith [sq_nonneg (m - 1)]
  have hres : 0 < (m + 1 / 2) ^ 2 / (12 * r ^ 2) +
      ((m + 1 / 2) * r + m ^ 3 - m) / 3 := by
    have hp : 0 < (m + 1 / 2) * r := mul_pos ht hr
    have hq : 0 < (m + 1 / 2) ^ 2 / (12 * r ^ 2) := by positivity
    linarith
  have hid : (1 / 4 + (m + 1 / 2) * r) * ((m + 1 / 2) ^ 2 / (3 * r ^ 2)) -
      (r ^ 2 * (((m + 1 / 2) / r) ^ 3 - (m + 1 / 2) / r) - (m ^ 3 - m)) / 3 =
      (m + 1 / 2) ^ 2 / (12 * r ^ 2) +
        ((m + 1 / 2) * r + m ^ 3 - m) / 3 := by field_simp; ring
  rw [hcoef]
  have hmono := mul_le_mul_of_nonneg_left hz hc.le
  linarith

/-- The prescribed coefficient budget dominates the Y-degree budget in the paper's regime. -/
theorem y_budget_le_coefficient_budget (m r : ℝ) (hm : 3 ≤ m)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    (m + 1 / 2) / r ≤ (m + 1 / 2) ^ 2 / (3 * r ^ 2) := by
  apply (div_le_div_iff₀ hr (by positivity : 0 < 3 * r ^ 2)).mpr
  have ht : 0 ≤ m + 1 / 2 := by linarith
  have htr : 3 * r ≤ m + 1 / 2 := by linarith
  nlinarith [mul_nonneg hr.le (mul_nonneg ht (sub_nonneg.mpr htr))]

/-- The multiplicity threshold makes the X-degree budget small enough for the root argument.
Here `eta = 1 - r - gamma`; multiplying this inequality by the block length gives the
paper's `D_X ≤ (1 - gamma) * m * n`. -/
theorem x_budget_le_multiplicity_budget (m r eta : ℝ) (heta : 0 < eta)
    (hm : r / (2 * eta) ≤ m) :
    (m + 1 / 2) * r ≤ (r + eta) * m := by
  have h := (div_le_iff₀ (by positivity : 0 < 2 * eta)).mp hm
  nlinarith

end Polynomial.SymbolicInterpolation
