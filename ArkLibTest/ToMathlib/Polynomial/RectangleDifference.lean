/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.RectangleDifference

/-!
# Acceptance tests for rectangle-difference polynomials

The examples compute the degree-`s` coefficient of the rectangle difference for `s = 0, 1, 2`,
evaluate a small instance at a natural number, and show that both hypotheses `h ≤ a * N` and
`v ≤ b * N` of `Polynomial.eval_rectangleDifference_natCast` are needed.
-/

open Polynomial

namespace RectangleDifferenceTest

/-- With no variables the rectangle difference has natural degree `0` and constant coefficient
`h`. -/
example (a b h v : ℚ) :
    (rectangleDifference 0 a b h v).natDegree = 0 ∧
      (rectangleDifference 0 a b h v).coeff 0 = h := by
  refine ⟨Nat.le_zero.mp (natDegree_rectangleDifference_le 0 a b h v), ?_⟩
  rw [coeff_rectangleDifference_self]
  simp

/-- With one variable the rectangle difference has natural degree at most `1` and linear
coefficient `h * b + v * a`. -/
example (a b h v : ℚ) :
    (rectangleDifference 1 a b h v).natDegree ≤ 1 ∧
      (rectangleDifference 1 a b h v).coeff 1 = h * b + v * a := by
  refine ⟨natDegree_rectangleDifference_le 1 a b h v, ?_⟩
  rw [coeff_rectangleDifference_self]
  simp

/-- With two variables the rectangle difference has natural degree at most `2` and quadratic
coefficient `(h * b ^ 2 + 2 * v * a * b) / 2`. -/
example (a b h v : ℚ) :
    (rectangleDifference 2 a b h v).natDegree ≤ 2 ∧
      (rectangleDifference 2 a b h v).coeff 2 = (h * b ^ 2 + 2 * v * a * b) / 2 := by
  refine ⟨natDegree_rectangleDifference_le 2 a b h v, ?_⟩
  rw [coeff_rectangleDifference_self]
  norm_num

/-- For `s = 1`, `a = b = h = v = 1` and `N = 3` the rectangle difference counts
`4 * 4 - 3 * 3 = 7` exponents. -/
example : (rectangleDifference 1 ((1 : ℕ) : ℚ) (1 : ℕ) (1 : ℕ) (1 : ℕ)).eval ((3 : ℕ) : ℚ) = 7 := by
  rw [eval_rectangleDifference_natCast 1 1 1 1 1 3 (by norm_num) (by norm_num)]
  norm_num [Nat.choose_one_right]

/-- The hypothesis `h ≤ a * N` of `eval_rectangleDifference_natCast` is needed: for `s = 0`,
`a = b = v = N = 0` and `h = 1` the rectangle difference is the constant `1`, while the truncated
count is `1 * 1 - (0 - 1 + 1) * 1 = 0`. -/
example : (rectangleDifference 0 ((0 : ℕ) : ℚ) (0 : ℕ) (1 : ℕ) (0 : ℕ)).eval ((0 : ℕ) : ℚ) ≠
    (((0 * 0 + 1) * (0 * 0 + 0).choose 0 -
      (0 * 0 - 1 + 1) * (0 * 0 - 0 + 0).choose 0 : ℕ) : ℚ) := by
  simp [rectangleDifference, preHilbertPoly]

/-- The hypothesis `v ≤ b * N` of `eval_rectangleDifference_natCast` is needed: for `s = 1`,
`a = b = h = N = 0` and `v = 1` the rectangle difference evaluates to `1`, while the truncated
count is `1 * 1 - 1 * (0 - 1 + 1) = 0`. -/
example : (rectangleDifference 1 ((0 : ℕ) : ℚ) (0 : ℕ) (0 : ℕ) (1 : ℕ)).eval ((0 : ℕ) : ℚ) ≠
    (((0 * 0 + 1) * (0 * 0 + 1).choose 1 -
      (0 * 0 - 0 + 1) * (0 * 0 - 1 + 1).choose 1 : ℕ) : ℚ) := by
  simp [rectangleDifference, preHilbertPoly]

end RectangleDifferenceTest
