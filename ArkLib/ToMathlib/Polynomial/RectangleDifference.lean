/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Leading coefficients of low-dimensional rectangle differences

These explicit Hilbert polynomials record the rectangle differences used by bidegree image
bounds when the second projective factor has dimension one or two. Their evaluation lemmas
identify them with the corresponding natural-number dimension differences once the shifted
bidegrees are nonnegative.
-/

@[expose] public section

open Polynomial

namespace Polynomial

noncomputable section

/-- The dimension-one rectangle difference after substituting bidegrees `(a*N,b*N)` and
cutting by bidegree `(h,v)`. -/
def rectangleDifferenceOne (a b h v : ℚ) : ℚ[X] :=
  C (h * b + v * a) * X + C (h + v - h * v)

/-- The dimension-two rectangle difference after substituting bidegrees `(a*N,b*N)` and
cutting by bidegree `(h,v)`. -/
def rectangleDifferenceTwo (a b h v : ℚ) : ℚ[X] :=
  C ((h * b ^ 2 + 2 * v * a * b) / 2) * X ^ 2 +
    C ((2 * v * b + 3 * v * a - v ^ 2 * a + 3 * h * b - 2 * h * v * b) / 2) * X +
      C ((3 * v - v ^ 2 + h * (v ^ 2 - 3 * v + 2)) / 2)

theorem rectangleDifferenceOne_natDegree_le (a b h v : ℚ) :
    (rectangleDifferenceOne a b h v).natDegree ≤ 1 := by
  unfold rectangleDifferenceOne
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simpa using natDegree_C_mul_X_pow_le (h * b + v * a) 1
  · change (C (h + v - h * v)).natDegree ≤ 1
    rw [natDegree_C]
    omega

@[simp]
theorem rectangleDifferenceOne_coeff_one (a b h v : ℚ) :
    (rectangleDifferenceOne a b h v).coeff 1 = h * b + v * a := by
  simp [rectangleDifferenceOne]

theorem rectangleDifferenceTwo_natDegree_le (a b h v : ℚ) :
    (rectangleDifferenceTwo a b h v).natDegree ≤ 2 := by
  unfold rectangleDifferenceTwo
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · simpa using natDegree_C_mul_X_pow_le ((h * b ^ 2 + 2 * v * a * b) / 2) 2
    · exact natDegree_mul_le.trans (by simp)
  · rw [natDegree_C]
    omega

@[simp]
theorem rectangleDifferenceTwo_coeff_two (a b h v : ℚ) :
    (rectangleDifferenceTwo a b h v).coeff 2 =
      (h * b ^ 2 + 2 * v * a * b) / 2 := by
  simp [rectangleDifferenceTwo]

/-- Evaluation recovers `(aN+1)(bN+1)-(aN-h+1)(bN-v+1)`. -/
theorem eval_rectangleDifferenceOne_natCast (a b h v N : ℕ)
    (hh : h ≤ a * N) (hv : v ≤ b * N) :
    (rectangleDifferenceOne a b h v).eval (N : ℚ) =
      (((a * N + 1) * (b * N + 1) -
        (a * N - h + 1) * (b * N - v + 1) : ℕ) : ℚ) := by
  have ha : a * N - h + 1 ≤ a * N + 1 := Nat.add_le_add_right (Nat.sub_le _ _) 1
  have hb : b * N - v + 1 ≤ b * N + 1 := Nat.add_le_add_right (Nat.sub_le _ _) 1
  have hp := Nat.mul_le_mul ha hb
  rw [Nat.cast_sub hp]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Nat.cast_sub hh, Nat.cast_sub hv]
  simp only [rectangleDifferenceOne, eval_add, eval_mul, eval_C, eval_X, Nat.cast_mul]
  ring

/-- Evaluation recovers
`(aN+1) choose(bN+2,2) - (aN-h+1) choose(bN-v+2,2)`. -/
theorem eval_rectangleDifferenceTwo_natCast (a b h v N : ℕ)
    (hh : h ≤ a * N) (hv : v ≤ b * N) :
    (rectangleDifferenceTwo a b h v).eval (N : ℚ) =
      (((a * N + 1) * (b * N + 2).choose 2 -
        (a * N - h + 1) * (b * N - v + 2).choose 2 : ℕ) : ℚ) := by
  have ha : a * N - h + 1 ≤ a * N + 1 := Nat.add_le_add_right (Nat.sub_le _ _) 1
  have hb : b * N - v + 2 ≤ b * N + 2 := Nat.add_le_add_right (Nat.sub_le _ _) 2
  have hp := Nat.mul_le_mul ha (Nat.choose_le_choose 2 hb)
  rw [Nat.cast_sub hp]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_choose_two]
  rw [Nat.cast_sub hh, Nat.cast_sub hv]
  push_cast
  simp only [rectangleDifferenceTwo, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

end

end Polynomial
