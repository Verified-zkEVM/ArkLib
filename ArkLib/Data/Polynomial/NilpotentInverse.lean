/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite correction of an approximate inverse

For an approximate inverse `b` of `a`, the error is `1 - a*b`. A finite geometric
sum corrects this error whenever its specified power vanishes. All operations are
executable over a commutative ring, including rings with nilpotents. The construction
does not search for an approximate inverse or certify a nilpotence bound.
-/

@[expose] public section

namespace Polynomial.NilpotentInverse

variable {R : Type*} [CommRing R]

/-- Finite geometric sum, evaluated using the ring's executable operations. -/
def geometric (N : ℕ) (e : R) : R := ∑ i ∈ Finset.range N, e ^ i

/-- Correct an approximate inverse with the first `N` powers of its residual error. -/
def correct (N : ℕ) (a b : R) : R := b * geometric N (1 - a * b)

/-- No correction terms are present at precision zero. -/
@[simp] theorem geometric_zero (e : R) : geometric 0 e = 0 := by simp [geometric]

/-- The precision-zero result is zero; no positive precision is silently substituted. -/
@[simp] theorem correct_zero (a b : R) : correct 0 a b = 0 := by simp [correct]

/-- The finite geometric product identity, without a nilpotence assumption. -/
theorem geometric_identity (N : ℕ) (e : R) :
    (1 - e) * geometric N e = 1 - e ^ N := mul_neg_geom_sum e N

/-- The corrected multiplicative residual is exactly the specified power of the old error. -/
theorem mul_correct (N : ℕ) (a b : R) :
    a * correct N a b = 1 - (1 - a * b) ^ N := by
  rw [correct, ← mul_assoc]
  simpa using geometric_identity N (1 - a * b)

/-- The same identity holds with the corrected inverse on the left. -/
theorem correct_mul (N : ℕ) (a b : R) :
    correct N a b * a = 1 - (1 - a * b) ^ N := by
  rw [mul_comm, mul_correct]

/-- Vanishing residual power gives a right inverse. -/
theorem right_inverse (N : ℕ) (a b : R) (h : (1 - a * b) ^ N = 0) :
    a * correct N a b = 1 := by rw [mul_correct, h, sub_zero]

/-- Vanishing residual power gives a left inverse. -/
theorem left_inverse (N : ℕ) (a b : R) (h : (1 - a * b) ^ N = 0) :
    correct N a b * a = 1 := by rw [correct_mul, h, sub_zero]

/-- Package the computed correction as a unit using only the residual certificate. -/
def unit (N : ℕ) (a b : R) (h : (1 - a * b) ^ N = 0) : Rˣ where
  val := a
  inv := correct N a b
  val_inv := right_inverse N a b h
  inv_val := left_inverse N a b h

/-- In a nontrivial ring, a valid nilpotence certificate necessarily has positive precision. -/
theorem precision_pos [Nontrivial R] (N : ℕ) (a b : R)
    (h : (1 - a * b) ^ N = 0) : 0 < N := by
  cases N with
  | zero => simp at h
  | succ N => exact Nat.zero_lt_succ N

end Polynomial.NilpotentInverse
