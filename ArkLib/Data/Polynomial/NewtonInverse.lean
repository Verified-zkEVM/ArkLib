/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.NilpotentInverse
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring

/-!
# Executable Newton inverse doubling

Each update squares the multiplicative residual. The requested nilpotence precision
selects the least number of doubling rounds, rather than performing that many updates.
The initial approximate inverse and its residual certificate remain caller inputs.
-/

@[expose] public section

namespace Polynomial.NewtonInverse

variable {R : Type*} [CommRing R]

/-- One Newton update, using multiplication and subtraction only. -/
def step (a b : R) : R := b * (2 - a * b)

/-- Execute exactly the specified number of Newton updates. -/
def iterate : ℕ → R → R → R
  | 0, _, b => b
  | rounds + 1, a, b => step a (iterate rounds a b)

/-- The multiplicative error squares in one update, in every characteristic. -/
theorem residual_step (a b : R) : 1 - a * step a b = (1 - a * b) ^ 2 := by
  unfold step
  ring

/-- After the executed rounds, the original residual has exponent `2^rounds`. -/
theorem residual_iterate (rounds : ℕ) (a b : R) :
    1 - a * iterate rounds a b = (1 - a * b) ^ (2 ^ rounds) := by
  induction rounds with
  | zero => simp [iterate]
  | succ rounds ih =>
    rw [iterate, residual_step, ih, ← pow_mul, pow_succ]

/-- The smallest number of doublings reaching a requested exponent. -/
def rounds (N : ℕ) : ℕ := Nat.clog 2 N

/-- The selected exponent reaches the requested precision, including precision zero. -/
theorem precision_le (N : ℕ) : N ≤ 2 ^ rounds N := Nat.le_pow_clog (by decide) N

/-- No smaller round count suffices to reach the requested precision. -/
theorem rounds_le_iff (N m : ℕ) : rounds N ≤ m ↔ N ≤ 2 ^ m :=
  Nat.clog_le_iff_le_pow (by decide)

/-- Correct an approximate inverse with the least sufficient number of Newton rounds. -/
def correct (N : ℕ) (a b : R) : R := iterate (rounds N) a b

/-- Precision zero executes no updates and returns the supplied approximation unchanged. -/
@[simp] theorem correct_zero (a b : R) : correct 0 a b = b := by
  simp [correct, rounds, iterate]

/-- Precision one also requires no update; its certificate already asserts exact inversion. -/
@[simp] theorem correct_one (a b : R) : correct 1 a b = b := by
  simp [correct, rounds, iterate]

/-- Exact residual identity for the precision-selected computation. -/
theorem residual_correct (N : ℕ) (a b : R) :
    1 - a * correct N a b = (1 - a * b) ^ (2 ^ rounds N) :=
  residual_iterate (rounds N) a b

/-- A certified nilpotent error yields a computed right inverse. -/
theorem right_inverse (N : ℕ) (a b : R) (h : (1 - a * b) ^ N = 0) :
    a * correct N a b = 1 := by
  have hz := pow_eq_zero_of_le (precision_le N) h
  rw [← residual_correct] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The computed result is also a left inverse over the commutative coefficient ring. -/
theorem left_inverse (N : ℕ) (a b : R) (h : (1 - a * b) ^ N = 0) :
    correct N a b * a = 1 := by
  rw [mul_comm, right_inverse N a b h]

/-- Package the executed Newton result as a unit using its nilpotence certificate. -/
def unit (N : ℕ) (a b : R) (h : (1 - a * b) ^ N = 0) : Rˣ where
  val := a
  inv := correct N a b
  val_inv := right_inverse N a b h
  inv_val := left_inverse N a b h

/-- A zero-precision inverse certificate is impossible in a nontrivial ring. -/
theorem precision_pos [Nontrivial R] (N : ℕ) (a b : R)
    (h : (1 - a * b) ^ N = 0) : 0 < N :=
  NilpotentInverse.precision_pos N a b h

end Polynomial.NewtonInverse
