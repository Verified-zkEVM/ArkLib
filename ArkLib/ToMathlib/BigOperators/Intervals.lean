/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring

/-!
# Sums of the first natural numbers and their squares in a ring

Mathlib's `Finset.sum_range_id_mul_two` computes `∑_{i<n} i` in `ℕ`. This file states the
Faulhaber sums of degree one and two after casting into an arbitrary commutative ring, where the
subtraction `n - 1` is the ring subtraction and needs no case split at `n = 0`.

## Main statements

* `Finset.sum_range_natCast_mul_two`: `(∑_{i<n} i) * 2 = n (n - 1)`.
* `Finset.sum_range_natCast_sq_mul_six`: `(∑_{i<n} i²) * 6 = n (n - 1) (2n - 1)`.
-/

@[expose] public section

namespace Finset

variable {R : Type*} [CommRing R]

/-- The sum `∑_{i<n} i`, cast into a commutative ring, satisfies `(∑_{i<n} i) * 2 = n (n - 1)`. -/
theorem sum_range_natCast_mul_two (n : ℕ) :
    (∑ i ∈ range n, (i : R)) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- The sum `∑_{i<n} i²`, cast into a commutative ring, satisfies
`(∑_{i<n} i²) * 6 = n (n - 1) (2n - 1)`. -/
theorem sum_range_natCast_sq_mul_six (n : ℕ) :
    (∑ i ∈ range n, (i : R) ^ 2) * 6 = n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

end Finset
