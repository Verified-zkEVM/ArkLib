/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.RingTheory.Polynomial.Basic

/-!
# `Polynomial.degreeLT` facts

Lemmas about `Polynomial.degreeLT R n`, the submodule of polynomials of degree `< n`.

## Main statements

* `Polynomial.degreeLT_zero`: at the boundary `n = 0`, `degreeLT R 0` is the zero submodule.
* `Polynomial.natDegree_le_of_mem_degreeLT_succ`: a polynomial in `degreeLT R (n + 1)` has
  natural degree at most `n`.
* `Polynomial.mem_degreeLT_of_mul_left`: if the coefficient semiring has no zero divisors,
  `g ≠ 0`, and `g * q ∈ degreeLT R n`, then `q ∈ degreeLT R n`.

The boundary fact is reusable for any construction that maps `degreeLT` through a linear map —
e.g. Reed-Solomon codes (`ReedSolomon.code α n = (degreeLT F n).map (evalOnPoints α)`), folded
RS codes, and similar code families. The other two lemmas serve degree bounds stated with
`degreeLT`: the first converts such a bound to a natural-degree bound, and the second keeps it
when a common factor is removed, as in the primitive kernel vectors of
`ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight`. Candidates for upstream PR to Mathlib.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- `Polynomial.degreeLT R 0 = ⊥`: the only polynomial with degree strictly less than `0`
(in `WithBot ℕ`) is the zero polynomial.

Not `@[simp]` to avoid disrupting existing simp-based proofs that unfold `degreeLT` directly. -/
theorem degreeLT_zero : degreeLT R 0 = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [Polynomial.mem_degreeLT, Nat.cast_zero, Nat.WithBot.lt_zero_iff,
      Polynomial.degree_eq_bot] at hp
  exact hp ▸ Submodule.zero_mem _

/-- A polynomial in `degreeLT R (n + 1)` has natural degree at most `n`.

This converts a strict `degreeLT` bound into the natural-degree form. The natural-degree form
loses information: the zero polynomial and the nonzero constants both have natural degree `0`,
while `degreeLT R 1` and `degreeLT R 0 = ⊥` distinguish them. -/
theorem natDegree_le_of_mem_degreeLT_succ {p : R[X]} {n : ℕ} (hp : p ∈ degreeLT R (n + 1)) :
    p.natDegree ≤ n := by
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE] at hp
  exact natDegree_le_of_degree_le hp

/-- Removing a nonzero left factor keeps a polynomial in the same strict degree bound.

If `g ≠ 0` and `g * q` has degree less than `n`, then so does `q`. The hypothesis `g ≠ 0` is
necessary, since `0 * q = 0` has every degree bound. The coefficient ring must have no zero
divisors, so that the degree of `g * q` is the sum of the degrees of `g` and `q`. Because the
statement uses `Polynomial.degreeLT`, it also covers `q = 0` and the budget `n = 0`, where
membership means `q = 0`; a natural-degree formulation would conflate `q = 0` with nonzero
constants. -/
theorem mem_degreeLT_of_mul_left [NoZeroDivisors R] {g q : R[X]} {n : ℕ} (hg : g ≠ 0)
    (h : g * q ∈ degreeLT R n) : q ∈ degreeLT R n := by
  rw [mem_degreeLT, degree_mul] at h
  rw [mem_degreeLT]
  exact (le_add_of_nonneg_left (zero_le_degree_iff.mpr hg)).trans_lt h

end Polynomial
