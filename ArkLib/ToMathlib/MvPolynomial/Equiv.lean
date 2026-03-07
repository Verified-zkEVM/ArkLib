/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Polynomial.AlgebraMap

/-!
# Equivalences for MvPolynomial and Polynomial

This file provides lemmas relating `Polynomial.toMvPolynomial` with properties like
non-zero preservation and total degree bounds.

These are auxiliary lemmas intended to be upstreamed to Mathlib.
-/

namespace ArkLib.ToMathlib

section ToMvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

/-- `Polynomial.toMvPolynomial` preserves non-zero property. -/
lemma Polynomial.toMvPolynomial_ne_zero_iff (p : Polynomial R) (i : σ) :
    (Polynomial.toMvPolynomial i) p ≠ 0 ↔ p ≠ 0 := by
  constructor
  · intro h hp
    rw [hp, map_zero] at h
    exact h rfl
  · intro hp h
    apply hp
    rw [← map_zero (toMvPolynomial i)] at h
    exact (toMvPolynomial_injective i) h

/-- The total degree of `toMvPolynomial p` is at most the natural degree of `p`. -/
-- TODO: Complete this proof using `MvPolynomial.totalDegree_finsetSum_le`,
-- `MvPolynomial.totalDegree_mul`, `MvPolynomial.totalDegree_C`, `MvPolynomial.totalDegree_X_pow`,
-- and `Polynomial.le_natDegree_of_mem_supp`. Depends on Mathlib API for `Polynomial.aeval_monomial`
-- and `MvPolynomial.algebraMap_eq` being available in the current Mathlib version.
lemma Polynomial.toMvPolynomial_totalDegree_le [Nontrivial R] (p : Polynomial R) (i : σ) :
    ((Polynomial.toMvPolynomial i) p).totalDegree ≤ p.natDegree := by
  sorry

end ToMvPolynomial

end ArkLib.ToMathlib
