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
lemma Polynomial.toMvPolynomial_totalDegree_le [Nontrivial R] (p : Polynomial R) (i : σ) :
    ((Polynomial.toMvPolynomial i) p).totalDegree ≤ p.natDegree := by
  rw [p.as_sum_support]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro n hn
  simp only [Polynomial.toMvPolynomial, Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  rw [← Polynomial.as_sum_support p]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  rw [MvPolynomial.totalDegree_X_pow]
  exact Polynomial.le_natDegree_of_mem_supp n hn

end ToMvPolynomial

end ArkLib.ToMathlib
