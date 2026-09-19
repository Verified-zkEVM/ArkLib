/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jieyi Long, Quang Dao
-/
module

public import CompPoly.ToMathlib.Polynomial.BivariateDegree
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Degree sums for bivariate factors

The sum of either axis degree over distinct normalized factors of a nonzero polynomial is
bounded by the corresponding degree of that polynomial. Here `R[X][Y]` has outer variable `Y`:
`natDegree` measures `Y`, whereas `degreeX` measures the coefficient variable `X`.
The bounds also hold after selecting any subset of the distinct factors.

The finite-product lemmas work over an integral domain. The normalized-factor bounds additionally
require normalization and unique factorization for the bivariate polynomial ring.

## Implementation references

Adapted from Jieyi Long (`jieyilong`), `BCHKSUniversalFactorSums.lean`, lines 15–123, and
`BCHKSFactorPigeon.lean`, lines 277–302, in the Apache-2.0 licensed better-codes development:
https://github.com/proximity-prize/proximity-prize/blob/19bc7d3e21b2261257e1961acd720b2c395d87e1/ProximityPrize/SubmissionLower/BCHKSUniversalFactorSums.lean

Changes: use the existing CompPoly degree API, generalize finite products to indexed families,
weaken field assumptions to domain and factorization assumptions, and generalize the
positive-degree filter to an arbitrary subset. No donor `LocalMathlib` modules are copied.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The coefficient-variable degree is additive on a finite product of nonzero polynomials. -/
theorem degreeX_prod {ι : Type*} (s : Finset ι) (f : ι → R[X][Y])
    (hf : ∀ i ∈ s, f i ≠ 0) :
    degreeX (∏ i ∈ s, f i) = ∑ i ∈ s, degreeX (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    apply Nat.eq_zero_of_le_zero
    unfold degreeX
    apply Finset.sup_le
    intro i _hi
    by_cases h : i = 0 <;> simp [Polynomial.coeff_one, h]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [degreeX_mul _ _ (hf i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

/-- Divisibility into a nonzero polynomial bounds the coefficient-variable degree. -/
theorem degreeX_le_of_dvd {p q : R[X][Y]} (h : p ∣ q) (hq : q ≠ 0) :
    degreeX p ≤ degreeX q := by
  obtain ⟨r, rfl⟩ := h
  rw [degreeX_mul _ _ (left_ne_zero_of_mul hq) (right_ne_zero_of_mul hq)]
  exact Nat.le_add_right _ _

/-- A nonzero polynomial bounds both axis-degree sums of any indexed family whose product
divides it. The product premise accounts for repeated factors and their multiplicities. -/
theorem sum_natDegree_degreeX_le_of_prod_dvd {ι : Type*} (s : Finset ι)
    (f : ι → R[X][Y]) {p : R[X][Y]} (hp : p ≠ 0) (h : (∏ i ∈ s, f i) ∣ p) :
    (∑ i ∈ s, (f i).natDegree) ≤ p.natDegree ∧
      (∑ i ∈ s, degreeX (f i)) ≤ degreeX p := by
  have hf : ∀ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mp (ne_zero_of_dvd_ne_zero hp h)
  constructor
  · rw [← Polynomial.natDegree_prod s f hf]
    exact Polynomial.natDegree_le_of_dvd h hp
  · rw [← degreeX_prod s f hf]
    exact degreeX_le_of_dvd h hp

variable [DecidableEq R] [NormalizationMonoid R[X][Y]] [UniqueFactorizationMonoid R[X][Y]]

omit [IsDomain R] in
/-- The product of the distinct normalized factors divides the original nonzero polynomial. -/
theorem normalizedFactors_toFinset_prod_dvd (p : R[X][Y]) (hp : p ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors p).toFinset.prod id ∣ p := by
  classical
  exact (Multiset.toFinset_prod_dvd_prod _).trans
    (UniqueFactorizationMonoid.prod_normalizedFactors hp).dvd

/-- The distinct normalized factors separately satisfy both axis-degree budgets. -/
theorem normalizedFactors_toFinset_sum_natDegree_degreeX_le (p : R[X][Y]) (hp : p ≠ 0) :
    (∑ q ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset, q.natDegree) ≤
        p.natDegree ∧
      (∑ q ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset, degreeX q) ≤
        degreeX p := by
  classical
  exact sum_natDegree_degreeX_le_of_prod_dvd _ id hp
    (normalizedFactors_toFinset_prod_dvd p hp)

/-- Selecting any subset of the distinct normalized factors preserves both degree budgets.
In particular, this applies to the subset of factors with positive outer degree. -/
theorem sum_natDegree_degreeX_le_of_subset_normalizedFactors {p : R[X][Y]} (hp : p ≠ 0)
    (s : Finset R[X][Y]) (hs : s ⊆ (UniqueFactorizationMonoid.normalizedFactors p).toFinset) :
    (∑ q ∈ s, q.natDegree) ≤ p.natDegree ∧ (∑ q ∈ s, degreeX q) ≤ degreeX p := by
  have h := normalizedFactors_toFinset_sum_natDegree_degreeX_le p hp
  constructor
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hs (by simp)).trans h.1
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hs (by simp)).trans h.2

end

end Polynomial.Bivariate
