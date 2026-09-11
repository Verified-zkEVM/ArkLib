/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.NormSieve.MultiplicitySupport

/-!
# All-fiber norm product filter

The decoder's first filter multiplies the nonuniversal norm polynomials from every interpolation
fiber. A candidate retained with threshold `T` therefore has total root multiplicity at least
`T` across the norm factors. This module supplies the executable product-and-filter operation
and its exact extension-field semantics.

The construction is deliberately independent of how each norm factor is obtained.  In
particular, it does not package the separate base-change obligation that connects a concrete
finite fiber algebra to its specialized multiplication determinant, and it makes no runtime or
bit-complexity claim.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.NormSieve

open Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Product of all nonuniversal norm factors, indexed in their transcript order. -/
def normProduct {n : ℕ} (norms : Fin n → CompPoly.CPolynomial F) :
    CompPoly.CPolynomial F :=
  ∏ i, norms i

@[simp] theorem normProduct_toPoly {n : ℕ}
    (norms : Fin n → CompPoly.CPolynomial F) :
    (normProduct norms).toPoly = ∏ i, (norms i).toPoly := by
  simp only [normProduct, CompPoly.CPolynomial.toPoly_prod]

theorem normProduct_ne_zero {n : ℕ}
    {norms : Fin n → CompPoly.CPolynomial F} (hnorms : ∀ i, norms i ≠ 0) :
    normProduct norms ≠ 0 := by
  intro hzero
  have hpoly := congrArg CompPoly.CPolynomial.toPoly hzero
  rw [normProduct_toPoly, CompPoly.CPolynomial.toPoly_zero] at hpoly
  exact (Finset.prod_ne_zero_iff.mpr fun i _ ↦
    (CompPoly.CPolynomial.toPoly_eq_zero_iff (norms i)).not.mpr (hnorms i)) hpoly

/-- The degree of the product is exactly the sum of the individual norm degrees. -/
theorem natDegree_normProduct_eq_sum {n : ℕ}
    (norms : Fin n → CompPoly.CPolynomial F) (hnorms : ∀ i, norms i ≠ 0) :
    (normProduct norms).natDegree = ∑ i, (norms i).natDegree := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, normProduct_toPoly,
    Polynomial.natDegree_prod Finset.univ _ (fun i _ ↦
      (CompPoly.CPolynomial.toPoly_eq_zero_iff (norms i)).not.mpr (hnorms i))]
  simp only [CompPoly.CPolynomial.natDegree_toPoly]

/-- Root multiplicity in the all-fiber product is the sum of the individual multiplicities.
The equality holds after every coefficient-field extension. -/
theorem rootMultiplicity_normProduct_map {n : ℕ}
    (norms : Fin n → CompPoly.CPolynomial F) (hnorms : ∀ i, norms i ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    ((normProduct norms).toPoly.map phi).rootMultiplicity x =
      ∑ i, ((norms i).toPoly.map phi).rootMultiplicity x := by
  rw [normProduct_toPoly]
  rw [Polynomial.map_prod]
  let factor : Fin n → Polynomial K := fun i ↦ (norms i).toPoly.map phi
  have hfactor : ∀ i, factor i ≠ 0 := fun i ↦ by
    exact (Polynomial.map_ne_zero_iff phi.injective).2
      ((CompPoly.CPolynomial.toPoly_eq_zero_iff (norms i)).not.mpr (hnorms i))
  change (∏ i, factor i).rootMultiplicity x = ∑ i, (factor i).rootMultiplicity x
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Polynomial.rootMultiplicity_mul]
      · exact congrArg ((factor a).rootMultiplicity x + ·) ih
      · exact mul_ne_zero (hfactor a)
          (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hfactor i)

/-- At least `S.card` individually vanishing norm factors contribute to the multiplicity of the
same candidate in the all-fiber product. -/
theorem card_le_rootMultiplicity_normProduct_map_of_eval₂_eq_zero {n : ℕ}
    (norms : Fin n → CompPoly.CPolynomial F) (hnorms : ∀ i, norms i ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (S : Finset (Fin n))
    (hvanish : ∀ i ∈ S, (norms i).toPoly.eval₂ phi x = 0) :
    S.card ≤ ((normProduct norms).toPoly.map phi).rootMultiplicity x := by
  rw [rootMultiplicity_normProduct_map norms hnorms phi x]
  calc
    S.card = ∑ _i ∈ S, 1 := by simp
    _ ≤ ∑ i ∈ S, ((norms i).toPoly.map phi).rootMultiplicity x := by
      exact Finset.sum_le_sum fun i hi ↦ by
        apply Nat.succ_le_iff.2
        apply (Polynomial.rootMultiplicity_pos (by
          exact (Polynomial.map_ne_zero_iff phi.injective).2
            ((CompPoly.CPolynomial.toPoly_eq_zero_iff (norms i)).not.mpr (hnorms i)))).2
        rw [Polynomial.IsRoot, Polynomial.eval_map]
        exact hvanish i hi
    _ ≤ ∑ i, ((norms i).toPoly.map phi).rootMultiplicity x := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)

variable [Fintype F]

/-- Executable all-fiber product followed by characteristic-safe threshold retention. -/
def retainedNormProduct (p T : ℕ) [Fact p.Prime] [CharP F p]
    {n : ℕ} (norms : Fin n → CompPoly.CPolynomial F) :
    CompPoly.CPolynomial F :=
  retainedMultiplicitySupport p T (normProduct norms)

/-- Exact semantics of the product filter over every extension field. -/
theorem eval₂_retainedNormProduct_eq_zero_iff_sum_rootMultiplicity
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {n : ℕ} (norms : Fin n → CompPoly.CPolynomial F) (hnorms : ∀ i, norms i ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) (hT : 0 < T) :
    (retainedNormProduct p T norms).toPoly.eval₂ phi x = 0 ↔
      T ≤ ∑ i, ((norms i).toPoly.map phi).rootMultiplicity x := by
  rw [retainedNormProduct,
    eval₂_retainedMultiplicitySupport_eq_zero_iff_le_rootMultiplicity
      p T phi x (normProduct_ne_zero hnorms) hT,
    rootMultiplicity_normProduct_map norms hnorms phi x]

/-- The all-fiber threshold output has degree at most the product degree divided by `T` (stated
without natural-number division, so no rounding is hidden). -/
theorem threshold_mul_natDegree_retainedNormProduct_le
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {n : ℕ} (norms : Fin n → CompPoly.CPolynomial F) (hnorms : ∀ i, norms i ≠ 0)
    (hT : 0 < T) :
    T * (retainedNormProduct p T norms).natDegree ≤ (normProduct norms).natDegree := by
  exact threshold_mul_natDegree_retainedMultiplicitySupport_le
    p T (normProduct_ne_zero hnorms) hT

/-- Expanded form of the degree compression, exposing the sum of the individual norm degrees. -/
theorem threshold_mul_natDegree_retainedNormProduct_le_sum
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {n : ℕ} (norms : Fin n → CompPoly.CPolynomial F) (hnorms : ∀ i, norms i ≠ 0)
    (hT : 0 < T) :
    T * (retainedNormProduct p T norms).natDegree ≤ ∑ i, (norms i).natDegree := by
  rw [← natDegree_normProduct_eq_sum norms hnorms]
  exact threshold_mul_natDegree_retainedNormProduct_le p T norms hnorms hT

/-- Every candidate annihilating at least `T` individual nonzero norm factors survives the
all-fiber product filter. -/
theorem eval₂_retainedNormProduct_eq_zero_of_threshold_le_card
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    {n : ℕ} (norms : Fin n → CompPoly.CPolynomial F) (hnorms : ∀ i, norms i ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) (hT : 0 < T)
    (S : Finset (Fin n)) (hcard : T ≤ S.card)
    (hvanish : ∀ i ∈ S, (norms i).toPoly.eval₂ phi x = 0) :
    (retainedNormProduct p T norms).toPoly.eval₂ phi x = 0 := by
  rw [eval₂_retainedNormProduct_eq_zero_iff_sum_rootMultiplicity
    p T norms hnorms phi x hT]
  rw [← rootMultiplicity_normProduct_map norms hnorms phi x]
  exact hcard.trans (card_le_rootMultiplicity_normProduct_map_of_eval₂_eq_zero
    norms hnorms phi x S hvanish)

end ReedSolomon.ListDecoding.NormSieve
