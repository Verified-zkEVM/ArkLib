/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Degrees of curried polynomials

A polynomial in `S₁ ⊕ S₂` can be read as a polynomial in `S₁` with coefficients in `S₂`.
A weighted degree of the flat polynomial bounds, monomial by monomial, the outer weight plus the
total degree of the coefficient.

## Main statements

* `MvPolynomial.sumAlgEquiv_monomial`: currying a monomial.
* `MvPolynomial.coeff_coeff_sumAlgEquiv`: coefficients of the curried polynomial.
* `MvPolynomial.totalDegree_coeff_add_weight_sumAlgEquiv_symm_le`: the monomialwise degree bound.
-/

@[expose] public section

namespace MvPolynomial

variable {R S₁ S₂ : Type*} [CommSemiring R]

/-- A monomial in `S₁ ⊕ S₂` curries to a monomial in `S₁` with a monomial coefficient. -/
theorem sumAlgEquiv_monomial (k : S₁ ⊕ S₂ →₀ ℕ) (a : R) :
    sumAlgEquiv R S₁ S₂ (monomial k a) =
      monomial (Finsupp.sumFinsuppAddEquivProdFinsupp k).1
        (monomial (Finsupp.sumFinsuppAddEquivProdFinsupp k).2 a) := by
  simp only [Finsupp.sumFinsuppAddEquivProdFinsupp, Finsupp.sumFinsuppEquivProdFinsupp]
  ext s
  simp [sumAlgEquiv, monomial, Finsupp.comapDomain]

/-- Coefficients of the curried polynomial, read at the two halves of `k`, are those at `k`. -/
theorem coeff_coeff_sumAlgEquiv (p : MvPolynomial (S₁ ⊕ S₂) R) (k : S₁ ⊕ S₂ →₀ ℕ) :
    ((sumAlgEquiv R S₁ S₂ p).coeff (Finsupp.sumFinsuppAddEquivProdFinsupp k).1).coeff
      (Finsupp.sumFinsuppAddEquivProdFinsupp k).2 = p.coeff k := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial j a =>
    rw [sumAlgEquiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : j = k
    · subst h
      simp
    · have hne : ¬((Finsupp.sumFinsuppAddEquivProdFinsupp j).1 =
          (Finsupp.sumFinsuppAddEquivProdFinsupp k).1 ∧
          (Finsupp.sumFinsuppAddEquivProdFinsupp j).2 =
            (Finsupp.sumFinsuppAddEquivProdFinsupp k).2) := by
        rintro ⟨h1, h2⟩
        exact h (Finsupp.sumFinsuppAddEquivProdFinsupp.injective (Prod.ext h1 h2))
      rw [ite_eq_right_iff.mpr fun h' ↦ absurd h' h]
      split_ifs with h1 <;> simp_all
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]

/-- For a monomial `m` of `P`, its `w`-weight plus its coefficient degree is bounded by `P` flat.

The flat weight is `w` on `S₁` and `1` on `S₂`. -/
theorem totalDegree_coeff_add_weight_sumAlgEquiv_symm_le (w : S₁ → ℕ)
    (P : MvPolynomial S₁ (MvPolynomial S₂ R)) {m : S₁ →₀ ℕ} (hm : m ∈ P.support) :
    (P.coeff m).totalDegree + Finsupp.weight w m ≤
      ((sumAlgEquiv R S₁ S₂).symm P).weightedTotalDegree (Sum.elim w 1) := by
  classical
  obtain ⟨k, hk, hdeg⟩ := Finset.exists_mem_eq_sup (P.coeff m).support
    (support_nonempty.mpr (mem_support_iff.mp hm)) fun s ↦ s.sum fun _ e ↦ e
  set K := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (m, k)
  have hK : ((sumAlgEquiv R S₁ S₂).symm P).coeff K ≠ 0 := by
    rw [← coeff_coeff_sumAlgEquiv, AlgEquiv.apply_symm_apply]
    simp only [K, AddEquiv.apply_symm_apply]
    exact mem_support_iff.mp hk
  have hle := le_weightedTotalDegree (Sum.elim w 1) (mem_support_iff.mpr hK)
  have hweight : Finsupp.weight (Sum.elim w 1) K =
      Finsupp.weight w m + k.sum fun _ e ↦ e := by
    simp only [K, Finsupp.weight_apply]
    rw [Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply, Finsupp.sum_sumElim]
    simp [Finsupp.sum]
  rw [totalDegree, hdeg]
  omega

end MvPolynomial
