/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.Notation
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian

/-!
# Monomial basis for algebra extensions
-/

namespace Polynomial

section MonomialBasis

-- Fix a binary field `L` of degree `r` over its prime subfield `K`
variable {K : Type*} {L : Type*} [CommSemiring K] [Field L]
variable [Algebra K L]
-- We assume an `K`-basis for `L`, denoted by `(β₀, β₁, ..., β_{r-1})`, indexed by natural numbers.
variable (β : Nat → L) (hβ_lin_indep : LinearIndependent K β)

@[simp]
theorem sum_degreeLT_monomial_eq_subtype {n : ℕ} (p : L⦃< n⦄[X]) :
  (⟨p.val.sum (fun n a => Polynomial.monomial n a), by
    -- degree of sum is degree of p.val, which is < n
    rw [Polynomial.sum_monomial_eq p.val]
    exact p.property
  ⟩ : L⦃< n⦄[X]) = p :=
      -- `span_le` changes the goal to showing every vector in the generating set
  Subtype.eq (Polynomial.sum_monomial_eq p.val)

noncomputable def monomialBasisOfDegreeLT {n : ℕ} : Basis (Fin n) L (L⦃< n⦄[X]) := by
  set monomials_in_submodule:Fin n → L⦃< n⦄[X] := fun ⟨i, hi⟩ =>
  ⟨monomial (R := L) (n := i) (a := 1), by
    simp only [Polynomial.mem_degreeLT]
    simp only [ne_eq, one_ne_zero, not_false_eq_true, degree_monomial, Nat.cast_lt]
    exact hi
  ⟩

  have h_li_submodule : LinearIndependent L monomials_in_submodule := by
    rw [linearIndependent_iff] -- alternative : linearIndependent_powers_iff_aeval
    intro l hl -- l : Fin n →₀ L, hl : (Finsupp.linearCombination L monomials_in_submodule) l = 0
    apply Finsupp.ext -- ⊢ ∀ (a : Fin n), l a = 0 a
    intro i
    have h_poly_eq_zero : (Finsupp.linearCombination L monomials_in_submodule l).val = 0 := by
      -- converts the equality of subtypes `hl` to an equality of values
      exact Subtype.ext_iff.mp hl

    have h_coeff_eq_li :
      coeff (Finsupp.linearCombination L monomials_in_submodule l).val i = l i := by
      -- `span_le` changes the goal to showing every vector in the generating set
      set v := monomials_in_submodule
      simp only [v, monomials_in_submodule, monomial_one_right_eq_X_pow]
      rw [Finsupp.linearCombination_apply]
      simp only [SetLike.mk_smul_mk]
      conv =>
        lhs
        simp only [Finsupp.sum, AddSubmonoidClass.coe_finset_sum, finset_sum_coeff, coeff_smul,
          coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, monomials_in_submodule, v]
      -- ⊢ (∑ x ∈ l.support, if ↑i = ↑x then l x else 0) = l i
      simp_rw [Fin.val_eq_val, eq_comm]
      -- ⊢ l i = ∑ x ∈ l.support, if i = x then l x else 0
      by_cases h_i_in_l_support : i ∈ l.support
      -- `span_le` changes the goal to showing every vector in the generating set
      · rw [Finset.sum_ite_eq_of_mem] -- ⊢ represent l i as a sum over l.support
        exact h_i_in_l_support
      · have l_i_is_zero : l i = 0 := by
          exact Finsupp.notMem_support_iff.mp h_i_in_l_support
        simp only [l_i_is_zero, Finset.sum_ite_eq, Finsupp.mem_support_iff, ne_eq,
          not_true_eq_false, ↓reduceIte]
    rw [h_poly_eq_zero] at h_coeff_eq_li
    simp only [coeff_zero] at h_coeff_eq_li
    exact h_coeff_eq_li.symm

  have h_span_submodule : Submodule.span (R := L) (Set.range monomials_in_submodule) = ⊤ :=by
    apply le_antisymm
    · -- First goal : Prove that your span is a subspace of the whole space.
      -- `span_le` changes the goal to showing every vector in the generating set
      rw [Submodule.span_le]
      -- ⊢ ↑(Finset.image (fun n ↦ X ^ n) (Finset.range n)) ⊆ ↑L⦃< n⦄[X]
      rw [Set.range_subset_iff] -- simp [Set.image_subset_image_iff]
      intro j -- `j` is an index for your family, e.g., `j : Fin n`
      -- ⊢ monomials_in_submodule j ∈ ↑⊤
      simp only [Submodule.top_coe, Set.mem_univ, monomials_in_submodule]
    · -- Second goal : Prove the whole space is a subspace of your span.
      rw [Submodule.top_le_span_range_iff_forall_exists_fun]
      intro p
      have hp := p.property
      have h_deg_p : p.val.degree < n := by
        rw [Polynomial.mem_degreeLT] at hp
        exact hp
      -- ⊢ ∃ c, ∑ i, c i • monomials_in_submodule i = p
      set c : Fin n → L := fun i => p.val.coeff i
      have h_c : c = fun (i : Fin n) => p.val.coeff i := by rfl
      use c
      -- ⊢ ∑ i, c i • monomials_in_submodule i = p
      apply Subtype.ext -- bring equality from ↑L⦃< n⦄[X] to L[X]
      rw [←sum_degreeLT_monomial_eq_subtype (p := p)] -- convert ↑p in rhs into (↑p).sum form
      conv =>
        rhs -- ↑⟨(↑p).sum fun n a ↦ (monomial n) a, ⋯⟩
        -- we have to convert (↑p).sum into Fin n → L form using Polynomial.sum_fin
        simp only [monomial_zero_right, implies_true, ←Polynomial.sum_fin (hn := h_deg_p)]
      -- ⊢ ↑(∑ i, c i • monomials_in_submodule i) = ∑ i, (monomial ↑i) ((↑p).coeff ↑i)
      rw [AddSubmonoidClass.coe_finset_sum] -- bring both sides back to L[X]
      apply Finset.sum_congr rfl
      intro ⟨i, hi_finN⟩ hi
      simp only [SetLike.mk_smul_mk, c, monomials_in_submodule]
      -- ⊢ (↑p).coeff i • (monomial i) 1 = (monomial i) ((↑p).coeff i)
      simp only [monomial_one_right_eq_X_pow]
      rw [←Polynomial.smul_X_eq_monomial]

  apply Basis.mk (R := L) (M := degreeLT (R := L) (n := n))
  · exact h_li_submodule
  · exact le_of_eq (hab := h_span_submodule.symm)

theorem finrank_degreeLT_n (n : ℕ) : Module.finrank L (L⦃< n⦄[X]) = n := by
  have monomial_basis : Basis (Fin n) (R := L) (M := L⦃< n⦄[X]) := monomialBasisOfDegreeLT (n := n)
  rw [Module.finrank_eq_card_basis monomial_basis]
  rw [Fintype.card_fin]

instance finiteDimensional_degreeLT {n : ℕ} (h_n_pos : 0 < n) :
  FiniteDimensional L L⦃< n⦄[X] := by
  have h : 0 < Module.finrank L (L⦃< n⦄[X]) := by
    rw [finrank_degreeLT_n n]
    omega
  exact FiniteDimensional.of_finrank_pos h

end MonomialBasis

end Polynomial
