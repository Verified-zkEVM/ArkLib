/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/
import ArkLib.Data.Polynomial.Bivariate

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'

/-! This module is mostly needed from proving lemma 4.9
  from [ACFY24] but we thought it might be useful for 
  something else as well. 

## References

* [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E., 
  *STIR: Reed–Solomon Proximity Testing with Fewer Queries*][ACFY24]
-/

namespace Polynomial

section

open Polynomial Polynomial.Bivariate 

variable {ι F : Type*} [Field F] [DecidableEq F]

/-- The indicator polynomial is a univariate polynomial
  `I(X)` of the minimal degree 
  that takes the value `1` on a given finset `pos`
  and the value `0` on `neg`. -/
noncomputable def indicator (pos neg : Finset F) : F[X] :=
  Lagrange.interpolate (pos ∪ neg) id 
    (fun x ↦ if x ∈ pos then 1 else 0) 

/-- The indicator polynomial is a constant zero polynomial 
  if the set `pos` is empty. 

  Note, `indicator ∅ ∅ = 0` too! -/
@[simp]
lemma indicator_is_0_if_pos_empty {neg : Finset F} :
  indicator ∅ neg = 0 := by simp [indicator]

/-- The indicator polynomial is a constant one polynomial
  if the set `neg` is empty while `pos` is not. -/
lemma indicator_is_1_if_neg_is_empty_and_pos_non_empty
  {pos : Finset F}
  (h_pos : pos.Nonempty) : 
  indicator pos ∅ = 1 := by 
  unfold indicator
  rw [Finset.nonempty_iff_ne_empty] at h_pos
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (pos ∪ ∅) _ _
  · apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt _ _)
    · convert Lagrange.degree_interpolate_lt _ _ 
      aesop
    · simpa using Finset.card_pos.mpr (Finset.nonempty_of_ne_empty h_pos)
  · have {x} {y} (hy : y ∈ pos.erase x) : 
      (x - y)⁻¹ * (x - y) = 1 := 
        inv_mul_cancel₀ (sub_ne_zero_of_ne (by aesop))
    aesop 
      (add simp 
        [Polynomial.eval_prod, 
          Finset.prod_eq_zero_iff,
          Lagrange.basis,
          Lagrange.basisDivisor, 
          Finset.prod_eq_one]) 
      (add safe [(by rw 
        [Polynomial.eval_finset_sum, 
        Finset.sum_eq_single x])])
    
/-- If `pos` is non-empty then the indicator polynomial is the constant 
  zero polynomial. -/
lemma indicator_ne_if_pos_is_nonempty {pos neg : Finset F}
  (h : pos.Nonempty) :
  indicator pos neg ≠ 0 := by 
  unfold indicator
  obtain ⟨x, hx⟩ := h
  intro contra 
  have := congr_arg (Polynomial.eval x) contra 
  norm_num [ hx, Lagrange.eval_interpolate_at_node ] at this;
  rw [ Polynomial.eval_finset_sum, Finset.sum_eq_single x ] at this 
    <;> simp_all +decide [ Lagrange.basis ];
  · simp_all +decide [ Polynomial.eval_prod, Finset.prod_eq_zero_iff, Lagrange.basisDivisor ];
    exact this.elim fun a ha => ha.1.1 ( sub_eq_zero.mp ha.2 ▸ rfl );
  · intro y hy hyx; 
    rw [ Polynomial.eval_prod ] ; 
    exact Finset.prod_eq_zero 
      ( Finset.mem_erase_of_ne_of_mem 
          ( Ne.symm hyx ) 
          ( Finset.mem_union_left _ hx ) ) ( by simp +decide [ Lagrange.basisDivisor ] ) ;

lemma indicator_eq_1_on_pos {pos neg : Finset F} {x : F}
  (h_pos : x ∈ pos)
  :
  (indicator pos neg).eval x = 1 := by 
  unfold Polynomial.indicator;
  rw [ Polynomial.eval];
  simp +decide [ Polynomial.eval₂_finset_sum, Lagrange.basis ];
  rw [ Finset.sum_eq_single x ] <;> 
    simp_all +decide [ Polynomial.eval_prod, Finset.prod_eq_zero_iff, Lagrange.basisDivisor ];
  · exact Finset.prod_eq_one fun y hy 
      => by rw [ inv_mul_cancel₀ ] ; exact sub_ne_zero_of_ne <| by aesop;
  · exact fun y hy hyx => ⟨ x, ⟨ Ne.symm hyx, Or.inl h_pos ⟩, Or.inr ( sub_self x ) ⟩

lemma indicator_eq_0_on_neg_sub_pos {pos neg : Finset F} {x : F}
  (h_pos : x ∈ neg \ pos)
  :
  (indicator pos neg).eval x = 0 := by 
  simp [Polynomial.indicator];
  have h_basis_zero : ∀ y ∈ pos, Polynomial.eval x (Lagrange.basis (pos ∪ neg) id y) = 0 := by
    simp_all +decide only [Finset.mem_sdiff, Lagrange.basis, id_eq];
    intro y hy; 
    rw [ Polynomial.eval_prod, Finset.prod_eq_zero 
          ( Finset.mem_erase_of_ne_of_mem 
              ( by aesop ) 
              ( Finset.mem_union_right _ h_pos.1 ) ) ] ; 
    simp +decide [ Lagrange.basisDivisor ] ;
  rw [ Polynomial.eval_finset_sum, Finset.sum_eq_zero h_basis_zero ]

lemma indicator_degree_lt {pos neg : Finset F} :
  (indicator pos neg).degree < (pos ∪ neg).card := by
  unfold indicator 
  apply Lagrange.degree_interpolate_lt
  simp

lemma indicator_natDegree_lt {pos neg : Finset F}
  (h : pos.Nonempty)
  :
  (indicator pos neg).natDegree < (pos ∪ neg).card := by
  rw [Polynomial.natDegree_lt_iff_degree_lt 
        (indicator_ne_if_pos_is_nonempty h)]
  exact indicator_degree_lt

lemma indicator_natDegree_lt' {pos neg : Finset F}
  (h : neg.Nonempty)
  :
  (indicator pos neg).natDegree < (pos ∪ neg).card := by
  by_cases hpos: pos.Nonempty
  · exact indicator_natDegree_lt hpos
  · aesop 

lemma indicator_degree_lt_of_pos_subset_neg {pos neg : Finset F}
  (h : pos ⊆ neg)
  :
  (indicator pos neg).degree < neg.card := by
  apply lt_of_lt_of_le (indicator_degree_lt)
  rw [←Finset.union_eq_right] at h
  rw [h]

lemma indicator_natDegree_lt_of_pos_subset_neg {pos neg : Finset F}
  (h_nonEmpty : pos.Nonempty)
  (h : pos ⊆ neg)
  :
  (indicator pos neg).natDegree < neg.card := by
  rw [Polynomial.natDegree_lt_iff_degree_lt 
        (indicator_ne_if_pos_is_nonempty h_nonEmpty)]
  exact indicator_degree_lt_of_pos_subset_neg h

lemma indicator_natDegree_lt_of_pos_subset_neg' {pos neg : Finset F}
  (h_nonEmpty : neg.Nonempty)
  (h : pos ⊆ neg)
  :
  (indicator pos neg).natDegree < neg.card := by
  by_cases h_pos : pos.Nonempty
  · exact indicator_natDegree_lt_of_pos_subset_neg h_pos h
  · rw [Finset.not_nonempty_iff_eq_empty] at h_pos
    simp [h_pos, h_nonEmpty]

section SingletonIndicator

variable {x : F}

noncomputable def singletonIndicator (x : F) (S : Finset F) : F[X]
  := indicator {x} S

@[simp]
lemma singleton_indicator_eq_1 :
  singletonIndicator x ∅ = 1 := by
  unfold singletonIndicator
  rw [indicator_is_1_if_neg_is_empty_and_pos_non_empty (by simp)]

@[simp]
lemma singleton_indicator_eq_1_on_x {S : Finset F} :
  (singletonIndicator x S).eval x = 1 := by
  unfold singletonIndicator
  rw [indicator_eq_1_on_pos (by simp)]

lemma singleton_indicator_eq_0_on_S_minus_x {S : Finset F} {a : F}
  (h : a ∈ S \ {x})
  :
  (singletonIndicator x S).eval a = 0 := by
  unfold singletonIndicator
  rw [indicator_eq_0_on_neg_sub_pos (by simp [h])]

lemma singleton_indicator_degree_lt_of_mem {S : Finset F} 
  (h : x ∈ S)
  :
  (singletonIndicator x S).degree < S.card := by
  unfold singletonIndicator
  exact indicator_degree_lt_of_pos_subset_neg (by simp [h])

lemma singleton_indicator_natDegree_lt_of_mem {S : Finset F} 
  (h : x ∈ S)
  :
  (singletonIndicator x S).natDegree < S.card := by
  unfold singletonIndicator
  exact indicator_natDegree_lt_of_pos_subset_neg (by simp) (by simp [h])


end SingletonIndicator

end

end Polynomial
