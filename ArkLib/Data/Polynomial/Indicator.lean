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
  and the value `0` on `neg \ pos`. -/
noncomputable def indicator (pos neg : Finset F) : F[X] :=
  Lagrange.interpolate (pos ∪ neg) id 
    (fun x ↦ if x ∈ pos then 1 else 0) 

/-- The indicator polynomial is a constant zero polynomial 
  if the set `pos` is empty. 

  Note, `indicator ∅ ∅ = 0` too! -/
@[simp]
lemma indicator_eq_0_of_pos_empty {neg : Finset F} :
  indicator ∅ neg = 0 := by simp [indicator]

/-- The indicator polynomial is a constant one polynomial
  if the set `neg` is empty while `pos` is not. -/
lemma indicator_eq_1_of_neg_empty_empty_of_pos_nonempty
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
lemma indicator_ne_zero_of_pos_nonempty {pos neg : Finset F}
  (h : pos.Nonempty) :
  indicator pos neg ≠ 0 := by 
  unfold indicator
  intro contra 
  obtain ⟨x, hx⟩ := h
  have := congr_arg (Polynomial.eval x) contra 
  simp only [Lagrange.interpolate_apply, MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_mem, Finset.union_inter_cancel_left, eval_zero] at this
  rw [Polynomial.eval_finset_sum, Finset.sum_eq_single x] at this 
    <;> aesop 
    (add simp 
      [Lagrange.basis, 
       sub_eq_zero, 
       Finset.prod_eq_zero_iff,
       Finset.mem_erase_of_ne_of_mem,
       Finset.mem_union_left,
       Lagrange.basisDivisor, 
       Polynomial.eval_prod])
    (add safe (by apply Finset.prod_eq_zero))
    
/-- Indicator evaluated on an element of `pos` is equal to 1. -/
lemma indicator_eq_1_on_pos {pos neg : Finset F} {x : F}
  (h_pos : x ∈ pos) :
  (indicator pos neg).eval x = 1 := by 
  unfold indicator
  have {x} {y} (hy : y ∈ (pos ∪ neg).erase x) : 
    (x - y)⁻¹ * (x - y) = 1 := 
      inv_mul_cancel₀ (sub_ne_zero_of_ne (by aesop))
  rw [Polynomial.eval]
  aesop 
      (add simp 
        [Polynomial.eval_prod, 
          Polynomial.eval₂_finset_sum, 
          Lagrange.basis,
          Finset.prod_eq_zero_iff,
          Lagrange.basis,
          Lagrange.basisDivisor, 
          Finset.prod_eq_one]) 
      (add safe [(by rw [Finset.sum_eq_single x])])

/-- The indicator polynomial is zero on `neg \ pos`. -/
lemma indicator_eq_0_on_neg_sub_pos {pos neg : Finset F} {x : F}
  (h_pos : x ∈ neg \ pos) :
  (indicator pos neg).eval x = 0 := by 
  have h_basis_zero : ∀ y ∈ pos, Polynomial.eval x (Lagrange.basis (pos ∪ neg) id y) = 0 := by
    aesop 
      (add simp [Finset.mem_sdiff, Lagrange.basis, id_eq, eval_prod])
      (add safe [(by rw [Finset.prod_eq_zero])])
  aesop (add simp [indicator, Polynomial.eval_finset_sum, Finset.sum_eq_zero])

/-- The degree of the indicator polynomial 
  is less than `#(pos ∪ neg)`. -/
lemma indicator_degree_lt {pos neg : Finset F} :
  (indicator pos neg).degree < (pos ∪ neg).card := by
  unfold indicator 
  exact Lagrange.degree_interpolate_lt _ (by simp)

/-- The natDegree of the indicator polynomial 
  is less than `#(pos ∪ neg)` when `pos` is non-empty. -/
lemma indicator_natDegree_lt_of_pos_nonempty {pos neg : Finset F}
  (h : pos.Nonempty) :
  (indicator pos neg).natDegree < (pos ∪ neg).card := by
  rw [Polynomial.natDegree_lt_iff_degree_lt 
        (indicator_ne_zero_of_pos_nonempty h)]
  exact indicator_degree_lt

/-- The natDegree of the indicator polynomial 
  is less than `#(pos ∪ neg)` when `neg` is non-empty. -/
lemma indicator_natDegree_lt_of_neg_nonempty {pos neg : Finset F}
  (h : neg.Nonempty) :
  (indicator pos neg).natDegree < (pos ∪ neg).card := by
  by_cases hpos : pos.Nonempty
  · exact indicator_natDegree_lt_of_pos_nonempty hpos
  · aesop 

/-- If `pos` is a subset of `neg` then the degree of
  the indicator polynomial is less than `#neg`. -/
lemma indicator_degree_lt_of_pos_subset_neg {pos neg : Finset F}
  (h : pos ⊆ neg)
  :
  (indicator pos neg).degree < neg.card := 
    lt_of_lt_of_le indicator_degree_lt <| by
    rw [←Finset.union_eq_right] at h
    simp [h]

/-- If `pos` is a subset of `neg` then the natDegree of
  the indicator polynomial is less than `#neg` when `pos` is nonempty. -/
lemma indicator_natDegree_lt_of_pos_nonempty_of_pos_subset_neg {pos neg : Finset F}
  (h_nonEmpty : pos.Nonempty)
  (h : pos ⊆ neg) :
  (indicator pos neg).natDegree < neg.card := by
  rw [Polynomial.natDegree_lt_iff_degree_lt 
        (indicator_ne_zero_of_pos_nonempty h_nonEmpty)]
  exact indicator_degree_lt_of_pos_subset_neg h

/-- If `pos` is a subset of `neg` then the natDegree of
  the indicator polynomial is less than `#neg` when `neg` is nonempty. -/
lemma indicator_natDegree_lt_of_neg_nonempty_of_pos_subset_neg {pos neg : Finset F}
  (h_nonEmpty : neg.Nonempty)
  (h : pos ⊆ neg)
  :
  (indicator pos neg).natDegree < neg.card := by
  by_cases h_pos : pos.Nonempty
  · exact indicator_natDegree_lt_of_pos_nonempty_of_pos_subset_neg h_pos h
  · rw [Finset.not_nonempty_iff_eq_empty] at h_pos
    simp [h_pos, h_nonEmpty]

section SingletonIndicator

variable {x : F}

/-- A special case of an indicator polynomial. 
  The subset `pos` is a singleton `{x}`. -/
noncomputable def singletonIndicator (x : F) (S : Finset F) : F[X]
  := indicator {x} S

/-- Singleton indicator polynomial is a constant one polynomial
  when `S` is empty. -/
@[simp]
lemma singleton_indicator_eq_1_empty :
  singletonIndicator x ∅ = 1 := by
  unfold singletonIndicator
  rw [indicator_eq_1_of_neg_empty_empty_of_pos_nonempty (by simp)]

/-- Singleton indicator evaluated on `x` is one. -/
@[simp]
lemma singleton_indicator_eval_self {S : Finset F} :
  (singletonIndicator x S).eval x = 1 := by
  unfold singletonIndicator
  rw [indicator_eq_1_on_pos (by simp)]

/-- Singleton indicator on `S \ {x}` is zero. -/
lemma singleton_indicator_eval_eq_zero_of_mem_sdiff {S : Finset F} {a : F}
  (h : a ∈ S \ {x}) :
  (singletonIndicator x S).eval a = 0 := by
  unfold singletonIndicator
  rw [indicator_eq_0_on_neg_sub_pos (by simp [h])]

/-- The degree of the singleton indicator is less than `#S`. -/
lemma singleton_indicator_degree_lt_of_mem {S : Finset F}
  (h : x ∈ S) :
  (singletonIndicator x S).degree < S.card := by
  unfold singletonIndicator
  exact indicator_degree_lt_of_pos_subset_neg (by simp [h])

/-- The natDegree of the singleton indicator is less than `#S`. -/
lemma singleton_indicator_natDegree_lt_of_mem {S : Finset F}
  (h : x ∈ S) :
  (singletonIndicator x S).natDegree < S.card := by
  unfold singletonIndicator
  exact indicator_natDegree_lt_of_pos_nonempty_of_pos_subset_neg (by simp) (by simp [h])

end SingletonIndicator

end

end Polynomial
