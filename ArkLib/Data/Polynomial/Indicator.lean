/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/
import ArkLib.Data.Polynomial.Bivariate

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombinationPrime

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

private lemma indicator_eval_of_mem_union {pos neg : Finset F} {x : F}
    (hx : x ∈ pos ∪ neg) :
    (indicator pos neg).eval x = if x ∈ pos then 1 else 0 := by
  unfold indicator
  simpa only [id_eq] using
    Lagrange.eval_interpolate_at_node (fun y : F => if y ∈ pos then 1 else 0)
      Function.injective_id.injOn hx

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
  rw [Finset.nonempty_iff_ne_empty] at h_pos
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (pos ∪ ∅) _ _
  · apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt _ _)
    · unfold indicator
      convert Lagrange.degree_interpolate_lt _ _
      aesop
    · simpa using Finset.card_pos.mpr (Finset.nonempty_of_ne_empty h_pos)
  · intro x hx
    have hxpos : x ∈ pos := by simpa using hx
    have heval := indicator_eval_of_mem_union (pos := pos) (neg := ∅) hx
    simpa [hxpos] using heval

/-- If `pos` is non-empty then the indicator polynomial is the constant
  zero polynomial. -/
lemma indicator_ne_zero_of_pos_nonempty {pos neg : Finset F}
  (h : pos.Nonempty) :
  indicator pos neg ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ := h
  have heval := indicator_eval_of_mem_union (neg := neg) (Finset.mem_union_left neg hx)
  rw [if_pos hx, hzero, eval_zero] at heval
  exact zero_ne_one heval

/-- Indicator evaluated on an element of `pos` is equal to 1. -/
lemma indicator_eq_1_on_pos {pos neg : Finset F} {x : F}
  (h_pos : x ∈ pos) :
  (indicator pos neg).eval x = 1 := by
  simpa [h_pos] using
    indicator_eval_of_mem_union (neg := neg) (Finset.mem_union_left neg h_pos)

/-- The indicator polynomial is zero on `neg \ pos`. -/
lemma indicator_eq_0_on_neg_sub_pos {pos neg : Finset F} {x : F}
  (h_pos : x ∈ neg \ pos) :
  (indicator pos neg).eval x = 0 := by
  have hmem := Finset.mem_sdiff.mp h_pos
  simpa [hmem.2] using
    indicator_eval_of_mem_union (pos := pos) (neg := neg)
      (Finset.mem_union_right pos hmem.1)

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
