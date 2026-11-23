/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Basic
public import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Substituting values for an initial segment of the variables

For variables indexed by a linear order `σ`, a point `x : σ → R` and `i : σ`,
`aeval (fun j ↦ if j ≤ i then C (x j) else X j)` substitutes `x j` for `X j` at every `j ≤ i`
and keeps the other variables, and likewise with `j < i`. The substitution at the variables `< i`
does not raise the degree in `X i`. A nonzero polynomial that vanishes at `x` has a first variable
`i` at which these substitutions become zero.

## Main statements

* `aeval_ite_lt_eq_zero_of_aeval_ite_le_eq_zero`: if the substitution at the variables `≤ i`
  vanishes, so does the substitution at the variables `< i'` for every `i' > i`.
* `aeval_ite_le_rename_swap`: the substitution at the variables `≤ i` commutes with swapping two
  variables larger than `i`.
* `degreeOf_aeval_ite_lt_le`: the substitution at the variables `< i` does not raise the degree in
  `X i`.
* `exists_aeval_ite_lt_ne_zero_and_aeval_ite_le_eq_zero`: with finitely many variables, a nonzero
  polynomial that vanishes at `x` has a variable `i` such that the substitution at the variables
  `< i` does not vanish and the substitution at the variables `≤ i` vanishes.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {σ R : Type*} [LinearOrder σ] [CommSemiring R] {x : σ → R}

/-- If substituting `x j` for `X j` at every `j ≤ i` makes `p` vanish and `i < i'`, then
substituting `x j` for `X j` at every `j < i'` makes `p` vanish. -/
theorem aeval_ite_lt_eq_zero_of_aeval_ite_le_eq_zero {i i' : σ} (hii' : i < i')
    {p : MvPolynomial σ R} (hp : aeval (fun j ↦ if j ≤ i then C (x j) else X j) p = 0) :
    aeval (fun j ↦ if j < i' then C (x j) else X j) p = 0 := by
  have key : (fun j ↦ aeval (fun j ↦ if j < i' then C (x j) else X j)
      (if j ≤ i then C (x j) else X j)) = fun j ↦ if j < i' then C (x j) else X j := by
    funext j
    by_cases hj : j ≤ i
    · simp [hj, hj.trans_lt hii']
    · simp [hj]
  rw [← key, ← comp_aeval, AlgHom.comp_apply, hp, map_zero]

/-- Substituting `x j` for `X j` at every `j ≤ i` commutes with swapping two variables `a` and `b`
larger than `i`. -/
theorem aeval_ite_le_rename_swap {i a b : σ} (ha : i < a) (hb : i < b) (p : MvPolynomial σ R) :
    aeval (fun j ↦ if j ≤ i then C (x j) else X j) (rename (Equiv.swap a b) p) =
      rename (Equiv.swap a b) (aeval (fun j ↦ if j ≤ i then C (x j) else X j) p) := by
  rw [aeval_rename, ← AlgHom.comp_apply, comp_aeval]
  refine congrArg (fun f ↦ aeval f p) (funext fun j ↦ ?_)
  by_cases hj : j ≤ i
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (hj.trans_lt ha).ne
      (hj.trans_lt hb).ne]
    simp [hj]
  · have hσ : ¬Equiv.swap a b j ≤ i := by
      rw [Equiv.swap_apply_def]
      split_ifs
      · exact not_le.2 hb
      · exact not_le.2 ha
      · exact hj
    simp [hj, hσ]

/-- Substituting `x j` for `X j` at every `j < i` does not raise the degree of `p` in `X i`. -/
theorem degreeOf_aeval_ite_lt_le (i : σ) (p : MvPolynomial σ R) :
    (aeval (fun j ↦ if j < i then C (x j) else X j) p).degreeOf i ≤ p.degreeOf i := by
  rw [aeval_def, eval₂_eq]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun s hs ↦ ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [algebraMap_eq, degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ j ∈ s.support, degreeOf i ((if j < i then C (x j) else X j) ^ s j)
      ≤ ∑ j ∈ s.support, if j = i then s j else 0 := sum_le_sum fun j _ ↦ ?_
    _ ≤ s i := by
      rw [sum_ite_eq']
      split_ifs <;> simp
    _ ≤ p.degreeOf i := monomial_le_degreeOf i hs
  rcases eq_or_ne j i with rfl | hji
  · simp only [lt_irrefl, ↓reduceIte]
    rw [X_pow_eq_monomial]
    exact degreeOf_le_iff.mpr fun d hd ↦ by
      rw [mem_singleton.mp (support_monomial_subset hd), Finsupp.single_eq_same]
  · simp only [hji, ↓reduceIte]
    split_ifs
    · rw [← C_pow, degreeOf_C]
    · rw [degreeOf_X_pow_of_ne _ (Ne.symm hji)]

/-- **First vanishing substitution.** With finitely many variables, a nonzero polynomial `p` that
vanishes at `x` has a variable `i` such that substituting `x j` for `X j` at every `j < i` does
not make `p` vanish, and substituting `x j` for `X j` at every `j ≤ i` does. -/
theorem exists_aeval_ite_lt_ne_zero_and_aeval_ite_le_eq_zero [Finite σ] {p : MvPolynomial σ R}
    (hp : p ≠ 0) (hx : aeval x p = 0) :
    ∃ i, aeval (fun j ↦ if j < i then C (x j) else X j) p ≠ 0 ∧
      aeval (fun j ↦ if j ≤ i then C (x j) else X j) p = 0 := by
  classical
  have := Fintype.ofFinite σ
  have hC : aeval (C (σ := σ) ∘ x) p = 0 := by rw [aeval_C_comp_left, hx, map_zero]
  set S : Finset σ := {i | aeval (fun j ↦ if j ≤ i then C (x j) else X j) p = 0}
  have hS : S.Nonempty := by
    rcases isEmpty_or_nonempty σ with hσ | ⟨⟨i₀⟩⟩
    · refine absurd ?_ hp
      rw [← aeval_X_left_apply p, show (X : σ → MvPolynomial σ R) = C ∘ x from
        funext isEmptyElim, hC]
    · refine ⟨univ.max' ⟨i₀, mem_univ _⟩, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
      rw [show (fun j ↦ if j ≤ univ.max' ⟨i₀, mem_univ _⟩ then C (x j) else X j) = C ∘ x from
        funext fun j ↦ ite_eq_left (le_max' _ _ (mem_univ j)), hC]
  refine ⟨S.min' hS, fun h0 ↦ ?_, (mem_filter.1 (S.min'_mem hS)).2⟩
  rcases ({j | j < S.min' hS} : Finset σ).eq_empty_or_nonempty with hT | hT
  · refine hp ?_
    rw [← aeval_X_left_apply p, ← h0]
    refine congrArg (fun f ↦ aeval f p) (funext fun j ↦ (ite_eq_right fun hj ↦ ?_).symm)
    exact eq_empty_iff_forall_notMem.1 hT j (mem_filter.2 ⟨mem_univ _, hj⟩)
  · have hj := (mem_filter.1 (max'_mem _ hT)).2
    refine (S.min'_le _ (mem_filter.2 ⟨mem_univ _, ?_⟩)).not_gt hj
    rw [← h0]
    refine congrArg (fun f ↦ aeval f p) (funext fun l ↦ if_congr ?_ rfl rfl)
    exact ⟨fun hl ↦ hl.trans_lt hj, fun hl ↦ le_max' _ l (mem_filter.2 ⟨mem_univ _, hl⟩)⟩

end MvPolynomial
