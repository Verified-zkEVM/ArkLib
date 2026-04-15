/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import ArkLib.Data.MvPolynomial.Degrees
import Mathlib.Data.FinEnum

/-!
  # Interpolation of multivariate polynomials

  Theory of interpolation for `MvPolynomial` with individual bounds on `degreeOf`. Follows from a
  combination of the univariate case (see `Lagrange.lean`) and the tensor structure of
  `MvPolynomial`.

  ## Main definitions

  ### Notation

  ## Tags
  multivariate polynomial, interpolation, multivariate Lagrange
-/

noncomputable section

namespace MvPolynomial

open Finset

section SchwartzZippel

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

lemma schwartz_zippel_of_fintype [Fintype σ] {p : MvPolynomial σ R} (hp : p ≠ 0)
    (S : σ → Finset R) :
    #{x ∈ S ^^ σ | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤ ∑ i, (p.degreeOf i / #(S i) : ℚ≥0) := by
  let equiv : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have lem_of_equiv := by
    refine schwartz_zippel_sum_degreeOf (p := renameEquiv R equiv p) ?_ (S ∘ equiv.symm)
    exact rename_ne_zero_of_injective equiv.injective hp
  convert lem_of_equiv
  · refine Finset.card_bijective (fun f => f ∘ equiv.symm) ?_ ?_
    · exact Function.Bijective.comp_right (Equiv.bijective equiv.symm)
    · intro i
      simp only [mem_filter, Fintype.mem_piFinset, renameEquiv_apply, Function.comp_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact And.intro (by simp [h1]) (by simp [h2, eval_rename, Function.comp_assoc])
      · rintro ⟨h1, h2⟩
        constructor
        · intro a
          have := h1 (equiv a)
          simpa [this]
        · simpa [eval_rename, Function.comp_assoc] using h2
  · exact prod_equiv equiv (by simp) (by simp)
  · refine sum_equiv equiv (by simp) ?_
    simp only [mem_univ, renameEquiv_apply, Function.comp_apply, Equiv.symm_apply_apply,
      forall_const]
    intro i
    congr
    symm
    exact degreeOf_rename_of_injective (Equiv.injective equiv) i

def Function.extendDomain {α β : Type*} [DecidableEq α] [Zero β] {s : Finset α}
    (f : (x : α) → (x ∈ s) → β) : α → β :=
  fun x ↦ if hx : x ∈ s then f x hx else 0

open Function in
lemma schwartz_zippel' [Finite σ] {p : MvPolynomial σ R} (hp : p ≠ 0) (S : σ → Finset R) :
    #{x ∈ Finset.pi p.vars S | eval (extendDomain x) p = 0} / ∏ i ∈ p.vars, (#(S i) : ℚ≥0)
      ≤ ∑ i ∈ p.vars, (p.degreeOf i / #(S i) : ℚ≥0) := by
  letI : Fintype σ := Fintype.ofFinite σ
  let S' : σ → Finset R := fun i ↦ if i ∈ p.vars then S i else {0}
  have hsz := schwartz_zippel_of_fintype (p := p) hp S'
  convert hsz using 1
  · congr! 1
    · refine congr_arg _ (Finset.card_bij ?_ ?_ ?_ ?_)
      · intro a _ i
        exact if hi : i ∈ p.vars then a i hi else 0
      · intro a ha
        rcases Finset.mem_filter.mp ha with ⟨ha_pi, ha_eval⟩
        have ha_mem : ∀ i, ∀ hi : i ∈ p.vars, a i hi ∈ S i := by
          rwa [Finset.mem_pi] at ha_pi
        refine Finset.mem_filter.mpr ?_
        constructor
        · rw [Fintype.mem_piFinset]
          intro i
          by_cases hi : i ∈ p.vars
          · simpa [S', hi] using ha_mem i hi
          · simp [S', hi]
        · simpa [extendDomain] using ha_eval
      · intro a₁ ha₁ a₂ ha₂ h
        funext i hi
        have h' := congr_fun h i
        simpa [extendDomain, hi] using h'
      · intro b hb
        rcases Finset.mem_filter.mp hb with ⟨hb_pi, hb_eval⟩
        have hb_mem : ∀ i, b i ∈ S' i := by
          rwa [Fintype.mem_piFinset] at hb_pi
        have h_extend : extendDomain (s := p.vars) (fun i _hi ↦ b i) = b := by
          funext i
          by_cases hi : i ∈ p.vars
          · simp [extendDomain, hi]
          · have hzero : b i = 0 := by
              have : b i ∈ ({0} : Finset R) := by simpa [S', hi] using hb_mem i
              simpa using this
            simp [extendDomain, hi, hzero]
        refine ⟨fun i _hi ↦ b i, ?_, h_extend⟩
        · refine Finset.mem_filter.mpr ?_
          constructor
          · rw [Finset.mem_pi]
            intro i hi
            simpa [S', hi] using hb_mem i
          · simpa [h_extend] using hb_eval
    · rw [← Finset.prod_subset (Finset.subset_univ p.vars)]
      · refine Finset.prod_congr rfl ?_
        intro i hi
        simp [S', hi]
      · intro i _ hi
        simp [S', hi]
  · rw [← Finset.sum_subset (Finset.subset_univ p.vars)]
    · refine Finset.sum_congr rfl ?_
      intro x hx
      simp [S', hx]
    · intro x _ hx
      have hdeg : degreeOf x p = 0 := by
        rw [degreeOf]
        simp only [Multiset.count_eq_zero]
        rw [vars_def] at hx
        exact fun h => hx (Multiset.mem_toFinset.mpr h)
      simp [S', hx, hdeg]


end SchwartzZippel

section Vars

variable {σ : Type*}

-- Need more theorems about `MvPolynomial.vars`

-- Equivalence between `{p : R[X σ] | p.vars ⊆ s}` and `R[X {x : σ | x ∈ s}]`?
-- #check MvPolynomial.exists_fin_rename

instance (s : Finset σ) : Fintype { x : σ | x ∈ s } := by exact Set.fintypeMemFinset s

end Vars

section MvPolynomialDetermination

variable {σ : Type*} [DecidableEq σ] [Fintype σ]
variable {R : Type*} [CommRing R] [IsDomain R]

section Finset

open Function Fintype

variable {n : ℕ}

open Polynomial
/-- A polynomial is zero if its degrees are bounded and it is zero on the product set. -/
-- This does not follow from Schwartz-Zippel!
-- Instead we should do induction on the number of variables.
-- Hence we should state the theorem for `σ = Fin n` first.
theorem eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin {n : ℕ} {p : R[X Fin n]}
    (S : Fin n → Finset R) (hDegree : ∀ i, p.degreeOf i < (S i).card)
    (hEval : ∀ x ∈ piFinset fun i ↦ S i, eval x p = 0) :
        p = 0 := by
  induction n with
  | zero =>
    rw [eq_C_of_isEmpty p] at hEval ⊢
    simp_all only [IsEmpty.forall_iff, piFinset_of_isEmpty, univ_unique, mem_singleton, eval_C,
      forall_eq, C_0]
  | succ n ih =>
    let q : R[X Fin n][X] := finSuccEquiv R n p
    let S' : Finset R[X Fin n] := (S 0).map CEmbedding
    have hCard : #S' = #(S 0) := Finset.card_map CEmbedding
    have hDegreeQ : q.natDegree < #S' := by
      have h := hDegree 0
      rwa [←natDegree_finSuccEquiv, ←hCard] at h
    have hEvalQ : ∀ x ∈ (S 0), q.eval (C x) = 0 := by
      unfold q
      intro x hx
      let px := q.eval (C x)
      have hDegreePx (i : Fin n) : px.degreeOf i < (S i.succ).card :=
        lt_of_le_of_lt (degreeOf_eval_C_finSuccEquiv p i x) (hDegree i.succ)
      have hEvalPx : ∀ y ∈ piFinset fun (i : Fin n) ↦ S i.succ, eval y px = 0 := by
        intro y hy
        change eval y (Polynomial.eval (C x) (finSuccEquiv R n p)) = 0
        rw [eval_comp_eval_C_finSuccEquiv]
        have hy' := Fintype.mem_piFinset.mp hy
        have : Fin.cons x y ∈ piFinset fun i ↦ S i := by
          rw [Fintype.mem_piFinset]
          intro a
          induction a using Fin.inductionOn with
          | zero => simpa using hx
          | succ i => simpa using hy' i
        simpa using hEval (Fin.cons x y) this
      simpa [px] using ih (fun i => S i.succ) hDegreePx hEvalPx
    have hEvalQ' : ∀ x ∈ S', q.eval x = 0 := fun x hx => by
      obtain ⟨y, hy, hEq⟩ := Finset.mem_map.mp hx
      subst hEq
      exact hEvalQ y hy
    have hZero : q = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q S' hEvalQ' hDegreeQ
    exact EmbeddingLike.map_eq_zero_iff.mp hZero

theorem eq_zero_of_degreeOf_lt_card_of_eval_eq_zero {p : R[X σ]} (S : σ → Finset R)
    (hDegree : ∀ i, p.degreeOf i < #(S i))
    (hEval : ∀ x ∈ piFinset fun i ↦ S i, eval x p = 0) : p = 0 := by
  let equiv : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let q := rename equiv p
  let S' := S ∘ equiv.symm
  have hDegree' : ∀ i, q.degreeOf i < #(S' i) := fun i => by
    convert hDegree (equiv.symm i)
    rw [← Equiv.apply_symm_apply equiv i]
    simp only [q, degreeOf_rename_of_injective equiv.injective]
    simp only [Equiv.apply_symm_apply]
  have hEval' : ∀ x ∈ piFinset fun i ↦ S' i, eval x q = 0 := fun x hx => by
    let y := x ∘ equiv
    have hy : y ∈ piFinset fun i ↦ S i := by
      rw [Fintype.mem_piFinset] at hx ⊢
      intro a
      simpa [y, S', Equiv.symm_apply_apply] using hx (equiv a)
    convert hEval y hy
    simp [q, y, eval_rename]
  have hq : q = 0 := eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin S' hDegree' hEval'
  exact rename_eq_zero_of_injective equiv.injective (by simpa [q] using hq)

/-- Equality of multivariable polynomials when they agree on a product of sets and have
    degree bounds on both (per-variable degree less than set size). -/
theorem eq_of_degreeOf_lt_card_of_eval_eq {p q : R[X σ]} (S : σ → Finset R)
    (hDegreeP : ∀ i, p.degreeOf i < #(S i))
    (hDegreeQ : ∀ i, q.degreeOf i < #(S i))
    (hEval : ∀ x ∈ piFinset fun i ↦ S i, eval x p = eval x q) : p = q := by
  have h : p - q = 0 :=
    eq_zero_of_degreeOf_lt_card_of_eval_eq_zero S
      (fun i ↦ lt_of_le_of_lt (degreeOf_sub_le i p q) (max_lt (hDegreeP i) (hDegreeQ i)))
      (fun x hx ↦ by simp [hEval x hx])
  exact sub_eq_zero.mp h

end Finset


end MvPolynomialDetermination

section Interpolation

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} {i j : ι}

/-- Define basis polynomials for interpolation -/
protected def basis : F := sorry

end Interpolation


end MvPolynomial

end
