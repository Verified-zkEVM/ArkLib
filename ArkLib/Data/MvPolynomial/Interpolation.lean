/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import ArkLib.Data.MvPolynomial.Degrees
public import Mathlib.Data.FinEnum

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

@[expose] public section

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

open _root_.MvPolynomial.Function in
lemma schwartz_zippel' {p : MvPolynomial σ R} (hp : p ≠ 0) (S : σ → Finset R) :
    #{x ∈ Finset.pi p.vars S | eval (extendDomain x) p = 0} / ∏ i ∈ p.vars, (#(S i) : ℚ≥0)
      ≤ ∑ i ∈ p.vars, (p.degreeOf i / #(S i) : ℚ≥0) := by
  obtain ⟨q, hq⟩ := exists_rename_coe_vars_eq p
  have heval (a : (i : σ) → i ∈ p.vars → R) :
      eval (extendDomain a) p = eval (fun i : p.vars => a i i.property) q := by
    conv_lhs => arg 2; rw [← hq]
    simp [eval_rename, extendDomain, Function.comp_def]
  have hsz := schwartz_zippel_of_fintype (p := q)
    (fun hz => hp (by simpa [hz] using hq.symm)) (fun i : p.vars => S i)
  convert hsz using 1
  · congr! 1
    · refine congr_arg _ (Finset.card_bij (fun a _ (i : p.vars) => a i i.property) ?_ ?_ ?_)
      · intro a ha
        simpa [mem_filter, mem_pi, Fintype.mem_piFinset, ← heval] using ha
      · intro a ha b hb hab
        funext i hi
        exact congr_fun hab ⟨i, hi⟩
      · intro b hb
        refine ⟨fun i hi => b ⟨i, hi⟩, ?_, rfl⟩
        simpa [mem_filter, mem_pi, Fintype.mem_piFinset, heval] using hb
    · exact (Finset.prod_coe_sort p.vars _).symm
  · rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← degreeOf_rename_of_injective Subtype.val_injective i, hq]


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

open _root_.MvPolynomial.Function Fintype

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
    -- The head-variable root count is shared with the nested-tree zero test; only `hEvalQ`
    -- differs between the two (product set here, `k` subtrees there).
    refine eq_zero_of_degreeOf_zero_lt_card_of_eval_C_eq_zero (S 0) (hDegree 0) ?_
    intro x hx
    let px := Polynomial.eval (C x) (finSuccEquiv R n p)
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

theorem eq_zero_of_degreeOf_lt_card_of_eval_eq_zero {p : R[X σ]} (S : σ → Finset R)
    (hDegree : ∀ i, p.degreeOf i < #(S i))
    (hEval : ∀ x ∈ piFinset fun i ↦ S i, eval x p = 0) : p = 0 := by
  let equiv : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let q := rename equiv p
  let S' := S ∘ equiv.symm
  have hDegree' : ∀ i, q.degreeOf i < #(S' i) := fun i => by
    convert hDegree (equiv.symm i)
    · rw [← Equiv.apply_symm_apply equiv i]
      simp only [q, degreeOf_rename_of_injective equiv.injective]
      simp
    · simp only [S', Function.comp_apply]
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

end MvPolynomial

end
