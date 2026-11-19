/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.LinearCombination

/-!
# Grid points on a hyperplane

Let `S` be a finite subset of a domain `R`, and consider the grid `Sⁿ⁺¹`.

A hyperplane `a ⬝ᵥ x = b` with `a ≠ 0` contains at most `#S ^ n` grid points.

Fix a coordinate `i` with `aᵢ ≠ 0`.

The other coordinates of a point on the hyperplane determine `xᵢ`, since `R` has no zero divisors.

Consequently, an affine form `σ₀ + σ' ⬝ᵥ x` that vanishes on more than `#S ^ n` grid points is zero.

## Main statements

* `Fintype.card_filter_piFinset_dotProduct_eq_le`: the hyperplane bound.
* `Fintype.eq_zero_of_forall_mem_add_dotProduct_eq_zero`: the vanishing of an affine form.
-/

@[expose] public section

namespace Fintype

open Finset

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-- A hyperplane `a ⬝ᵥ x = b` with `a ≠ 0` holds at most `#S ^ n` points of the grid `Sⁿ⁺¹`. -/
theorem card_filter_piFinset_dotProduct_eq_le {n : ℕ} (S : Finset R) {a : Fin (n + 1) → R}
    (ha : a ≠ 0) (b : R) :
    #{x ∈ piFinset fun _ ↦ S | a ⬝ᵥ x = b} ≤ #S ^ n := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  calc #{x ∈ piFinset fun _ ↦ S | a ⬝ᵥ x = b}
      ≤ #(piFinset fun _ : {j // j ≠ i} ↦ S) := by
        refine card_le_card_of_injOn (fun x j ↦ x j) (fun x hx ↦ ?_) ?_
        · rw [mem_coe, mem_filter, mem_piFinset] at hx
          exact mem_coe.mpr (mem_piFinset.mpr fun j ↦ hx.1 j)
        intro x hx y hy h
        rw [mem_coe, mem_filter] at hx hy
        have hoff : ∀ j, j ≠ i → x j = y j := fun j hj ↦ congrFun h ⟨j, hj⟩
        have hsum : ∑ j, a j * (x j - y j) = 0 := by
          have := hx.2.trans hy.2.symm
          simp only [dotProduct] at this
          simp only [mul_sub, sum_sub_distrib, this, sub_self]
        rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hoff j hj]) (by simp)] at hsum
        funext j
        by_cases hj : j = i
        · subst hj
          exact sub_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left hi)
        · exact hoff j hj
    _ = #S ^ n := by simp

omit [DecidableEq R] in
/-- Let `T` be a set of more than `#S ^ n` points of the grid `Sⁿ⁺¹`.

If the affine form `σ₀ + σ₁ x₁ + ⋯ + σₙ₊₁ xₙ₊₁` vanishes on `T`, then `σ = 0`. -/
theorem eq_zero_of_forall_mem_add_dotProduct_eq_zero {n : ℕ} (S : Finset R)
    {T : Finset (Fin (n + 1) → R)} (hTS : T ⊆ piFinset fun _ ↦ S) (hT : #S ^ n < #T)
    (σ : Fin (n + 2) → R) (h : ∀ x ∈ T, σ 0 + Fin.tail σ ⬝ᵥ x = 0) : σ = 0 := by
  classical
  by_contra hσ
  by_cases ht : Fin.tail σ = 0
  · have h0 : σ 0 ≠ 0 := fun h0 ↦ hσ (funext fun j ↦ Fin.cases h0 (fun i ↦ congrFun ht i) j)
    obtain ⟨x, hx⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    have := h x hx
    rw [ht, zero_dotProduct, add_zero] at this
    exact h0 this
  · have hsub : T ⊆ {x ∈ piFinset fun _ : Fin (n + 1) ↦ S | Fin.tail σ ⬝ᵥ x = -σ 0} :=
      fun x hx ↦ mem_filter.mpr ⟨hTS hx, by linear_combination h x hx⟩
    have := (card_le_card hsub).trans (card_filter_piFinset_dotProduct_eq_le S ht _)
    omega

end Fintype
