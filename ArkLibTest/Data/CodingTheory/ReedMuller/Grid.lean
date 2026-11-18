/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.Grid
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for grid points on hyperplanes -/

open ReedMuller Finset MvPolynomial

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable instance : Fintype (GaloisField 3 2) := Fintype.ofFinite _

-- The hyperplane `x₁ = 0` holds exactly `3 = 3²⁻¹` points of the grid `F₃²`, so (7.1) is tight.
example : #{z : Fin 2 → ZMod 3 | ![1, 0] ⬝ᵥ gridPoint (ZMod 3) z = 0} = 3 := by
  decide

-- The bound (7.1) on the proper subfield grid `F₃² ⊆ F₉²`.
open Classical in
example (a : Fin 2 → GaloisField 3 2) (ha : a ≠ 0) (b : GaloisField 3 2) :
    #{z : Fin 2 → ZMod 3 | a ⬝ᵥ gridPoint (GaloisField 3 2) z = b} ≤ 3 := by
  simpa [ZMod.card] using card_grid_inter_hyperplane_le (K₀ := ZMod 3) a ha b

-- An affine form over `F₉` vanishing on four points of the grid `F₃²` is zero.
example (T : Finset (Fin 2 → ZMod 3)) (hT : 3 < #T) (σ : Fin 3 → GaloisField 3 2)
    (h : ∀ z ∈ T, σ 0 + Fin.tail σ ⬝ᵥ gridPoint (GaloisField 3 2) z = 0) : σ = 0 :=
  eq_zero_of_forall_mem_add_dotProduct_eq_zero T (by simpa [ZMod.card] using hT) σ h

-- Four points of the grid `F₃²` contain three that pin down every affine form over `F₉`.
example (T : Finset (Fin 2 → ZMod 3)) (hT : 3 < #T) :
    ∃ t ⊆ T, #t = 3 ∧ ∀ σ : Fin 3 → GaloisField 3 2,
      (∀ z ∈ t, σ 0 + Fin.tail σ ⬝ᵥ gridPoint (GaloisField 3 2) z = 0) → σ = 0 :=
  exists_subset_card_eq_forall_add_dotProduct_eq_zero T (by simpa [ZMod.card] using hT)

-- The polynomial `X₁` over `F₉` has at most `1 · 3` zeros on the grid `F₃²`.
open Classical in
example : #{z : Fin 2 → ZMod 3 | eval (gridPoint (GaloisField 3 2) z) (X 0) = 0} ≤ 3 := by
  simpa [ZMod.card] using
    card_grid_eval_eq_zero_le (K₀ := ZMod 3) (X_ne_zero (R := GaloisField 3 2) (0 : Fin 2))

-- The Schwartz–Zippel count is exact for `X₁` on `F₃²`: the zeros are the line `x₁ = 0`.
example : #{z : Fin 2 → ZMod 3 | eval (gridPoint (ZMod 3) z) (X 0) = 0} = 3 := by
  simp only [eval_X, gridPoint_apply, Algebra.algebraMap_self, RingHom.id_apply]
  decide

/-- info: 'ReedMuller.card_grid_inter_hyperplane_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_grid_inter_hyperplane_le

/-- info: 'ReedMuller.eq_zero_of_forall_mem_add_dotProduct_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.eq_zero_of_forall_mem_add_dotProduct_eq_zero

/-- info: 'ReedMuller.exists_subset_card_eq_forall_add_dotProduct_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_subset_card_eq_forall_add_dotProduct_eq_zero

/-- info: 'ReedMuller.card_grid_eval_eq_zero_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_grid_eval_eq_zero_le

/-- info: 'ReedMuller.card_filter_gridPoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_filter_gridPoint
