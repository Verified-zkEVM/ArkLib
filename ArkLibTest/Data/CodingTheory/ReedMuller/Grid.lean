/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.Grid
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for grid points on hyperplanes -/

open ReedMuller Finset

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- The hyperplane `x₁ = 0` holds exactly `3 = 3²⁻¹` points of the grid `F₃²`, so (7.1) is tight.
example : #{z : Fin 2 → ZMod 3 | ∑ i, ![1, 0] i * algebraMap (ZMod 3) (ZMod 3) (z i) = 0} = 3 := by
  decide

-- The bound (7.1) at the same hyperplane.
example : #{z : Fin 2 → ZMod 3 | ∑ i, ![1, 0] i * algebraMap (ZMod 3) (ZMod 3) (z i) = 0} ≤
    Fintype.card (ZMod 3) ^ (2 - 1) :=
  card_grid_inter_hyperplane_le ![1, 0] (by decide) 0

-- Four grid points of `F₃²` are more than `3`, so three of them pin down every affine form.
example (T : Finset (Fin 2 → ZMod 3)) (hT : 3 < #T) :
    ∃ t ⊆ T, #t = 3 ∧ ∀ σ : Fin 3 → ZMod 3,
      (∀ z ∈ t, σ 0 + ∑ i, σ i.succ * algebraMap (ZMod 3) (ZMod 3) (z i) = 0) → σ = 0 :=
  exists_subset_card_eq_forall_add_sum_eq_zero T (by simpa [ZMod.card] using hT)

/-- info: 'ReedMuller.card_grid_inter_hyperplane_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_grid_inter_hyperplane_le

/-- info: 'ReedMuller.exists_subset_card_eq_forall_add_sum_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_subset_card_eq_forall_add_sum_eq_zero

/-- info: 'ReedMuller.card_grid_eval_eq_zero_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.card_grid_eval_eq_zero_le
