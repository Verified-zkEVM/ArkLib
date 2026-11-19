/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.LinearAlgebra.PiFinsetHyperplane
import Mathlib.Data.Fin.VecNotation

/-! # Acceptance cases for grid points on a hyperplane -/

open Finset

-- Over the integers, the line `x₁ + x₂ = 3` meets the grid `{0, 1, 2, 3}²` in at most `4` points.
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ ({0, 1, 2, 3} : Finset ℤ) |
    ![1, 1] ⬝ᵥ x = 3} ≤ 4 :=
  (Fintype.card_filter_piFinset_dotProduct_eq_le _ (by decide) 3).trans (by decide)

-- An affine form over `ℚ` vanishing on two points of the grid `{0, 1}¹` is zero.
example (σ : Fin 2 → ℚ) (h : ∀ x ∈ ({![0], ![1]} : Finset (Fin 1 → ℚ)),
    σ 0 + Fin.tail σ ⬝ᵥ x = 0) : σ = 0 :=
  Fintype.eq_zero_of_forall_mem_add_dotProduct_eq_zero ({0, 1} : Finset ℚ)
    (fun x hx ↦ by
      rw [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp) (by decide) σ h

/-- info: 'Fintype.card_filter_piFinset_dotProduct_eq_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.card_filter_piFinset_dotProduct_eq_le

/-- info: 'Fintype.eq_zero_of_forall_mem_add_dotProduct_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.eq_zero_of_forall_mem_add_dotProduct_eq_zero
