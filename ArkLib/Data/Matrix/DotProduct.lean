/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

/-!
# Inner products against a product of two vectors

The pairing of a vector `x` indexed by `ι₁ × ι₂` with the product vector `(i, j) ↦ v₁ i * v₂ j`
splits as an inner product over `ι₁` for each column `j`, followed by a weighted sum over `ι₂`.
-/

@[expose] public section

open Finset

namespace Matrix

variable {α : Type*} [CommSemiring α] {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The pairing of `x : ι₁ × ι₂ → α` with the product vector `(i, j) ↦ v₁ i * v₂ j` is the sum over
`j` of the inner products `v₁ ⬝ᵥ x(·, j)` weighted by `v₂ j`. -/
theorem sum_prod_mul_mul_eq_sum_dotProduct (v₁ : ι₁ → α) (v₂ : ι₂ → α) (x : ι₁ × ι₂ → α) :
    ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * x p = ∑ j, (v₁ ⬝ᵥ fun i => x (i, j)) * v₂ j := by
  rw [Fintype.sum_prod_type_right]
  refine sum_congr rfl fun j _ => ?_
  rw [dotProduct, sum_mul]
  exact sum_congr rfl fun i _ => by ring

end Matrix
