/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Thomas Coratger
-/

import ArkLib.ToMathlib.Finset.AffineZeros
import ArkLib.ToMathlib.Finset.LineAgreement
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for line agreement and zeros of affine functions
-/

open scoped Finset

/-- One concrete pair of lines has an exceptional set of size at most one. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧
    ∀ z ∉ exceptional, ∀ i ∈ ({0} : Finset (Fin 1)),
      (0 : ℚ) + z * 1 = 1 + z * 0 ↔ (0 : ℚ) = 1 ∧ (1 : ℚ) = 0 := by
  simpa using Finset.exists_card_le_forall_add_mul_eq_add_mul_iff
    ({0} : Finset (Fin 1)) (fun _ ↦ (0 : ℚ)) (fun _ ↦ (1 : ℚ))
    (fun _ ↦ (1 : ℚ)) (fun _ ↦ (0 : ℚ))

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Only the coefficient of `y` is nonzero: `y = 0` leaves five zeros in `F₅ × F₅`.
example : #{x : ZMod 5 × ZMod 5 | 0 + x.1 * 0 + x.2 * 1 = 0} ≤ 5 :=
  (Finset.card_filter_add_mul_add_mul_eq_zero_le (Or.inr (Or.inr one_ne_zero))).trans_eq
    (ZMod.card 5)

-- Only the constant is nonzero: the function `1` has no zeros, within the bound.
example : #{x : ZMod 5 × ZMod 5 | 1 + x.1 * 0 + x.2 * 0 = 0} = 0 := by simp
