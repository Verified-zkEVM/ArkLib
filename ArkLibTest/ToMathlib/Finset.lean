/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Thomas Coratger
-/

import ArkLib.ToMathlib.Finset.AffineZeros
import ArkLib.ToMathlib.Finset.LineAgreement
import ArkLib.ToMathlib.Finset.TripleCount
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for line agreement, zeros of affine functions and triple counts
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

-- The line `x = 0` attains the bound: `0 + x · 1 + y · 0` has exactly `q = 5` zeros in `F₅ × F₅`.
example : #{x : ZMod 5 × ZMod 5 | 0 + x.1 * 1 + x.2 * 0 = 0} = Fintype.card (ZMod 5) := by
  refine le_antisymm (Finset.card_filter_add_mul_add_mul_eq_zero_le (Or.inr (Or.inl one_ne_zero)))
    ?_
  have : ({x : ZMod 5 × ZMod 5 | 0 + x.1 * 1 + x.2 * 0 = 0} : Finset (ZMod 5 × ZMod 5)) =
      {0} ×ˢ Finset.univ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
    simp
  rw [this, Finset.card_product, Finset.card_singleton, Finset.card_univ, one_mul]

/-- info: 'Finset.card_filter_add_mul_add_mul_eq_zero_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Finset.card_filter_add_mul_add_mul_eq_zero_le

-- Over `𝔽₂`, each first coordinate allows the `2 = 2² · (1/2)` pairs with equal entries.
-- The triple count `2³ · (1/2) = 4` is then attained.
example : #{c : ZMod 2 × ZMod 2 × ZMod 2 | c.2.1 = c.2.2} = 4 ∧
    (#{c : ZMod 2 × ZMod 2 × ZMod 2 | c.2.1 = c.2.2} : ℝ) ≤ 2 ^ 3 * (1 / 2) := by
  refine ⟨by decide, ?_⟩
  have h := Finset.card_filter_triples_le_mul (fun c : ZMod 2 × ZMod 2 × ZMod 2 ↦ c.2.1 = c.2.2)
    (1 / 2) fun θ ↦ by
      have : #{x : ZMod 2 × ZMod 2 | x.1 = x.2} = 2 := by decide
      simp only [this, ZMod.card]
      norm_num
  simpa [ZMod.card] using h

-- Adding the first coordinate `0` as a set `B` adds `#B · 2² = 4` triples to the bound.
-- The six triples with first coordinate `0` or equal last entries stay below `4 + 4 = 8`.
example : #{c : ZMod 2 × ZMod 2 × ZMod 2 | c.1 = 0 ∨ c.2.1 = c.2.2} = 6 ∧
    (#{c : ZMod 2 × ZMod 2 × ZMod 2 | c.1 = 0 ∨ c.2.1 = c.2.2} : ℝ) ≤
      2 ^ 3 * (1 / 2) + 1 * 2 ^ 2 := by
  refine ⟨by decide, ?_⟩
  have h := Finset.card_filter_triples_le_of_imp_or (p := fun c : ZMod 2 × ZMod 2 × ZMod 2 ↦
      c.1 = 0 ∨ c.2.1 = c.2.2) (a := fun c ↦ c.2.1 = c.2.2) {0} (E := 1 / 2)
    (fun c hc ↦ hc.symm.imp_right Finset.mem_singleton.mpr) fun θ ↦ by
      have : #{x : ZMod 2 × ZMod 2 | x.1 = x.2} = 2 := by decide
      simp only [this, ZMod.card]
      norm_num
  simpa [ZMod.card] using h

/-- info: 'Finset.card_filter_triples_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Finset.card_filter_triples_le_mul

/-- info: 'Finset.card_filter_triples_le_of_imp_or' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Finset.card_filter_triples_le_of_imp_or
