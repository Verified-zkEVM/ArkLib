/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.CrtVariant
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# BitZ CRT variant: instances and axiom boundaries

Instances of the CRT variant of the exponent lift. Over `ZMod 11`, where `2` generates `(ZMod 11)ˣ`
(order `10`), take `ℓ₁ = 3`, coprime to `10`, with `ℓ₁² = 9 < 10`. The weights `γ = (9, 8, 7)` are
below `10` but `ℓ₁ · max γ = 27 > 10`, so the overflow bound of `prod_bitFactor_eq_pow_iff` does not
apply, and the second grand product modulo `ℓ₁` is what rules out wrap-around. A second instance in
`ZMod 15`, which is not a field, applies the version with `orderOf`.

Each hypothesis is also necessary: dropping the second grand product, the coprimality of `ℓ₁` and
the order, the bound `ℓ₁² < ord x` or the bound `μ < ℓ₁ · ord x` leaves every other hypothesis true
and both grand products valid, yet `⟨γ, b⟩ ≠ μ`.
-/

open BitZ Finset

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The unit `2 ∈ (ZMod 11)ˣ`. -/
private def g11 : (ZMod 11)ˣ := ⟨2, 6, by decide, by decide⟩

/-- `2` generates `(ZMod 11)ˣ`. -/
private theorem g11_generates : ∀ x : (ZMod 11)ˣ, x ∈ Subgroup.zpowers g11 := by
  intro x
  obtain ⟨n, hn⟩ := (by decide +kernel : ∀ x : (ZMod 11)ˣ, ∃ n : Fin 10, g11 ^ (n : ℕ) = x) x
  exact ⟨n, by simpa using hn⟩

/-- `2` has order `10` in `ZMod 11`. -/
private theorem orderOf_two_zmod11 : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

/-- `3` has order `6` in `ZMod 7`. -/
private theorem orderOf_three_zmod7 : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

/-- The vector of `n` bits all equal to `1`. -/
private def ones (n : ℕ) : Fin n → ℕ := fun _ => 1

private def γ₁ : Fin 3 → ℕ := ![9, 8, 7]

/-- `γ = (9, 8, 7)`, `b = (1, 1, 1)`, `μ = 24`, `a = 1`: `⟨γ, b⟩ = 24`, and modulo `ℓ₁ = 3`
`⟨γ mod 3, b⟩ = 0 + 2 + 1 = 3 = (24 mod 3) + 1 · 3`. -/
example : ∑ i : Fin 3, γ₁ i * ones 3 i = 24 := by
  refine sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime (g := g11) (a := 1)
    g11_generates γ₁ _ ?_ (fun _ => le_rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [γ₁, ZMod.card]
  · simp [ZMod.card]
  · simp
  · simp only [Fintype.card_fin, ZMod.card]
    decide
  · simp [ZMod.card]
  · decide +kernel
  · decide +kernel

/-- The second grand product is needed: with `μ = 4` the first product also holds, because
`4 ≡ 24 (mod 10)`, but `⟨γ, b⟩ = 24 ≠ 4`. -/
example : ∏ i : Fin 3, (((2 : ZMod 11) ^ γ₁ i - 1) * (ones 3 i : ZMod 11) + 1) = 2 ^ 4 ∧
    ∑ i : Fin 3, γ₁ i * ones 3 i ≠ 4 := by
  decide +kernel

private def γ₂ : Fin 2 → ℕ := ![9, 9]

/-- Coprimality of `ℓ₁` and the order is needed: in `ZMod 11` take `ℓ₁ = 2`, which divides the
order `10`, `γ = (9, 9)`, `b = (1, 1)`, `μ = 8` and `a = 1`. Both grand products hold, since
`18 ≡ 8 (mod 10)` and `⟨γ mod 2, b⟩ = 2 = (8 mod 2) + 1 · 2`, and every other hypothesis holds, but
`⟨γ, b⟩ = 18 ≠ 8`: the congruences modulo `10` and `2` only determine the sum modulo `10`. -/
example :
    (∀ i, γ₂ i < orderOf (2 : ZMod 11)) ∧ 8 < Fintype.card (Fin 2) * orderOf (2 : ZMod 11) ∧
    1 < Fintype.card (Fin 2) ∧ Fintype.card (Fin 2) ^ 2 < orderOf (2 : ZMod 11) ∧
    ¬ (Fintype.card (Fin 2)).Coprime (orderOf (2 : ZMod 11)) ∧
    ∏ i : Fin 2, (((2 : ZMod 11) ^ γ₂ i - 1) * (ones 2 i : ZMod 11) + 1) = 2 ^ 8 ∧
    ∏ i : Fin 2, (((2 : ZMod 11) ^ (γ₂ i % Fintype.card (Fin 2)) - 1) * (ones 2 i : ZMod 11) + 1) =
      2 ^ (8 % Fintype.card (Fin 2) + 1 * Fintype.card (Fin 2)) ∧
    ∑ i : Fin 2, γ₂ i * ones 2 i ≠ 8 := by
  rw [orderOf_two_zmod11]
  decide +kernel

private def γ₅ : Fin 5 → ℕ := ![5, 4, 3, 2, 1]

/-- The bound `ℓ₁² < ord x` is needed: in `ZMod 7` (where `3` has order `6`) take `ℓ₁ = 5`, coprime
to `6`, `γ = (5, 4, 3, 2, 1)`, `b = 0`, `μ = 6 < 30` and `a = 1`. Both grand products equal `1`,
since `3 ^ 6 = 1`, and every other hypothesis holds, but `⟨γ, b⟩ = 0 ≠ 6`: the second product
`3 ^ (6 mod 5 + 1 · 5)` has an exponent above the order, so it wraps around. -/
example :
    (∀ i, γ₅ i < orderOf (3 : ZMod 7)) ∧ 6 < Fintype.card (Fin 5) * orderOf (3 : ZMod 7) ∧
    1 < Fintype.card (Fin 5) ∧ (Fintype.card (Fin 5)).Coprime (orderOf (3 : ZMod 7)) ∧
    ¬ Fintype.card (Fin 5) ^ 2 < orderOf (3 : ZMod 7) ∧
    ∏ i : Fin 5, (((3 : ZMod 7) ^ γ₅ i - 1) * ((0 : ℕ) : ZMod 7) + 1) = 3 ^ 6 ∧
    ∏ i : Fin 5, (((3 : ZMod 7) ^ (γ₅ i % Fintype.card (Fin 5)) - 1) * ((0 : ℕ) : ZMod 7) + 1) =
      3 ^ (6 % Fintype.card (Fin 5) + 1 * Fintype.card (Fin 5)) ∧
    ∑ i : Fin 5, γ₅ i * 0 ≠ 6 := by
  rw [orderOf_three_zmod7]
  decide +kernel

/-- The bound `μ < ℓ₁ · ord x` is needed: with the data of the first instance, `μ = 54 = 24 + 30`
makes both grand products hold, since `54 ≡ 24 (mod 10)`, `54 ≡ 24 ≡ 0 (mod 3)` and
`⟨γ mod 3, b⟩ = 3 = (54 mod 3) + 1 · 3`, but `⟨γ, b⟩ = 24 ≠ 54`. -/
example :
    (∀ i, γ₁ i < orderOf (2 : ZMod 11)) ∧ 1 < Fintype.card (Fin 3) ∧
    (Fintype.card (Fin 3)).Coprime (orderOf (2 : ZMod 11)) ∧
    Fintype.card (Fin 3) ^ 2 < orderOf (2 : ZMod 11) ∧
    ¬ 54 < Fintype.card (Fin 3) * orderOf (2 : ZMod 11) ∧
    ∏ i : Fin 3, (((2 : ZMod 11) ^ γ₁ i - 1) * (ones 3 i : ZMod 11) + 1) = 2 ^ 54 ∧
    ∏ i : Fin 3, (((2 : ZMod 11) ^ (γ₁ i % Fintype.card (Fin 3)) - 1) * (ones 3 i : ZMod 11) + 1) =
      2 ^ (54 % Fintype.card (Fin 3) + 1 * Fintype.card (Fin 3)) ∧
    ∑ i : Fin 3, γ₁ i * ones 3 i ≠ 54 := by
  rw [orderOf_two_zmod11]
  decide +kernel

/-- The version with `orderOf` needs no field: `2 ∈ ZMod 15` has order `4`; with `ℓ₁ = 1`,
`γ = (3)`, `b = (1)`, `μ = 3` and `a = 0` the two products give `⟨γ, b⟩ = 3`. -/
example : ∑ i : Fin 1, (fun _ => 3 : Fin 1 → ℕ) i * ones 1 i = 3 := by
  have hord : orderOf (2 : ZMod 15) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  refine sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime_orderOf (x := (2 : ZMod 15)) (a := 0)
    _ _ ?_ (fun _ => le_rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rw [hord]
    decide
  · simp [hord]
  · simp
  · simp [hord]
  · simp [hord]
  · decide
  · decide

/-- `GaloisField` is a splitting field, so its finiteness is not executable data; the instance is
only used to state the cardinality in the example below. -/
noncomputable instance : Fintype (GaloisField 2 3) := Fintype.ofFinite _

/-- `|F| - 1` is coprime to every power of two in characteristic `2`, here for `F = 𝔽₈`. -/
example : (2 ^ 5).Coprime (Fintype.card (GaloisField 2 3) - 1) :=
  coprime_two_pow_card_sub_one 5

/-! ### Axiom boundaries -/

/--
info: 'BitZ.sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime_orderOf' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime_orderOf

/--
info: 'BitZ.sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime

/--
info: 'BitZ.coprime_two_pow_card_sub_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.coprime_two_pow_card_sub_one
