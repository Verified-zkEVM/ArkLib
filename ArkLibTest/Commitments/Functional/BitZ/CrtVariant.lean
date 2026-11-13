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
`ZMod 22`, which is not a field, applies the version with `orderOf`.

Dropping the range check `a < ℓ₁`, the second grand product, the coprimality of `ℓ₁` and the order,
the bound `ℓ₁² < ord x` or the bound `μ < ℓ₁ · ord x` leaves every other hypothesis true and the
remaining grand products valid, yet `⟨γ, b⟩ ≠ μ`.
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

/-- `9` has order `8` in `ZMod 17`. -/
private theorem orderOf_nine_zmod17 : orderOf (9 : ZMod 17) = 8 := by
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

/-- The honest side: for `μ = ⟨γ, b⟩ = 24` the iff supplies an in-range quotient `a < 3` for the
second grand product. -/
example : ∃ a < 3, ∏ i : Fin 3, (((2 : ZMod 11) ^ (γ₁ i % 3) - 1) * (ones 3 i : ZMod 11) + 1) =
    2 ^ (24 % 3 + a * 3) := by
  refine ((prod_bitFactor_eq_pow_and_exists_iff_of_coprime_orderOf (x := (2 : ZMod 11)) γ₁ (ones 3)
    ?_ (fun _ => le_rfl) ?_ ?_ ?_ ?_).2 ?_).2 <;>
    (try simp only [orderOf_two_zmod11, Fintype.card_fin]) <;> decide

/-- The second grand product is needed: with `μ = 4` the first product also holds, because
`4 ≡ 24 (mod 10)`, but `⟨γ, b⟩ = 24 ≠ 4`. -/
example : ∏ i : Fin 3, (((2 : ZMod 11) ^ γ₁ i - 1) * (ones 3 i : ZMod 11) + 1) = 2 ^ 4 ∧
    ∑ i : Fin 3, γ₁ i * ones 3 i ≠ 4 := by
  decide +kernel

/-- For `μ = 4` the second grand product fails for every in-range `a < 3`, so it rejects. -/
example : ∀ a < 3,
    ∏ i : Fin 3, (((2 : ZMod 11) ^ (γ₁ i % 3) - 1) * (ones 3 i : ZMod 11) + 1) ≠
      2 ^ (4 % 3 + a * 3) := by
  decide +kernel

/-- The range check `a < ℓ₁` is needed: with `μ = 4` and `a = 4`, both grand products hold, since
`⟨γ mod 3, b⟩ = 3 ≡ 13 = (4 mod 3) + 4 · 3 (mod 10)`, and every other hypothesis holds, but
`⟨γ, b⟩ = 24 ≠ 4`. Since `ℓ₁` is invertible modulo the order, some `a` always satisfies the second
product. -/
example :
    (∀ i, γ₁ i < orderOf (2 : ZMod 11)) ∧ 4 < Fintype.card (Fin 3) * orderOf (2 : ZMod 11) ∧
    (Fintype.card (Fin 3)).Coprime (orderOf (2 : ZMod 11)) ∧
    Fintype.card (Fin 3) ^ 2 < orderOf (2 : ZMod 11) ∧ ¬ 4 < Fintype.card (Fin 3) ∧
    ∏ i : Fin 3, (((2 : ZMod 11) ^ γ₁ i - 1) * (ones 3 i : ZMod 11) + 1) = 2 ^ 4 ∧
    ∏ i : Fin 3, (((2 : ZMod 11) ^ (γ₁ i % Fintype.card (Fin 3)) - 1) * (ones 3 i : ZMod 11) + 1) =
      2 ^ (4 % Fintype.card (Fin 3) + 4 * Fintype.card (Fin 3)) ∧
    ∑ i : Fin 3, γ₁ i * ones 3 i ≠ 4 := by
  rw [orderOf_two_zmod11]
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

private def γ₇ : Fin 3 → ℕ := ![7, 7, 7]

/-- The bound `ℓ₁² < ord x` is needed, already at `ord x = ℓ₁² - 1` (for `ℓ₁ ≥ 2` coprime to the
order, `ℓ₁² = ord x` is impossible): in `ZMod 17` (where `9` has order `8`) take `ℓ₁ = 3`,
`γ = (7, 7, 7)`, `b = 0`, `μ = 8 < 24` and `a = 2`. Both grand products equal `1`, since
`9 ^ 8 = 1`, and every other hypothesis holds, but `⟨γ, b⟩ = 0 ≠ 8`: the second product
`9 ^ (8 mod 3 + 2 · 3)` has an exponent equal to the order, so it wraps around. -/
example :
    (∀ i, γ₇ i < orderOf (9 : ZMod 17)) ∧ 8 < Fintype.card (Fin 3) * orderOf (9 : ZMod 17) ∧
    2 < Fintype.card (Fin 3) ∧ (Fintype.card (Fin 3)).Coprime (orderOf (9 : ZMod 17)) ∧
    Fintype.card (Fin 3) ^ 2 = orderOf (9 : ZMod 17) + 1 ∧
    ∏ i : Fin 3, (((9 : ZMod 17) ^ γ₇ i - 1) * ((0 : ℕ) : ZMod 17) + 1) = 9 ^ 8 ∧
    ∏ i : Fin 3, (((9 : ZMod 17) ^ (γ₇ i % Fintype.card (Fin 3)) - 1) * ((0 : ℕ) : ZMod 17) + 1) =
      9 ^ (8 % Fintype.card (Fin 3) + 2 * Fintype.card (Fin 3)) ∧
    ∑ i : Fin 3, γ₇ i * 0 ≠ 8 := by
  rw [orderOf_nine_zmod17]
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

/-- The version with `orderOf` needs no field: `3 ∈ ZMod 22` has order `5`; with `ℓ₁ = 2`,
`γ = (4, 3)`, `b = (1, 1)`, `μ = 7` and `a = 0` the two products give `⟨γ, b⟩ = 7`. Here
`ℓ₁ · max γ = 8 > 5`, so the plain overflow bound does not apply. -/
example : ∑ i : Fin 2, (![4, 3] : Fin 2 → ℕ) i * ones 2 i = 7 := by
  have hord : orderOf (3 : ZMod 22) = 5 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  refine sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime_orderOf (x := (3 : ZMod 22)) (a := 0)
    _ _ ?_ (fun _ => le_rfl) ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [hord, Fintype.card_fin]) <;> decide

/-- `|F| - 1` is coprime to every power of two in characteristic `2`, here for `F = 𝔽₈`. -/
example [Fintype (GaloisField 2 3)] : (2 ^ 5).Coprime (Fintype.card (GaloisField 2 3) - 1) :=
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

/--
info: 'BitZ.exists_prod_bitFactor_mod_eq_pow' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.exists_prod_bitFactor_mod_eq_pow

/--
info: 'BitZ.prod_bitFactor_eq_pow_and_exists_iff_of_coprime_orderOf' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.prod_bitFactor_eq_pow_and_exists_iff_of_coprime_orderOf
