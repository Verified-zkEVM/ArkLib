/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Commitments.Functional.BitZ.ExponentLift
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.FieldTheory.Finite.Basic

/-!
# BitZ: relaxing the overflow bound by a CRT argument

[BGKLSW26, Remark A.1, Method 2] relaxes the condition `ℓ₁ · max P < |𝔽_{2^ν}| - 1` of
Theorem 4.7 to `max P < |𝔽_{2^ν}| - 1`, which removes the dependence of the prime set `P` on the
witness size, at the price of an additional batch of grand products. The grand product
`∏ᵢ ((g ^ γᵢ - 1) · bᵢ + 1) = g ^ μ` only proves `⟨γ, b⟩ ≡ μ (mod ord g)`, where `ord g = |𝔽| - 1`,
and that gives equality over `ℕ` if both sides are below `ord g`, which is what
`ℓ₁ · max P < |𝔽| - 1` guarantees. If the entries of `γ` are only below `|𝔽| - 1`, the two sides can
differ by a multiple of `|𝔽| - 1`, but they are both below `ℓ₁ · (|𝔽| - 1)`. So it is enough to
prove the congruence also modulo `ℓ₁`, which is coprime to `|𝔽| - 1` when `ℓ₁` is a power of two and
`𝔽` has characteristic `2`. By the Chinese remainder theorem the two sides then agree modulo
`ℓ₁ · (|𝔽| - 1)`, hence are equal.

The congruence modulo `ℓ₁` is proved by a second grand product: the prover sends
`a ∈ [0 .. ℓ₁ - 1]`, which the verifier range-checks, and proves the integer equality
`⟨γ mod ℓ₁, b⟩ = (μ mod ℓ₁) + a · ℓ₁`, where both sides are below `ℓ₁² < |𝔽| - 1`, so no overflow
occurs. The range check is what makes the second product binding: `ℓ₁` is invertible modulo `ord g`,
so without it some `a` always satisfies the second product. The statements are per column of the
witness (the vector `f_{*j}` of the paper).

## Main statements

* `BitZ.sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime_orderOf`: the implication in any commutative
  ring, with `ord x` in place of `|𝔽| - 1`.
* `BitZ.sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime`: the same in a finite field with a
  generator `g` of the units.
* `BitZ.coprime_two_pow_card_sub_one`: `|𝔽| - 1` is coprime to every power of two when `𝔽` has
  characteristic `2`.

The general statement only needs `ℓ₁` coprime to `ord x`, not a power of two, and it needs `μ` only
below `ℓ₁ · ord x`. In the protocol `μ` is the prover's message, and the bound follows from the
verifier's Round 2 range check `μ ≤ ℓ₁ · (q - 1)` together with `q - 1 ≤ |𝔽| - 2`, which holds
under `max P < |𝔽| - 1` and the relaxed conditions for skipping Round 1. This file contains only
theorems, so there are no definitions to make executable.

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset

namespace BitZ

section General

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]

/-- **The integer inner product from two grand products.** Let `x` be an element of a commutative
ring with `N := orderOf x`, let `γᵢ < N` and let `b` be a vector of bits of length `ℓ₁ = |ι|`, with
`ℓ₁` coprime to `N`, `ℓ₁² < N`, `μ < ℓ₁ · N` and `a < ℓ₁`. If

* `∏ᵢ ((x ^ γᵢ - 1) · bᵢ + 1) = x ^ μ` (the equality modulo `N`), and
* `∏ᵢ ((x ^ (γᵢ mod ℓ₁) - 1) · bᵢ + 1) = x ^ ((μ mod ℓ₁) + a · ℓ₁)` (the equality modulo `ℓ₁`),

then `∑ᵢ γᵢ · bᵢ = μ` over `ℕ`. -/
theorem sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime_orderOf {x : A} (γ b : ι → ℕ)
    (hγ : ∀ i, γ i < orderOf x) (hb : ∀ i, b i ≤ 1) {μ a : ℕ}
    (hμ : μ < Fintype.card ι * orderOf x) (ha : a < Fintype.card ι)
    (hcop : (Fintype.card ι).Coprime (orderOf x)) (hℓ : Fintype.card ι ^ 2 < orderOf x)
    (hgp : ∏ i, ((x ^ γ i - 1) * (b i : A) + 1) = x ^ μ)
    (hgp' : ∏ i, ((x ^ (γ i % Fintype.card ι) - 1) * (b i : A) + 1) =
      x ^ (μ % Fintype.card ι + a * Fintype.card ι)) :
    ∑ i, γ i * b i = μ := by
  set ℓ₁ := Fintype.card ι
  have hℓpos : 0 < ℓ₁ := Nat.zero_lt_of_lt ha
  have hNpos : 0 < orderOf x := Nat.zero_lt_of_lt hℓ
  -- modulo `orderOf x`
  have h1 : ∑ i, γ i * b i ≡ μ [MOD orderOf x] := by
    rw [prod_bitFactor_eq_pow x γ b hb] at hgp
    exact (orderOf_pos_iff.1 hNpos).pow_eq_pow_iff_modEq.1 hgp
  -- modulo `ℓ₁`: the second grand product has no overflow
  have h2 := (prod_bitFactor_eq_pow_iff_of_lt_orderOf (qMax := ℓ₁) (fun i => γ i % ℓ₁) b
    (fun i => (Nat.mod_lt _ hℓpos).le) hb
    (by nlinarith [Nat.mod_lt μ hℓpos]) (by simpa [sq] using hℓ)).1 hgp'
  have h3 : ∑ i, γ i * b i ≡ μ [MOD ℓ₁] := by
    refine (Nat.ModEq.sum fun i _ => ((Nat.mod_modEq (γ i) ℓ₁).symm.mul_right (b i))).trans ?_
    rw [h2]
    simp [Nat.ModEq, Nat.add_mul_mod_self_right]
  refine ((Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h3, h1⟩).eq_of_lt_of_lt ?_ hμ
  calc ∑ i, γ i * b i ≤ ∑ _i : ι, (orderOf x - 1) :=
        sum_le_sum fun i _ =>
          (Nat.mul_le_mul_left _ (hb i)).trans (by have := hγ i; rw [mul_one]; omega)
    _ < ℓ₁ * orderOf x := by
        simp only [sum_const, card_univ, smul_eq_mul]
        exact Nat.mul_lt_mul_of_pos_left (by omega) hℓpos

end General

section Field

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι]

/-- **The integer inner product from two grand products in a finite field.** Let `g` generate `Fˣ`,
let `γᵢ < |F| - 1` and let `b` be a vector of bits of length `ℓ₁ = |ι|`, with `ℓ₁` coprime to
`|F| - 1`, `ℓ₁² < |F| - 1`, `μ < ℓ₁ · (|F| - 1)` and `a < ℓ₁`. If

* `∏ᵢ ((g ^ γᵢ - 1) · bᵢ + 1) = g ^ μ`, and
* `∏ᵢ ((g ^ (γᵢ mod ℓ₁) - 1) · bᵢ + 1) = g ^ ((μ mod ℓ₁) + a · ℓ₁)`,

then `∑ᵢ γᵢ · bᵢ = μ` over `ℕ`. -/
theorem sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime {g : Fˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (γ b : ι → ℕ) (hγ : ∀ i, γ i < Fintype.card F - 1)
    (hb : ∀ i, b i ≤ 1) {μ a : ℕ} (hμ : μ < Fintype.card ι * (Fintype.card F - 1))
    (ha : a < Fintype.card ι) (hcop : (Fintype.card ι).Coprime (Fintype.card F - 1))
    (hℓ : Fintype.card ι ^ 2 < Fintype.card F - 1)
    (hgp : ∏ i, (((g : F) ^ γ i - 1) * (b i : F) + 1) = (g : F) ^ μ)
    (hgp' : ∏ i, (((g : F) ^ (γ i % Fintype.card ι) - 1) * (b i : F) + 1) =
      (g : F) ^ (μ % Fintype.card ι + a * Fintype.card ι)) :
    ∑ i, γ i * b i = μ := by
  classical
  have hord : orderOf (g : F) = Fintype.card F - 1 := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  rw [← hord] at hγ hμ hcop hℓ
  exact sum_mul_eq_of_prod_bitFactor_eq_pow_of_coprime_orderOf γ b hγ hb hμ ha hcop hℓ hgp hgp'

/-- In a field of characteristic `2`, `|F| - 1` is odd, so it is coprime to every power of two. -/
theorem coprime_two_pow_card_sub_one [CharP F 2] (a : ℕ) :
    (2 ^ a).Coprime (Fintype.card F - 1) := by
  have heven := FiniteField.even_card_iff_char_two.1 (ringChar.eq F 2)
  have hpos := Fintype.card_pos (α := F)
  exact Nat.Coprime.pow_left a (Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega)))

end Field

end BitZ
