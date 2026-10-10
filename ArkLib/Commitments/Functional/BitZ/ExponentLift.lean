/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# BitZ: lifting an integer inner product into the exponent of a generator

BitZ ([BGKLSW26], §2.1 Steps 4–5 and Phase 3 of Construction 4.4) turns an integer claim
`⟨γ, b⟩ = μ` on a vector of bits `b` into a claim in the multiplicative group of a binary field
`𝔽_{2^ν}`, where `g` is a generator of the group of units:

  `∏ᵢ ((g ^ γᵢ - 1) · bᵢ + 1) = g ^ μ`.

The left-hand side is a product of *bit-dependent* factors, so it is a polynomial expression in the
committed bits, which is what the grand-product argument proves. This file contains the two
elementary facts that make the translation sound:

* `BitZ.prod_bitFactor_eq_pow`: for bits `b`, the product equals `g ^ ⟨γ, b⟩`;
* `BitZ.inner_eq_of_pow_eq_pow`: if every integer in sight is below the order of `g`, equality in
  the exponent of `g` implies equality over `ℕ` (no wrap-around, the "overflow" condition
  `ℓ₁ · max P < |𝔽_{2^ν}| - 1` of [BGKLSW26, Theorem 4.7]).

## References

* [BGKLSW26] R. Bloemen, A. Garreta, M. Kostrzewa, S. Londhe, L. Soukhanov, J. Wu.
  *BitZ: proofs and commitments in arbitrary rings through binary fields*. ePrint 2026/2141.
-/

@[expose] public section

open Finset

namespace BitZ

section Product

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]

/-- A single factor of the BitZ grand product: for a bit `b ∈ {0, 1}` it evaluates to `x ^ (γ * b)`.
-/
theorem bitFactor_eq_pow (x : A) (γ b : ℕ) (hb : b ≤ 1) :
    (x ^ γ - 1) * (b : A) + 1 = x ^ (γ * b) := by
  interval_cases b <;> simp

/-- **The BitZ grand-product identity.** For a vector of bits `b` (as natural numbers `≤ 1`),
`∏ᵢ ((x ^ γᵢ - 1) · bᵢ + 1) = x ^ ∑ᵢ γᵢ · bᵢ`, in any commutative ring. -/
theorem prod_bitFactor_eq_pow (x : A) (γ b : ι → ℕ) (hb : ∀ i, b i ≤ 1) :
    ∏ i, ((x ^ γ i - 1) * (b i : A) + 1) = x ^ ∑ i, γ i * b i := by
  rw [← prod_pow_eq_pow_sum]
  exact prod_congr rfl fun i _ => bitFactor_eq_pow x (γ i) (b i) (hb i)

end Product

section Overflow

variable {G : Type*} [Monoid G]

/-- Equality of powers of `g` between two exponents below `orderOf g` is equality of exponents. -/
theorem eq_of_pow_eq_pow_of_lt_orderOf {g : G} {a b : ℕ} (ha : a < orderOf g) (hb : b < orderOf g)
    (h : g ^ a = g ^ b) : a = b :=
  pow_injOn_Iio_orderOf ha hb h

variable {ι : Type*} [Fintype ι]

/-- **No overflow.** Let `γᵢ ≤ qMax` and let `b` be a vector of bits. If `μ ≤ |ι| · qMax` and
`|ι| · qMax < orderOf g`, then `g ^ μ = g ^ ∑ᵢ γᵢ bᵢ` already forces `μ = ∑ᵢ γᵢ bᵢ` over `ℕ`.

The paper's hypothesis `max P < (|𝔽_{2^ν}| - 1) / ℓ₁` gives `ℓ₁ · q < orderOf g`, which is
stronger than the `|ι| · qMax < orderOf g` used here with `qMax = q - 1`. -/
theorem inner_eq_of_pow_eq_pow {g : G} {qMax μ : ℕ} (γ b : ι → ℕ) (hγ : ∀ i, γ i ≤ qMax)
    (hb : ∀ i, b i ≤ 1) (hμ : μ ≤ Fintype.card ι * qMax) (hord : Fintype.card ι * qMax < orderOf g)
    (h : g ^ μ = g ^ ∑ i, γ i * b i) : μ = ∑ i, γ i * b i := by
  have hsum : ∑ i, γ i * b i ≤ Fintype.card ι * qMax := by
    calc ∑ i, γ i * b i ≤ ∑ _i : ι, qMax := sum_le_sum fun i _ =>
          calc γ i * b i ≤ γ i * 1 := Nat.mul_le_mul_left _ (hb i)
            _ ≤ qMax := by simpa using hγ i
      _ = Fintype.card ι * qMax := by simp
  exact eq_of_pow_eq_pow_of_lt_orderOf (lt_of_le_of_lt hμ hord) (lt_of_le_of_lt hsum hord) h

end Overflow

section Field

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι]

/-- **Soundness of the exponent lift in a finite field.** For a generator `g` of `Fˣ`, with
`γᵢ ≤ qMax`, `b` a vector of bits, `μ ≤ |ι| · qMax` and `|ι| · qMax < |F| - 1`, the BitZ
grand-product claim `∏ᵢ ((g ^ γᵢ - 1) bᵢ + 1) = g ^ μ` holds if and only if `⟨γ, b⟩ = μ` over `ℕ`.
-/
theorem prod_bitFactor_eq_pow_iff {g : Fˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) {qMax μ : ℕ}
    (γ b : ι → ℕ) (hγ : ∀ i, γ i ≤ qMax) (hb : ∀ i, b i ≤ 1) (hμ : μ ≤ Fintype.card ι * qMax)
    (hord : Fintype.card ι * qMax < Fintype.card F - 1) :
    ∏ i, (((g : F) ^ γ i - 1) * (b i : F) + 1) = (g : F) ^ μ ↔ ∑ i, γ i * b i = μ := by
  classical
  have hord' : orderOf g = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  rw [prod_bitFactor_eq_pow _ γ b hb]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h' : g ^ μ = g ^ ∑ i, γ i * b i := Units.ext (by simpa using h.symm)
  exact (inner_eq_of_pow_eq_pow γ b hγ hb hμ (hord' ▸ hord) h').symm

end Field

end BitZ
