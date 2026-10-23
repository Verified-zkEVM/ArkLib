/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Commitments.Functional.BitZ.ExponentLift
public import ArkLib.Data.Matrix.DotProduct

/-!
# BitZ: soundness of Round 2 of Construction 4.4

Round 2 of [BGKLSW26, Construction 4.4] splits the claim `⟨v⁽¹⁾ ⊗ v⁽²⁾, π_q(f)⟩ = µ` over `𝔽_q`
into `ℓ₂` integer claims `⟨f_{*j}, γ⟩ = µⱼ`, where `γ = π_q⁻¹(v⁽¹⁾) ∈ [0 .. q - 1]^{ℓ₁}` and the
prover sends integers `µⱼ ∈ [0 .. (q - 1) · ℓ₁]`. The verifier checks `∑ⱼ π_q(µⱼ) · v⁽²⁾ⱼ = µ`, and
Phase 3 hands the integer claims to the grand-product IOR as `∏ᵢ ((g ^ γᵢ - 1) · fᵢⱼ + 1) = g ^ µⱼ`.

This file is the algebraic core of the second half of the proof of [BGKLSW26, Theorem 4.7]. It is
stated for an arbitrary commutative ring `K` in place of `𝔽_q`, so that it also covers Remark 4.5
(`R = ℤ`, no Round 1), with `K = ℤ`. The paper's hypothesis `ℓ₁ · max P < |𝔽_{2^ν}| - 1` with
`q ≤ max P` implies the weaker overflow bound `ℓ₁ · (q - 1) < |𝔽_{2^ν}| - 1` used here.

## Main statements

* `BitZ.sum_prod_mul_mul_eq_of_prod_bitFactor_eq_pow`: if the grand products hold, the range checks
  hold and `ℓ₁ · (q - 1) < |𝔽| - 1`, then the integer claims `⟨f_{*j}, γ⟩ = µⱼ` hold, and together
  with the verifier check `∑ⱼ µⱼ · v⁽²⁾ⱼ = c` they give `⟨v⁽¹⁾ ⊗ v⁽²⁾, f⟩ = c` in `K`.

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset

namespace BitZ

variable {F : Type*} [Field F] [Fintype F] {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
  {K : Type*} [CommRing K]

/-- **Round 2 of [BGKLSW26, Construction 4.4], as a pure implication.** Let `g` generate `Fˣ`, let
`γᵢ < q` and `µⱼ ≤ |ι₁| · (q - 1)`, let `f` be a matrix of bits, and assume
`|ι₁| · (q - 1) < |F| - 1`. Let `v₁ ∈ Kˡ¹` and `v₂ ∈ Kˡ²` with `v₁ = (γᵢ)ᵢ` in `K`, that is, `γ` is
the integer representative of `v₁`. If every column satisfies the BitZ grand product
`∏ᵢ ((g ^ γᵢ - 1) · fᵢⱼ + 1) = g ^ µⱼ` and the verifier's check `∑ⱼ µⱼ · v₂ⱼ = c` passes, then
`⟨v₁ ⊗ v₂, f⟩ = c` in `K`. -/
theorem sum_prod_mul_mul_eq_of_prod_bitFactor_eq_pow {g : Fˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {q : ℕ} (γ : ι₁ → ℕ) (hγ : ∀ i, γ i < q) (f : ι₁ × ι₂ → ℕ) (hf : ∀ p, f p ≤ 1)
    (μ : ι₂ → ℕ) (hμ : ∀ j, μ j ≤ Fintype.card ι₁ * (q - 1))
    (hord : Fintype.card ι₁ * (q - 1) < Fintype.card F - 1)
    (hgp : ∀ j, ∏ i, (((g : F) ^ γ i - 1) * (f (i, j) : F) + 1) = (g : F) ^ μ j)
    (v₁ : ι₁ → K) (v₂ : ι₂ → K) (hv₁ : ∀ i, (γ i : K) = v₁ i) (c : K)
    (hc : ∑ j, (μ j : K) * v₂ j = c) :
    ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : K) = c := by
  rw [Matrix.sum_prod_mul_mul_eq_sum_dotProduct v₁ v₂ fun p => (f p : K), ← hc]
  refine sum_congr rfl fun j _ => ?_
  have hj := (prod_bitFactor_eq_pow_iff hg γ (fun i => f (i, j))
    (fun i => Nat.le_sub_one_of_lt (hγ i)) (fun _ => hf _) (hμ j) hord).1 (hgp j)
  have : (v₁ ⬝ᵥ fun i => (f (i, j) : K)) = (μ j : K) := by
    rw [← hj]
    push_cast
    exact sum_congr rfl fun i _ => by rw [← hv₁ i]
  rw [this]

end BitZ
