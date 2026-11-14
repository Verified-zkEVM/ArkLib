/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Commitments.Functional.BitZ.BitifiedClaim

/-!
# BitZ: the honest messages of Rounds 1 and 2

An honest prover that holds a matrix of bits `f` sends, in Round 1, the integer polynomial
`μ' = ⟨a ⊗ b, f⟩` for lifts `a`, `b` of the two tensor factors of the weights
(`BitZ.honestMessage`, with its degree and norm bounds in `Round1`), and in Round 2, for a prime
`q` and a point `α`, the integers `μⱼ = ∑ᵢ γᵢ · fᵢⱼ`, where `γᵢ` is the integer representative of
the reduction of `aᵢ`. This file shows that the second message passes the check of Round 2 against
the first and satisfies the grand-product claim, and that, for a bitified witness, the first message
satisfies the Round 1 equation exactly when the original claim holds. These are the facts that the
completeness of Rounds 1 and 2 of [BGKLSW26, Construction 4.4] and of
[BGKLSW26, Construction 4.13] rests on; the completeness statements themselves need the protocol,
which is not formalized here.

## Main statements

* `BitZ.honestRound2Message` is the honest second message.
  `BitZ.round2Check_honestRound2Message` shows that it passes `BitZ.Round2Check` against the honest
  first message for every modulus `q > 0` and every point, and
  `BitZ.grandProductClaim_honestRound2Message` that it satisfies `BitZ.GrandProductClaim` for every
  unit `g`, with no overflow bound, because these are identities for bits.
* `BitZ.map_honestMessage_bitified` shows that the canonical image of the honest first message for
  a vector of bits is the original claim `⟨v, ψ(L g)⟩`, so the equation `π_canon(μ') = μ` checked
  by the verifier holds exactly when the original claim does.
  `BitZ.map_honestMessage_coeffBits` specializes it to the bits `BitZ.coeffBits` of a witness with
  bounded digits, which form the bitification [BGKLSW26, (46)] of the witness that the honest prover
  of [BGKLSW26, Construction 4.13] uses.

`honestRound2Message` is executable.

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset MvPolynomial Matrix

namespace BitZ

variable {k : ℕ} {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The honest second message: `μⱼ = ∑ᵢ γᵢ * f(i, j)`, where `γᵢ` is the integer representative of
the reduction of `aᵢ` at `(q, α)`. -/
def honestRound2Message (q : ℕ) (α : Fin k → ZMod q) (a : ι₁ → MvPolynomial (Fin k) ℤ)
    (f : ι₁ × ι₂ → ℕ) : ι₂ → ℕ :=
  fun j => ∑ i, (reduceAt q α (a i)).val * f (i, j)

/-- **The honest messages pass the check of Round 2.** For a matrix of bits `f`, the honest second
message passes `Round2Check` against the honest first message, for every modulus `q > 0` and every
point `α`. -/
theorem round2Check_honestRound2Message (a : ι₁ → MvPolynomial (Fin k) ℤ)
    (b : ι₂ → MvPolynomial (Fin k) ℤ) {f : ι₁ × ι₂ → ℕ} (hf : ∀ p, f p ≤ 1) (q : ℕ) [NeZero q]
    (α : Fin k → ZMod q) :
    Round2Check (Fintype.card ι₁) b (honestMessage a b f) q α (honestRound2Message q α a f) := by
  refine ⟨fun j => ?_, ?_⟩
  · calc ∑ i, (reduceAt q α (a i)).val * f (i, j) ≤ ∑ _i : ι₁, (q - 1) * 1 :=
          sum_le_sum fun i _ => Nat.mul_le_mul (Nat.le_sub_one_of_lt (ZMod.val_lt _)) (hf _)
      _ = Fintype.card ι₁ * (q - 1) := by simp [mul_comm]
  · rw [map_honestMessage, Fintype.sum_prod_type_right]
    refine sum_congr rfl fun j _ => ?_
    simp only [honestRound2Message, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id',
      id_eq, sum_mul]
    exact sum_congr rfl fun i _ => by ring

variable {F : Type*} [Field F]

omit [Fintype ι₂] in
/-- **The honest second message satisfies the grand-product claim.** For a matrix of bits `f` and
every unit `g`, the honest second message satisfies `GrandProductClaim`. -/
theorem grandProductClaim_honestRound2Message (g : Fˣ) (a : ι₁ → MvPolynomial (Fin k) ℤ)
    {f : ι₁ × ι₂ → ℕ} (hf : ∀ p, f p ≤ 1) (q : ℕ) (α : Fin k → ZMod q) :
    GrandProductClaim g a f q α (honestRound2Message q α a f) := fun j =>
  prod_bitFactor_eq_pow (g : F) (fun i => (reduceAt q α (a i)).val) (fun i => f (i, j))
    (fun _ => hf _)

section Bitified

variable {S R : Type*} [CommSemiring S] [CommSemiring R] {M : Type*} [Fintype M] [DecidableEq ι₁]
  [DecidableEq ι₂]

/-- **The honest first message of a bitified claim.** Let `πc : ℤ[X₁, …, X_k] → R` and let `a`, `b`
be lifts of `v₁` and of the bitified weights `bitWeights ψ γ B v₂`. For every vector `bits` of
natural numbers, in particular a vector of bits, `πc` sends the honest message for `bits` to the
original inner product `⟨v₁ ⊗ v₂, ψ(L · bits)⟩`, so the equation `πc μ' = μ` checked by the
verifier holds for the honest message exactly when the original claim does. -/
theorem map_honestMessage_bitified (πc : MvPolynomial (Fin k) ℤ →+* R) (ψ : S →+* R) (γ : M → S)
    (B : ℕ) {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ × Fin B × M → MvPolynomial (Fin k) ℤ}
    {v₁ : ι₁ → R} {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i)
    (hb : ∀ j, πc (b j) = bitWeights ψ γ B v₂ j) (bits : (ι₁ × ι₂) × Fin B × M → ℕ) :
    πc (honestMessage a b (fun p => bits ((p.1, p.2.1), p.2.2))) =
      (fun p : ι₁ × ι₂ => v₁ p.1 * v₂ p.2) ⬝ᵥ
        (fun p => ψ ((bitMatrix γ B *ᵥ fun x => (bits x : S)) p)) := by
  rw [map_honestMessage, dotProduct_tensor_map_bitMatrix_mulVec]
  exact sum_congr rfl fun p _ => by rw [ha, hb]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- **The honest first message of a bounded witness.** If a witness `f` has entries
`∑ⱼ h(p, j) * γⱼ` with digits `h(p, j) < 2 ^ B`, the honest first message for its bits
`coeffBits B h` is sent by `πc` to the original claim `⟨v₁ ⊗ v₂, ψ(f)⟩`. -/
theorem map_honestMessage_coeffBits (πc : MvPolynomial (Fin k) ℤ →+* R) (ψ : S →+* R) (γ : M → S)
    {B : ℕ} {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ × Fin B × M → MvPolynomial (Fin k) ℤ}
    {v₁ : ι₁ → R} {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i)
    (hb : ∀ j, πc (b j) = bitWeights ψ γ B v₂ j) (h : ι₁ × ι₂ → M → ℕ)
    (hlt : ∀ p j, h p j < 2 ^ B) :
    πc (honestMessage a b (fun p => coeffBits B h ((p.1, p.2.1), p.2.2))) =
      (fun p : ι₁ × ι₂ => v₁ p.1 * v₂ p.2) ⬝ᵥ (fun p => ψ (∑ j, (h p j : S) * γ j)) := by
  classical
  rw [map_honestMessage_bitified πc ψ γ B ha hb (coeffBits B h), bitMatrix_mulVec_coeffBits γ h hlt]

end Bitified

end BitZ
