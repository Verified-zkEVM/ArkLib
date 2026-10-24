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
`μ' = ⟨a ⊗ b, f⟩` for lifts `a`, `b` of the two tensor factors of the weights, and in Round 2, for
a prime `q` and a point `α`, the integers `μⱼ = ∑ᵢ γᵢ · fᵢⱼ`, where `γᵢ` is the integer
representative of the reduction of `aᵢ`. This file proves that these messages pass the verifier's
checks, which is the completeness half of [BGKLSW26, Theorem 4.7] and, through the identification
of the original and bitified claims, of [BGKLSW26, Theorem 4.15].

## Main statements

* `BitZ.honestMessage` is the honest first message `μ'`, and `BitZ.claimPoly_eq_honestMessage_sub`
  identifies `BitZ.claimPoly` with the honest message minus the prover's message. Its degree is
  bounded by `BitZ.totalDegree_honestMessage_le`, its coefficients by
  `BitZ.natAbs_coeff_honestMessage_le`, and `BitZ.map_honestMessage` computes its image under a
  ring homomorphism.
* `BitZ.honestRound2Message` is the honest second message.
  `BitZ.round2Check_honestRound2Message` shows that it passes `BitZ.Round2Check` against the honest
  first message at every prime and every point, with no hypothesis on the generator and no overflow
  bound, because the checks are identities for bits.
* `BitZ.map_honestMessage_bitified` shows that the canonical image of the honest first message for
  a vector of bits is the original claim `⟨v, ψ(L g)⟩`, so the equation `π_canon(μ') = μ` checked
  by the verifier holds exactly when the original claim does.

`honestRound2Message` is executable. `honestMessage` uses Mathlib's noncomputable polynomial ring
operations, so it is a mathematical object; an implementation of the prover would compute the
same polynomial in a computational representation.

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

/-- The tensor polynomial `⟨a ⊗ b, f⟩ = ∑ₚ a(p₁) * b(p₂) * f(p)` that an honest prover sends as its
first message. -/
noncomputable def honestMessage (a : ι₁ → MvPolynomial (Fin k) ℤ)
    (b : ι₂ → MvPolynomial (Fin k) ℤ) (f : ι₁ × ι₂ → ℕ) : MvPolynomial (Fin k) ℤ :=
  ∑ p : ι₁ × ι₂, a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ)

/-- The difference `claimPoly a b f μ'` is the honest message minus the prover's message. -/
theorem claimPoly_eq_honestMessage_sub (a : ι₁ → MvPolynomial (Fin k) ℤ)
    (b : ι₂ → MvPolynomial (Fin k) ℤ) (f : ι₁ × ι₂ → ℕ) (μ' : MvPolynomial (Fin k) ℤ) :
    claimPoly a b f μ' = honestMessage a b f - μ' :=
  rfl

/-- The honest message has total degree at most `2D` when the lifts have total degree at most
`D`. -/
theorem totalDegree_honestMessage_le {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ → MvPolynomial (Fin k) ℤ} {f : ι₁ × ι₂ → ℕ} {D : ℕ} (ha : ∀ i, (a i).totalDegree ≤ D)
    (hb : ∀ j, (b j).totalDegree ≤ D) : (honestMessage a b f).totalDegree ≤ 2 * D := by
  have h := totalDegree_claimPoly_le (f := f) (μ' := 0) ha hb (by simp)
  rwa [claimPoly_eq_honestMessage_sub, sub_zero] at h

/-- A ring homomorphism out of `ℤ[X₁, …, X_k]` carries the honest message to
`⟨φ(a) ⊗ φ(b), f⟩`. -/
theorem map_honestMessage {K : Type*} [CommSemiring K] (φ : MvPolynomial (Fin k) ℤ →+* K)
    (a : ι₁ → MvPolynomial (Fin k) ℤ) (b : ι₂ → MvPolynomial (Fin k) ℤ) (f : ι₁ × ι₂ → ℕ) :
    φ (honestMessage a b f) = ∑ p : ι₁ × ι₂, φ (a p.1) * φ (b p.2) * (f p : K) := by
  simp only [honestMessage, map_sum, map_mul, map_natCast]

/-- The honest second message: `μⱼ = ∑ᵢ γᵢ * f(i, j)`, where `γᵢ` is the integer representative of
the reduction of `aᵢ` at `(q, α)`. -/
def honestRound2Message (q : ℕ) (α : Fin k → ZMod q) (a : ι₁ → MvPolynomial (Fin k) ℤ)
    (f : ι₁ × ι₂ → ℕ) : ι₂ → ℕ :=
  fun j => ∑ i, (reduceAt q α (a i)).val * f (i, j)

variable {F : Type*} [Field F]

/-- **The honest messages pass Round 2.** For a matrix of bits `f`, the honest second message
passes `Round2Check` against the honest first message, at every prime `q` and every point `α`, for
every unit `g`. -/
theorem round2Check_honestRound2Message (g : Fˣ) (a : ι₁ → MvPolynomial (Fin k) ℤ)
    (b : ι₂ → MvPolynomial (Fin k) ℤ) {f : ι₁ × ι₂ → ℕ} (hf : ∀ p, f p ≤ 1) (q : ℕ) [NeZero q]
    (α : Fin k → ZMod q) :
    Round2Check g a b f (honestMessage a b f) q α (honestRound2Message q α a f) := by
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · calc ∑ i, (reduceAt q α (a i)).val * f (i, j) ≤ ∑ _i : ι₁, (q - 1) * 1 :=
          sum_le_sum fun i _ => Nat.mul_le_mul (Nat.le_sub_one_of_lt (ZMod.val_lt _)) (hf _)
      _ = Fintype.card ι₁ * (q - 1) := by simp [mul_comm]
  · rw [map_honestMessage, Fintype.sum_prod_type_right]
    refine sum_congr rfl fun j _ => ?_
    simp only [honestRound2Message, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id',
      id_eq, sum_mul]
    exact sum_congr rfl fun i _ => by ring
  · exact prod_bitFactor_eq_pow (g : F) (fun i => (reduceAt q α (a i)).val) (fun i => f (i, j))
      (fun i => hf _)

section Bitified

variable {S R : Type*} [CommSemiring S] [CommSemiring R] {M : Type*} [Fintype M] [DecidableEq ι₁]
  [DecidableEq ι₂]

/-- **The honest first message of a bitified claim.** Let `πc : ℤ[X₁, …, X_k] → R`, let `a`, `b` be
lifts of `v₁` and of the bitified weights `bitWeights ψ γ B v₂`, and let `bits` be a vector of bits.
Then `πc` sends the honest message for `bits` to the original inner product
`⟨v₁ ⊗ v₂, ψ(L · bits)⟩`, so the equation `πc μ' = μ` checked by the verifier holds for the honest
message exactly when the original claim does. -/
theorem map_honestMessage_bitified (πc : MvPolynomial (Fin k) ℤ →+* R) (ψ : S →+* R) (γ : M → S)
    (B : ℕ) {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ × Fin B × M → MvPolynomial (Fin k) ℤ}
    {v₁ : ι₁ → R} {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i)
    (hb : ∀ j, πc (b j) = bitWeights ψ γ B v₂ j) (bits : (ι₁ × ι₂) × Fin B × M → ℕ) :
    πc (honestMessage a b (fun p => bits ((p.1, p.2.1), p.2.2))) =
      (fun p : ι₁ × ι₂ => v₁ p.1 * v₂ p.2) ⬝ᵥ
        (fun p => ψ ((bitMatrix γ B *ᵥ fun x => (bits x : S)) p)) := by
  rw [map_honestMessage, dotProduct_tensor_map_bitMatrix_mulVec]
  exact sum_congr rfl fun p _ => by rw [ha, hb]

end Bitified

end BitZ
