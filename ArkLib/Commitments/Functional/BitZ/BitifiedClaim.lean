/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Commitments.Functional.BitZ.Bitification
public import ArkLib.Commitments.Functional.BitZ.FixedWitnessError

/-!
# BitZ: the bitified claim and its fixed-witness error

[BGKLSW26, Theorem 4.15] derives the round-by-round knowledge soundness of the protocol for a
witness over a finitely generated ring `S` from the proof of Theorem 4.7 applied to the bitified
claim `⟨g, u⟩ = μ`, `u = ψ(L)ᵀ v`. Two facts connect the two claims, and they are formalized here
with no protocol attached.

* A tensor decomposition `v = v⁽¹⁾ ⊗ v⁽²⁾` of the weights gives a tensor decomposition
  `u = v⁽¹⁾ ⊗ u⁽²⁾` with `u⁽²⁾ = v⁽²⁾ ⊗ (1, …, 2^{B-1}) ⊗ ψ(γ)` of the bitified weights
  ([BGKLSW26, Remark 4.14]), so the two rounds apply unchanged.
* For a vector of bits, the original claim `⟨v, ψ(L g)⟩` is the bitified claim ([BGKLSW26,
  Lemma 4.12]; this is the claim part of Appendix B.1, (65)). If no witness with entries in the
  bounded set `S^{<D}_{≤B}` satisfies the original claim, then by the closure of Definition 4.9 the
  bitified claim is false for every vector of bits.

## Main statements

* `BitZ.bitWeights_tensor` and `BitZ.dotProduct_bitWeights_tensor` are the tensor decomposition
  of the bitified weights.
* `BitZ.dotProduct_tensor_map_bitMatrix_mulVec` is the identification of the original and
  bitified claims in the shape consumed by the rounds.
* `BitZ.prEvent_round2Satisfiable_le_bitified` is the bound of
  `BitZ.prEvent_round2Satisfiable_le` for the bitified claim: for a vector of bits on which the
  original claim is false, the probability that some second message passes the check of Round 2 and
  satisfies the grand-product claim is at most the error of Round 1, with the length
  `ℓ = ℓ₀ · B · d` of the bitified vector.
* `BitZ.prEvent_round2Satisfiable_le_bitified_of_forall_mem_boundedCombos` is the same bound for
  every vector of bits when no witness with entries in `boundedCombos γ B` satisfies the original
  claim.

An eq vector is a tensor of eq vectors by `CompPoly.CMlPolynomialEval.eqTilde_append`. The tensor
decomposition and the identification of claims hold over commutative semirings; the error bound
needs a commutative ring `R` for the fingerprinting of Round 1.

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset MvPolynomial Matrix
open scoped ProbabilityTheory

namespace BitZ

section Tensor

variable {S R : Type*} [CommSemiring S] [CommSemiring R] (ψ : S →+* R) {M : Type*}
  {ι₁ ι₂ : Type*}

/-- If `v = v₁ ⊗ v₂` then the bitified weights are the tensor of `v₁` with the bitified weights of
`v₂`, reading the index `((i₁, i₂), k, j)` as `(i₁, (i₂, k, j))`. -/
theorem bitWeights_tensor (γ : M → S) (B : ℕ) (v₁ : ι₁ → R) (v₂ : ι₂ → R)
    (x : (ι₁ × ι₂) × Fin B × M) :
    bitWeights ψ γ B (fun p => v₁ p.1 * v₂ p.2) x =
      v₁ x.1.1 * bitWeights ψ γ B v₂ (x.1.2, x.2) := by
  simp only [bitWeights]
  ring

/-- **The bitified inner product in tensor form.** For `v = v₁ ⊗ v₂` and any `g`, the inner product
of `g` with the bitified weights is the sum of `v₁ i * u₂ j * g((i, j))` over the pairs `(i, j)`
with `j = (i₂, k, j')`, where `u₂ = bitWeights ψ γ B v₂`. -/
theorem dotProduct_bitWeights_tensor [Fintype ι₁] [Fintype ι₂] [Fintype M] (γ : M → S) (B : ℕ)
    (v₁ : ι₁ → R) (v₂ : ι₂ → R) (g : (ι₁ × ι₂) × Fin B × M → R) :
    g ⬝ᵥ bitWeights ψ γ B (fun p => v₁ p.1 * v₂ p.2) =
      ∑ p : ι₁ × ι₂ × Fin B × M,
        v₁ p.1 * bitWeights ψ γ B v₂ p.2 * g ((p.1, p.2.1), p.2.2) := by
  rw [dotProduct]
  refine Fintype.sum_equiv (Equiv.prodAssoc ι₁ ι₂ (Fin B × M)) _ _ fun x => ?_
  simp only [Equiv.prodAssoc_apply, bitWeights_tensor]
  ring

variable [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Fintype M]

/-- **The original claim is the bitified claim.** For `v = v₁ ⊗ v₂` and a vector of bits `g`, the
original inner product `⟨v, ψ(L g)⟩` equals the sum of `v₁ i * u₂ j * g((i, j))` over the pairs
`(i, j)`, where `u₂ = bitWeights ψ γ B v₂` and the column `j = (i₂, k, j')` ranges over
`ι₂ × Fin B × M`. -/
theorem dotProduct_tensor_map_bitMatrix_mulVec (γ : M → S) (B : ℕ) (v₁ : ι₁ → R) (v₂ : ι₂ → R)
    (g : (ι₁ × ι₂) × Fin B × M → ℕ) :
    (fun p : ι₁ × ι₂ => v₁ p.1 * v₂ p.2) ⬝ᵥ
        (fun p => ψ ((bitMatrix γ B *ᵥ fun x => (g x : S)) p)) =
      ∑ p : ι₁ × ι₂ × Fin B × M, v₁ p.1 * bitWeights ψ γ B v₂ p.2 *
        ((g ((p.1, p.2.1), p.2.2) : ℕ) : R) := by
  rw [dotProduct_map_bitMatrix_mulVec]
  simp only [map_natCast]
  exact dotProduct_bitWeights_tensor ψ γ B v₁ v₂ fun p => (g p : R)

end Tensor

section Error

variable {k : ℕ} {S R : Type*} [CommSemiring S] [CommRing R] {M : Type*} [Fintype M]
  {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  {F : Type*} [Field F] [Fintype F]

/-- **The fixed-witness error for a bitified claim.** Let `ψ : S →+* R`, let `L` be the standard
bitification matrix and let `v = v₁ ⊗ v₂`. Let `bits` be a vector of bits for which the original
claim `⟨v, ψ(L · bits)⟩ = μ` is false, let `π_canon(μ') = μ`, and let `a`, `b` be lifts of `v₁` and
of the bitified weights `u₂ = bitWeights ψ γ B v₂` with the degree and norm bounds of
`prEvent_claim_le` for the bitified length `ℓ = ℓ₀ · B · d`. Let `g` generate `Fˣ`, and let
`|ι₁| · (q - 1) < |F| - 1` for the primes `q ∈ P`. For a uniform prime followed by a uniform point,
the probability that some message passes the check of Round 2 and satisfies the grand-product claim
for the bits is at most `⌊log_{q_min}(2TℓN²)⌋ / |P| + 2D / q_min`. -/
theorem prEvent_round2Satisfiable_le_bitified {g : Fˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (πc : MvPolynomial (Fin k) ℤ →+* R) (ψ : S →+* R) (γ : M → S) (B : ℕ)
    {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ × Fin B × M → MvPolynomial (Fin k) ℤ}
    {v₁ : ι₁ → R} {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i)
    (hb : ∀ j, πc (b j) = bitWeights ψ γ B v₂ j) {bits : (ι₁ × ι₂) × Fin B × M → ℕ}
    (hbits : ∀ x, bits x ≤ 1) {μ : R} {μ' : MvPolynomial (Fin k) ℤ} (hμ : πc μ' = μ)
    (hfalse : (fun p : ι₁ × ι₂ => v₁ p.1 * v₂ p.2) ⬝ᵥ
      (fun p => ψ ((bitMatrix γ B *ᵥ fun x => (bits x : S)) p)) ≠ μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμD : μ'.totalDegree ≤ 2 * D)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤
      (D + k).choose k * Fintype.card (ι₁ × ι₂ × Fin B × M) * N ^ 2)
    {P : Finset ℕ} [SampleableType ↥P] (hP : ∀ q ∈ P, q.Prime) {qmin : ℕ} (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q)
    (hord : ∀ q ∈ P, Fintype.card ι₁ * (q - 1) < Fintype.card F - 1) :
    Pr{let q ← $ᵗ ↥P; let α ← MvPolynomial.modPointSample hP q}[
      Round2Satisfiable g a b (fun p => bits ((p.1, p.2.1), p.2.2)) μ' q.val α] ≤
      ENNReal.ofReal ((Nat.log qmin
        (2 * (D + k).choose k * Fintype.card (ι₁ × ι₂ × Fin B × M) * N ^ 2) : ℝ) / #P +
        ((2 * D : ℕ) : ℝ) / qmin) :=
  prEvent_round2Satisfiable_le hg πc ha hb (fun p => hbits _) hμ
    (by rwa [← dotProduct_tensor_map_bitMatrix_mulVec ψ γ B v₁ v₂ bits]) haD hbD haN hbN hμD hμN
    hP hq2 hqmin hord

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- **The fixed-witness error for an original claim with no bounded solution.** Assume that no
witness `f` with entries in `boundedCombos γ B` satisfies `⟨v₁ ⊗ v₂, ψ(f)⟩ = μ`. By the closure
property `bitMatrix_mulVec_mem`, the original claim is then false for every vector of bits, so the
bound of `prEvent_round2Satisfiable_le_bitified` holds for every vector of bits, with the same
lifts, degree and norm bounds, generator and primes. -/
theorem prEvent_round2Satisfiable_le_bitified_of_forall_mem_boundedCombos {g : Fˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (πc : MvPolynomial (Fin k) ℤ →+* R) (ψ : S →+* R)
    (γ : M → S) (B : ℕ) {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ × Fin B × M → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R} {v₂ : ι₂ → R}
    (ha : ∀ i, πc (a i) = v₁ i) (hb : ∀ j, πc (b j) = bitWeights ψ γ B v₂ j) {μ : R}
    (hno : ∀ f : ι₁ × ι₂ → S, (∀ p, f p ∈ boundedCombos γ B) →
      (fun p : ι₁ × ι₂ => v₁ p.1 * v₂ p.2) ⬝ᵥ (fun p => ψ (f p)) ≠ μ)
    {bits : (ι₁ × ι₂) × Fin B × M → ℕ} (hbits : ∀ x, bits x ≤ 1) {μ' : MvPolynomial (Fin k) ℤ}
    (hμ : πc μ' = μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμD : μ'.totalDegree ≤ 2 * D)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤
      (D + k).choose k * Fintype.card (ι₁ × ι₂ × Fin B × M) * N ^ 2)
    {P : Finset ℕ} [SampleableType ↥P] (hP : ∀ q ∈ P, q.Prime) {qmin : ℕ} (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q)
    (hord : ∀ q ∈ P, Fintype.card ι₁ * (q - 1) < Fintype.card F - 1) :
    Pr{let q ← $ᵗ ↥P; let α ← MvPolynomial.modPointSample hP q}[
      Round2Satisfiable g a b (fun p => bits ((p.1, p.2.1), p.2.2)) μ' q.val α] ≤
      ENNReal.ofReal ((Nat.log qmin
        (2 * (D + k).choose k * Fintype.card (ι₁ × ι₂ × Fin B × M) * N ^ 2) : ℝ) / #P +
        ((2 * D : ℕ) : ℝ) / qmin) := by
  classical
  exact prEvent_round2Satisfiable_le_bitified hg πc ψ γ B ha hb hbits hμ
    (hno _ (bitMatrix_mulVec_mem γ B bits hbits)) haD hbD haN hbN hμD hμN hP hq2 hqmin hord

end Error

end BitZ
