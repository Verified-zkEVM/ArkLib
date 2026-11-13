/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Commitments.Functional.BitZ.Round1
public import ArkLib.Commitments.Functional.BitZ.Round2

/-!
# BitZ: the fixed-witness error of Rounds 1 and 2

The proof of [BGKLSW26, Theorem 4.7] decomposes Construction 4.4 into three IORs. The first,
`Π₁`, consists of Round 1, where the prover sends an integer polynomial `μ'`, and Round 2, where,
for a prime `q` and a point `α ∈ 𝔽_qᵏ` chosen by the verifier at the end of Round 1 (the map
`π_rand` of Lemma 4.3 reduces modulo `q` and evaluates at `α`), the prover sends integers
`μ₁, …, μ_{ℓ₂}`. The verifier of Round 2 checks the range of each `μⱼ` and the weighted sum (39).
Phase 3 then hands the grand-product claim (40) about the bit matrix `f` to the grand-product
reduction `Π_red`, as the instance (41). This file joins `BitZ.prEvent_claim_le` (Round 1) and
`BitZ.sum_prod_mul_mul_eq_of_prod_bitFactor_eq_pow` (Round 2) into one bound on the event that
some second message passes the checks of Round 2 and makes the grand-product claim true.

The witness `f` and the first message `μ'` are fixed, and `μ'` satisfies the Round 1 checks. The
passage from a fixed `f` to `∃ w` (unique decoding), the proximity condition, the knowledge-state
function and Round 0 are not formalized here.

## Main statements

* `BitZ.Round2Check` is the verifier's check of Round 2 on a message `μ`: the range of each `μⱼ`
  and the weighted sum against the reduced second tensor factor. It is decidable.
* `BitZ.GrandProductClaim` is the grand-product claim for the bit matrix `f` and a message `μ`. It
  is decidable over a field with decidable equality.
* `BitZ.Round2Satisfiable` says that, at `(q, α)`, some message passes `Round2Check` and satisfies
  `GrandProductClaim`.
* `BitZ.sum_prod_mul_mul_eq_of_round2Satisfiable` shows that the reduced tensor claim then holds at
  `(q, α)`.
* `BitZ.prEvent_round2Satisfiable_le` bounds the probability of `Round2Satisfiable` for a false
  claim, over a uniform prime followed by a uniform point, by the error of Round 1.

`Round2Satisfiable` quantifies over all messages, so it is a mathematical event. The bound needs the
grand-product claim: for `Round2Check` alone it fails (see the test).

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset MvPolynomial
open scoped ProbabilityTheory

namespace BitZ

variable {k : ℕ} {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {F : Type*} [Field F]

/-- The verifier's check of Round 2 on a message `μ`, for a lift `b` of the second tensor factor
and a first message `μ'`, at the prime `q` and the point `α`: each `μⱼ` is at most `ℓ₁ · (q - 1)`,
and the weighted sum `∑ⱼ μⱼ · b̄ⱼ` equals the reduction of `μ'`, where the bars are the
reductions `reduceAt q α`. -/
def Round2Check (ℓ₁ : ℕ) (b : ι₂ → MvPolynomial (Fin k) ℤ) (μ' : MvPolynomial (Fin k) ℤ) (q : ℕ)
    (α : Fin k → ZMod q) (μ : ι₂ → ℕ) : Prop :=
  (∀ j, μ j ≤ ℓ₁ * (q - 1)) ∧ ∑ j, (μ j : ZMod q) * reduceAt q α (b j) = reduceAt q α μ'

instance (ℓ₁ : ℕ) (b : ι₂ → MvPolynomial (Fin k) ℤ) (μ' : MvPolynomial (Fin k) ℤ) (q : ℕ)
    (α : Fin k → ZMod q) (μ : ι₂ → ℕ) : Decidable (Round2Check ℓ₁ b μ' q α μ) := by
  unfold Round2Check
  infer_instance

omit [Fintype ι₂] in
/-- The grand-product claim for a lift `a` of the first tensor factor, a matrix `f` and a message
`μ`, at the prime `q` and the point `α`: `∏ᵢ ((g ^ γᵢ - 1) · fᵢⱼ + 1) = g ^ μⱼ` for every `j`,
where `γᵢ` is the integer representative of the reduction of `aᵢ`. -/
def GrandProductClaim (g : Fˣ) (a : ι₁ → MvPolynomial (Fin k) ℤ) (f : ι₁ × ι₂ → ℕ) (q : ℕ)
    (α : Fin k → ZMod q) (μ : ι₂ → ℕ) : Prop :=
  ∀ j, ∏ i, (((g : F) ^ (reduceAt q α (a i)).val - 1) * (f (i, j) : F) + 1) = (g : F) ^ μ j

instance [DecidableEq F] (g : Fˣ) (a : ι₁ → MvPolynomial (Fin k) ℤ)
    (f : ι₁ × ι₂ → ℕ) (q : ℕ) (α : Fin k → ZMod q) (μ : ι₂ → ℕ) :
    Decidable (GrandProductClaim g a f q α μ) := by
  unfold GrandProductClaim
  infer_instance

/-- At `(q, α)`, some message `μ` passes `Round2Check` with the range bound `|ι₁| · (q - 1)` and
satisfies `GrandProductClaim` for the matrix `f`. -/
def Round2Satisfiable (g : Fˣ) (a : ι₁ → MvPolynomial (Fin k) ℤ) (b : ι₂ → MvPolynomial (Fin k) ℤ)
    (f : ι₁ × ι₂ → ℕ) (μ' : MvPolynomial (Fin k) ℤ) (q : ℕ) (α : Fin k → ZMod q) : Prop :=
  ∃ μ : ι₂ → ℕ, Round2Check (Fintype.card ι₁) b μ' q α μ ∧ GrandProductClaim g a f q α μ

/-- **The reduced tensor claim from the check and the claim of Round 2.** Let `g` generate `Fˣ`, let
`f` be a matrix of bits and assume `|ι₁| · (q - 1) < |F| - 1`. If some message passes `Round2Check`
and satisfies `GrandProductClaim` at `(q, α)`, then `∑ₚ ā(p₁) · b̄(p₂) · f p = μ̄'` in `𝔽_q`, where
the bars are the reductions `reduceAt q α`. -/
theorem sum_prod_mul_mul_eq_of_round2Satisfiable [Fintype F] {g : Fˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ → MvPolynomial (Fin k) ℤ} {f : ι₁ × ι₂ → ℕ} (hf : ∀ p, f p ≤ 1)
    {μ' : MvPolynomial (Fin k) ℤ} {q : ℕ} [NeZero q]
    (hord : Fintype.card ι₁ * (q - 1) < Fintype.card F - 1) {α : Fin k → ZMod q}
    (h : Round2Satisfiable g a b f μ' q α) :
    ∑ p : ι₁ × ι₂, reduceAt q α (a p.1) * reduceAt q α (b p.2) * (f p : ZMod q) =
      reduceAt q α μ' := by
  obtain ⟨μ, ⟨hμ, hc⟩, hgp⟩ := h
  exact sum_prod_mul_mul_eq_of_prod_bitFactor_eq_pow hg (fun i => (reduceAt q α (a i)).val)
    (fun i => ZMod.val_lt _) f hf μ hμ hord hgp (fun i => reduceAt q α (a i))
    (fun j => reduceAt q α (b j)) (fun i => ZMod.natCast_zmod_val _) _ hc

variable {R : Type*} [CommRing R]

/-- **The fixed-witness error of Rounds 1 and 2.** Let `π_canon : ℤ[X₁, …, X_k] → R` be a ring
homomorphism with lifts `a`, `b` of `v₁`, `v₂` and `π_canon(μ') = μ`. Let `f` be a matrix of bits
with `⟨v₁ ⊗ v₂, f⟩ ≠ μ`, let `g` generate `Fˣ`, and let `P` be a set of primes, each at least
`q_min ≥ 2`, with `|ι₁| · (q - 1) < |F| - 1` for `q ∈ P`. With the degree and norm bounds of
`prEvent_claim_le`, for a uniform prime `q ∈ P` followed by a uniform point `α ∈ 𝔽_qᵏ`, the
probability that some message passes the check of Round 2 and satisfies the grand-product claim
for `f` is at most `⌊log_{q_min}(2TℓN²)⌋ / |P| + 2D / q_min`, where `T = C(D + k, k)` and
`ℓ = |ι₁| · |ι₂|`. -/
theorem prEvent_round2Satisfiable_le [Fintype F] {g : Fˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (πc : MvPolynomial (Fin k) ℤ →+* R)
    {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R}
    {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i) (hb : ∀ j, πc (b j) = v₂ j) {f : ι₁ × ι₂ → ℕ}
    (hf : ∀ p, f p ≤ 1) {μ : R} {μ' : MvPolynomial (Fin k) ℤ} (hμ : πc μ' = μ)
    (hfalse : ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : R) ≠ μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμD : μ'.totalDegree ≤ 2 * D)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤ (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2)
    {P : Finset ℕ} [SampleableType ↥P] (hP : ∀ q ∈ P, q.Prime) {qmin : ℕ} (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q)
    (hord : ∀ q ∈ P, Fintype.card ι₁ * (q - 1) < Fintype.card F - 1) :
    Pr{let q ← $ᵗ ↥P; let α ← modPointSample hP q}[
      Round2Satisfiable g a b f μ' q.val α] ≤
      ENNReal.ofReal ((Nat.log qmin (2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2) : ℝ) /
        #P + ((2 * D : ℕ) : ℝ) / qmin) := by
  refine le_trans ?_
    (prEvent_claim_le πc ha hb hf hμ hfalse haD hbD haN hbN hμD hμN hP hq2 hqmin)
  simpa only [id_map] using prEvent_bind_mono_of_forall_le ($ᵗ ↥P)
    (fun q => (fun α => Round2Satisfiable g a b f μ' q.val α) <$> modPointSample hP q)
    (fun q => (fun α => ∑ p : ι₁ × ι₂, reduceAt q.val α (a p.1) * reduceAt q.val α (b p.2) *
      (f p : ZMod q.val) = reduceAt q.val α μ') <$> modPointSample hP q) id id fun q =>
    prEvent_map_le_map _ _ _ id id fun α h =>
      have : NeZero q.val := ⟨(hP q.val q.property).ne_zero⟩
      sum_prod_mul_mul_eq_of_round2Satisfiable hg hf (hord q.val q.property) h

end BitZ
