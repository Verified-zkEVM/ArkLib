/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Data.MvPolynomial.PrimeFingerprintProbability
public import ArkLib.ToMathlib.MvPolynomial.CoeffBound
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# BitZ: fingerprinting a fixed bit claim

Round 1 of [BGKLSW26, Construction 4.4] replaces a claim `⟨π(f), v⟩ = µ` in a finitely generated
ring `R` by a claim over a small prime field `𝔽_q`. With the canonical map
`π_canon : ℤ[X₁, …, X_k] → R` and a section `π_canon⁻¹` (the *lift*), the prover sends an integer
polynomial `µ'` with `⟨π_canon⁻¹(v⁽¹⁾) ⊗ π_canon⁻¹(v⁽²⁾), f⟩ = µ'`, the verifier checks bounds on
`µ'` and `π_canon(µ') = µ`, and a random prime `q` and a random point `α ∈ 𝔽_qᵏ` reduce the
polynomial identity to `𝔽_q`.

This file proves the algebraic and probabilistic content of the first half of the proof of
[BGKLSW26, Theorem 4.7], for a fixed witness `f` of bits that does *not* satisfy the original
claim: the difference `h := ⟨π_canon⁻¹(v⁽¹⁾) ⊗ π_canon⁻¹(v⁽²⁾), f⟩ - µ'` is a nonzero polynomial
of total degree `≤ 2D` with `‖h‖∞ ≤ M := 2 · T · ℓ · N_R²`, so by fingerprinting (Lemma 4.3) the
reduced claim holds with probability at most `⌊log_{q_min} M⌋ / |P| + 2D / q_min`. This is at most
the error `κ₀ = log₂ M / (⌊log₂ q_min⌋ · |P|) + 2D / q_min` of Theorem 4.7. The passage from a
fixed `f` to `∃ w` (uniqueness of the witness within the unique-decoding radius) and the
knowledge-state function are not formalized here.

## Main statements

* `BitZ.claimPoly` is the polynomial `h`;
* `BitZ.totalDegree_claimPoly_le` and `BitZ.natAbs_coeff_claimPoly_le` bound its degree and norm;
* `BitZ.natAbs_coeff_honestMessage_le` is the norm bound `T · ℓ · N²` on the honest prover's `µ'`,
  the quantity the verifier checks;
* `BitZ.claimPoly_ne_zero` shows `h ≠ 0` when the claim over `R` is false;
* `BitZ.zeroCountMod_claimPoly` identifies solutions of the reduced claim with zeros of `h`;
* `BitZ.avg_card_claim_le` bounds the fraction of points satisfying the reduced claim, averaged
  over the primes, by `⌊log_{q_min} M⌋ / |P| + 2D / q_min`;
  `BitZ.avg_card_claim_le_logb` gives the bound `κ₀` of [BGKLSW26, Lemma 4.3].
* `BitZ.prEvent_claim_le` gives the bound for a uniform prime followed by a uniform field point.

`reduceAt` evaluates directly with coefficient reduction and is executable. `claimPoly` is a
mathematical error polynomial for the soundness proof: its construction uses Mathlib's
noncomputable polynomial ring operations. It is not an implementation of the prover.

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset MvPolynomial
open scoped BigOperators

namespace BitZ

variable {k : ℕ} {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The difference `⟨a ⊗ b, f⟩ - µ'` between the tensor claim on the lifts and the prover's
polynomial message. -/
noncomputable def claimPoly (a : ι₁ → MvPolynomial (Fin k) ℤ) (b : ι₂ → MvPolynomial (Fin k) ℤ)
    (f : ι₁ × ι₂ → ℕ) (μ' : MvPolynomial (Fin k) ℤ) : MvPolynomial (Fin k) ℤ :=
  ∑ p : ι₁ × ι₂, a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ) - μ'

/-- A ring homomorphism carries `claimPoly a b f µ'` to `⟨φ(a) ⊗ φ(b), f⟩ - φ(µ')`. -/
theorem map_claimPoly {K : Type*} [CommRing K] (φ : MvPolynomial (Fin k) ℤ →+* K)
    (a : ι₁ → MvPolynomial (Fin k) ℤ) (b : ι₂ → MvPolynomial (Fin k) ℤ) (f : ι₁ × ι₂ → ℕ)
    (μ' : MvPolynomial (Fin k) ℤ) :
    φ (claimPoly a b f μ') = ∑ p : ι₁ × ι₂, φ (a p.1) * φ (b p.2) * (f p : K) - φ μ' := by
  simp [claimPoly, map_sum]

/-- The total degree of `claimPoly a b f µ'` is at most `2D` when both lift families have degree
`≤ D` and the message has degree `≤ 2D`. -/
theorem totalDegree_claimPoly_le {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ → MvPolynomial (Fin k) ℤ} {f : ι₁ × ι₂ → ℕ} {μ' : MvPolynomial (Fin k) ℤ} {D : ℕ}
    (ha : ∀ i, (a i).totalDegree ≤ D) (hb : ∀ j, (b j).totalDegree ≤ D)
    (hμ : μ'.totalDegree ≤ 2 * D) : (claimPoly a b f μ').totalDegree ≤ 2 * D := by
  unfold claimPoly
  refine (totalDegree_sub _ _).trans (max_le ?_ hμ)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun p _ => ?_)
  have hf : (f p : MvPolynomial (Fin k) ℤ).totalDegree = 0 := by
    rw [← map_natCast (C : ℤ →+* MvPolynomial (Fin k) ℤ)]
    exact totalDegree_C _
  refine (totalDegree_mul _ _).trans ?_
  rw [hf]
  have hab := (totalDegree_mul (a p.1) (b p.2)).trans (Nat.add_le_add (ha p.1) (hb p.2))
  omega

/-- For bits `f` and lifts with coefficients bounded by `N`, the coefficients of the honest
tensor polynomial `⟨a ⊗ b, f⟩` are bounded by `TℓN²`, where `T = C(D + k, k)` and
`ℓ = |ι₁| · |ι₂|`. Only the `a i` need total degree `≤ D`; no degree bound on `b j` is needed. -/
theorem natAbs_coeff_honestMessage_le {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ → MvPolynomial (Fin k) ℤ} {f : ι₁ × ι₂ → ℕ} {D N : ℕ} (hf : ∀ p, f p ≤ 1)
    (ha : ∀ i, (a i).totalDegree ≤ D) (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N)
    (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N) (s : Fin k →₀ ℕ) :
    ((∑ p : ι₁ × ι₂, a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ)).coeff s).natAbs ≤
      (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2 := by
  classical
  rw [coeff_sum]
  refine (Int.natAbs_sum_le _ _).trans ?_
  calc
    ∑ p : ι₁ × ι₂, ((a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ)).coeff s).natAbs
        ≤ ∑ _p : ι₁ × ι₂, (D + k).choose k * N ^ 2 := by
      apply sum_le_sum
      intro p _
      rw [mul_comm, ← map_natCast (C : ℤ →+* MvPolynomial (Fin k) ℤ), coeff_C_mul,
        Int.natAbs_mul]
      have hprod : ((a p.1 * b p.2).coeff s).natAbs ≤ (D + k).choose k * (N * N) := by
        simpa only [Fintype.card_fin] using
          natAbs_coeff_mul_le (ha p.1) (haN p.1) (hbN p.2) s
      have hbit : (f p : ℤ).natAbs ≤ 1 := by simpa using hf p
      simpa [pow_two] using Nat.mul_le_mul hbit hprod
    _ = _ := by simp [mul_comm, mul_assoc]

/-- The coefficients of `claimPoly a b f µ'` are bounded by `2TℓN²` when `f` consists of bits,
both lift families have coefficients bounded by `N`, the `a i` have degree `≤ D`, and `µ'` has
coefficients bounded by `TℓN²`. Here `T = C(D + k, k)` and `ℓ = |ι₁| · |ι₂|`.
No degree bound on `b j` is needed. -/
theorem natAbs_coeff_claimPoly_le {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ → MvPolynomial (Fin k) ℤ} {f : ι₁ × ι₂ → ℕ} {μ' : MvPolynomial (Fin k) ℤ} {D N : ℕ}
    (hf : ∀ p, f p ≤ 1) (ha : ∀ i, (a i).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤ (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2)
    (s : Fin k →₀ ℕ) :
    ((claimPoly a b f μ').coeff s).natAbs ≤
      2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2 := by
  unfold claimPoly
  rw [coeff_sub]
  refine (Int.natAbs_sub_le _ _).trans ?_
  calc _ ≤ _ + _ := Nat.add_le_add (natAbs_coeff_honestMessage_le hf ha haN hbN s) (hμN s)
    _ = _ := by ring

section Nonvanishing

variable {R : Type*} [CommRing R]

/-- **A false claim gives a nonzero polynomial.** Let `π_canon : ℤ[X₁, …, X_k] → R` be a ring
homomorphism, let `a`, `b` be lifts of `v₁`, `v₂` along `π_canon`, and `π_canon(µ') = µ`. If
`⟨v₁ ⊗ v₂, f⟩ ≠ µ` in `R`, then `claimPoly a b f µ'` is nonzero, since its canonical image is the
difference `⟨v₁ ⊗ v₂, f⟩ - µ`. -/
theorem claimPoly_ne_zero (πc : MvPolynomial (Fin k) ℤ →+* R) {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R} {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i)
    (hb : ∀ j, πc (b j) = v₂ j) (f : ι₁ × ι₂ → ℕ) {μ : R} {μ' : MvPolynomial (Fin k) ℤ}
    (hμ : πc μ' = μ) (hfalse : ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : R) ≠ μ) :
    claimPoly a b f μ' ≠ 0 := by
  intro h0
  have h := map_claimPoly πc a b f μ'
  rw [h0, map_zero, hμ] at h
  simp only [ha, hb] at h
  exact hfalse (sub_eq_zero.1 h.symm)

end Nonvanishing

section Reduction

/-- Reduce integer coefficients modulo `q`, then evaluate at `α : Fin k → ZMod q`. -/
def reduceAt (q : ℕ) (α : Fin k → ZMod q) : MvPolynomial (Fin k) ℤ →+* ZMod q :=
  eval₂Hom (Int.castRingHom (ZMod q)) α

@[simp]
theorem reduceAt_apply (q : ℕ) (α : Fin k → ZMod q) (h : MvPolynomial (Fin k) ℤ) :
    reduceAt q α h = eval α (map (Int.castRingHom (ZMod q)) h) :=
  eval₂_eq_eval_map _ _ _

/-- The number of points satisfying the reduced tensor claim is the number of zeros of the
difference polynomial modulo `q`. -/
theorem zeroCountMod_claimPoly (a : ι₁ → MvPolynomial (Fin k) ℤ) (b : ι₂ → MvPolynomial (Fin k) ℤ)
    (f : ι₁ × ι₂ → ℕ) (μ' : MvPolynomial (Fin k) ℤ) (q : ℕ) :
    zeroCountMod (claimPoly a b f μ') q =
      Nat.card {α : Fin k → ZMod q //
        ∑ p : ι₁ × ι₂, reduceAt q α (a p.1) * reduceAt q α (b p.2) * (f p : ZMod q) =
          reduceAt q α μ'} := by
  unfold zeroCountMod
  refine Nat.card_congr (Equiv.subtypeEquivRight fun α => ?_)
  rw [← reduceAt_apply, map_claimPoly, sub_eq_zero]

end Reduction

section Fingerprint

variable {R : Type*} [CommRing R]

/-- For a false tensor claim on bits and a message `µ'` with `πc µ' = µ`, the average fraction of
points satisfying the reduced claim is at most `⌊log_{q_min}(2TℓN²)⌋ / |P| + 2D / q_min`.
The lifts have degree `≤ D` and coefficients bounded by `N`; the message has degree `≤ 2D` and
coefficients bounded by `TℓN²`, where `T = C(D + k, k)` and `ℓ = |ι₁| · |ι₂|`.
All primes in `P` are at least `q_min ≥ 2`. -/
theorem avg_card_claim_le (πc : MvPolynomial (Fin k) ℤ →+* R)
    {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R}
    {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i) (hb : ∀ j, πc (b j) = v₂ j) {f : ι₁ × ι₂ → ℕ}
    (hf : ∀ p, f p ≤ 1) {μ : R} {μ' : MvPolynomial (Fin k) ℤ} (hμ : πc μ' = μ)
    (hfalse : ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : R) ≠ μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμD : μ'.totalDegree ≤ 2 * D)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤ (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2)
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {qmin : ℕ} (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q) :
    𝔼 q ∈ P, (Nat.card {α : Fin k → ZMod q //
        ∑ p : ι₁ × ι₂, reduceAt q α (a p.1) * reduceAt q α (b p.2) * (f p : ZMod q) =
          reduceAt q α μ'} : ℝ) / (q : ℝ) ^ k ≤
      (Nat.log qmin (2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2) : ℝ) / #P +
        ((2 * D : ℕ) : ℝ) / qmin := by
  have key := avg_zeroCountMod_div_le (claimPoly_ne_zero πc ha hb f hμ hfalse)
    (totalDegree_claimPoly_le haD hbD hμD)
    (natAbs_coeff_claimPoly_le hf haD haN hbN hμN) hP hq2 hqmin
  simpa only [zeroCountMod_claimPoly] using key

/-- The averaged reduced-claim error for a false bit claim, with the bound weakened to
`log₂(2TℓN²) / (⌊log₂ q_min⌋ · |P|) + 2D / q_min`.
Here `T = C(D + k, k)` and `ℓ = |ι₁| · |ι₂|`; the lift, message and prime bounds are those of
`avg_card_claim_le`. -/
theorem avg_card_claim_le_logb (πc : MvPolynomial (Fin k) ℤ →+* R)
    {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R}
    {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i) (hb : ∀ j, πc (b j) = v₂ j) {f : ι₁ × ι₂ → ℕ}
    (hf : ∀ p, f p ≤ 1) {μ : R} {μ' : MvPolynomial (Fin k) ℤ} (hμ : πc μ' = μ)
    (hfalse : ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : R) ≠ μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμD : μ'.totalDegree ≤ 2 * D)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤ (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2)
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {qmin : ℕ} (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q) :
    𝔼 q ∈ P, (Nat.card {α : Fin k → ZMod q //
        ∑ p : ι₁ × ι₂, reduceAt q α (a p.1) * reduceAt q α (b p.2) * (f p : ZMod q) =
          reduceAt q α μ'} : ℝ) / (q : ℝ) ^ k ≤
      Real.logb 2 ((2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2 : ℕ) : ℝ) /
          (Nat.log 2 qmin * #P) + ((2 * D : ℕ) : ℝ) / qmin := by
  have key := avg_zeroCountMod_div_le_logb (claimPoly_ne_zero πc ha hb f hμ hfalse)
    (totalDegree_claimPoly_le haD hbD hμD) (natAbs_coeff_claimPoly_le hf haD haN hbN hμN) hP hq2
    hqmin
  simpa only [zeroCountMod_claimPoly] using key

end Fingerprint

section Sampler

open scoped ProbabilityTheory

variable {R : Type*} [CommRing R]

/-- For a false bit claim, sample `q` uniformly from `P`, then `α` uniformly from `𝔽_qᵏ`.
The reduced claim holds with probability at most `⌊log_{q_min}(2TℓN²)⌋ / |P| + 2D / q_min`, where
`T = C(D + k, k)` and `ℓ = |ι₁| · |ι₂|`, under the lift, message and prime bounds of
`avg_card_claim_le`. -/
theorem prEvent_claim_le (πc : MvPolynomial (Fin k) ℤ →+* R)
    {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R}
    {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i) (hb : ∀ j, πc (b j) = v₂ j) {f : ι₁ × ι₂ → ℕ}
    (hf : ∀ p, f p ≤ 1) {μ : R} {μ' : MvPolynomial (Fin k) ℤ} (hμ : πc μ' = μ)
    (hfalse : ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : R) ≠ μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμD : μ'.totalDegree ≤ 2 * D)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤ (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2)
    {P : Finset ℕ} [SampleableType ↥P] (hP : ∀ q ∈ P, q.Prime) {qmin : ℕ} (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q) :
    Pr{let q ← $ᵗ ↥P; let α ← modPointSample hP q}[
      ∑ p : ι₁ × ι₂, reduceAt q.val α (a p.1) * reduceAt q.val α (b p.2) *
          (f p : ZMod q.val) = reduceAt q.val α μ'] ≤
      ENNReal.ofReal ((Nat.log qmin (2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2) : ℝ) /
        #P + ((2 * D : ℕ) : ℝ) / qmin) := by
  have key := prEvent_fingerprint_le (claimPoly_ne_zero πc ha hb f hμ hfalse)
    (totalDegree_claimPoly_le haD hbD hμD) (natAbs_coeff_claimPoly_le hf haD haN hbN hμN) hP hq2
    hqmin
  have heq : ∀ (q : ↥P) (α : Fin k → ZMod q.val),
      eval α (MvPolynomial.map (Int.castRingHom (ZMod q.val)) (claimPoly a b f μ')) = 0 ↔
        ∑ p : ι₁ × ι₂, reduceAt q.val α (a p.1) * reduceAt q.val α (b p.2) *
          (f p : ZMod q.val) = reduceAt q.val α μ' := fun q α => by
    rw [← reduceAt_apply, map_claimPoly, sub_eq_zero]
  simpa only [heq] using key

end Sampler

end BitZ
