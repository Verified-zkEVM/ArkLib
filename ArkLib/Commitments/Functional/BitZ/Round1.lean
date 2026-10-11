/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Data.MvPolynomial.CoeffBound
public import ArkLib.Data.MvPolynomial.PrimeFingerprint
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# BitZ: soundness of Round 1 of Construction 4.4

Round 1 of [BGKLSW26, Construction 4.4] replaces a claim `⟨π(f), v⟩ = µ` in a finitely generated
ring `R` by a claim over a small prime field `𝔽_q`. With the canonical map
`π_canon : ℤ[X₁, …, X_k] → R` and a section `π_canon⁻¹` (the *lift*), the prover sends an integer
polynomial `µ'` with `⟨π_canon⁻¹(v⁽¹⁾) ⊗ π_canon⁻¹(v⁽²⁾), f⟩ = µ'`, the verifier checks bounds on
`µ'` and `π_canon(µ') = µ`, and a random prime `q` and a random point `α ∈ 𝔽_qᵏ` reduce the
polynomial identity to `𝔽_q`.

This file formalizes the first half of the proof of [BGKLSW26, Theorem 4.7], the error `κ₀`:
for a witness `f` of bits that does *not* satisfy the original claim, the difference
`h := ⟨π_canon⁻¹(v⁽¹⁾) ⊗ π_canon⁻¹(v⁽²⁾), f⟩ - µ'` is a nonzero polynomial of total degree `≤ 2D`
and `‖h‖∞ ≤ 2 · T · ℓ · N_R²`, so by fingerprinting (Lemma 4.3) the reduced claim holds with
probability at most `κ₀ = log_{q_min} M / |P| + 2D / q_min`.

* `BitZ.claimPoly` is the polynomial `h`;
* `BitZ.totalDegree_claimPoly_le` and `BitZ.natAbs_coeff_claimPoly_le` bound its degree and norm;
* `BitZ.claimPoly_ne_zero` shows `h ≠ 0` when the claim over `R` is false;
* `BitZ.avg_card_claim_le` is [BGKLSW26, Lemma 4.3] applied to `h`: the probability, over a
  uniform prime `q ∈ P` and a uniform `α ∈ 𝔽_qᵏ`, that the reduced claim (43) holds is at most
  `κ₀`.

## References

* [BGKLSW26] R. Bloemen, A. Garreta, M. Kostrzewa, S. Londhe, L. Soukhanov, J. Wu.
  *BitZ: proofs and commitments in arbitrary rings through binary fields*. ePrint 2026/2141.
-/

@[expose] public section

open Finset MvPolynomial

namespace BitZ

variable {k : ℕ} {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The polynomial `h = ⟨a ⊗ b, f⟩ - µ'` of the proof of [BGKLSW26, Theorem 4.7], for lifts `a`
and `b` of the two tensor factors of the weight vector, a vector `f` of bits and the prover's
polynomial `µ'`. -/
noncomputable def claimPoly (a : ι₁ → MvPolynomial (Fin k) ℤ) (b : ι₂ → MvPolynomial (Fin k) ℤ)
    (f : ι₁ × ι₂ → ℕ) (μ' : MvPolynomial (Fin k) ℤ) : MvPolynomial (Fin k) ℤ :=
  ∑ p : ι₁ × ι₂, a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ) - μ'

/-- A ring homomorphism out of `ℤ[X₁, …, X_k]` carries `h` to `⟨φ(a) ⊗ φ(b), f⟩ - φ(µ')`. -/
theorem map_claimPoly {K : Type*} [CommRing K] (φ : MvPolynomial (Fin k) ℤ →+* K)
    (a : ι₁ → MvPolynomial (Fin k) ℤ) (b : ι₂ → MvPolynomial (Fin k) ℤ) (f : ι₁ × ι₂ → ℕ)
    (μ' : MvPolynomial (Fin k) ℤ) :
    φ (claimPoly a b f μ') = ∑ p : ι₁ × ι₂, φ (a p.1) * φ (b p.2) * (f p : K) - φ μ' := by
  simp [claimPoly, map_sum]

/-- The total degree of `h` is at most `2D` when the lifts and `µ'` have total degree `≤ D`,
`≤ D` and `≤ 2D` respectively. -/
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

/-- **The norm of `h`.** If the lifts `a i`, `b j` have total degree `≤ D` and coefficients bounded
by `N`, `f` is a vector of bits and `µ'` has coefficients bounded by `T · ℓ · N²`, where
`T = C(D + k, k)` and `ℓ = |ι₁| · |ι₂|`, then the coefficients of `h` are bounded by
`2 · T · ℓ · N²` ([BGKLSW26, §4.3]). -/
theorem natAbs_coeff_claimPoly_le {a : ι₁ → MvPolynomial (Fin k) ℤ}
    {b : ι₂ → MvPolynomial (Fin k) ℤ} {f : ι₁ × ι₂ → ℕ} {μ' : MvPolynomial (Fin k) ℤ} {D N : ℕ}
    (hf : ∀ p, f p ≤ 1) (ha : ∀ i, (a i).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤ (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2)
    (s : Fin k →₀ ℕ) :
    ((claimPoly a b f μ').coeff s).natAbs ≤
      2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2 := by
  classical
  have hterm : ∀ p : ι₁ × ι₂,
      ((a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ)).coeff s).natAbs ≤
        (D + k).choose k * N ^ 2 := by
    intro p
    rw [mul_comm, ← map_natCast (C : ℤ →+* MvPolynomial (Fin k) ℤ), coeff_C_mul, Int.natAbs_mul]
    have h1 := natAbs_coeff_mul_le (ha p.1) (haN p.1) (hbN p.2) s
    have h2 : (f p : ℤ).natAbs ≤ 1 := by simpa using hf p
    calc (f p : ℤ).natAbs * ((a p.1 * b p.2).coeff s).natAbs
        ≤ 1 * ((D + k).choose k * (N * N)) := Nat.mul_le_mul h2 h1
      _ = (D + k).choose k * N ^ 2 := by ring
  have hsum : (∑ p : ι₁ × ι₂, a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ)).coeff s =
      ∑ p : ι₁ × ι₂, (a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ)).coeff s := coeff_sum _ _ _
  have hle : ((∑ p : ι₁ × ι₂, a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ)).coeff s).natAbs ≤
      (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2 := by
    rw [hsum]
    have : ((∑ p : ι₁ × ι₂, (a p.1 * b p.2 * (f p : MvPolynomial (Fin k) ℤ)).coeff s) :
        ℤ).natAbs ≤ ∑ p : ι₁ × ι₂, ((a p.1 * b p.2 *
          (f p : MvPolynomial (Fin k) ℤ)).coeff s).natAbs := by
      refine Finset.induction_on (Finset.univ : Finset (ι₁ × ι₂)) (by simp) fun x t hx ih => ?_
      rw [sum_insert hx, sum_insert hx]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
    refine this.trans ((sum_le_sum fun p _ => hterm p).trans ?_)
    rw [sum_const, card_univ, smul_eq_mul]
    exact le_of_eq (by ring)
  unfold claimPoly
  rw [coeff_sub]
  refine (Int.natAbs_sub_le _ _).trans ?_
  have := hμN s
  calc _ ≤ _ + _ := Nat.add_le_add hle this
    _ = _ := by ring

section Nonvanishing

variable {R : Type*} [CommRing R]

/-- **A false claim gives a nonzero polynomial.** Let `π_canon : ℤ[X₁, …, X_k] → R` be a ring
homomorphism, let `a`, `b` be lifts of `v₁`, `v₂` along `π_canon`, and `π_canon(µ') = µ`. If
`⟨v₁ ⊗ v₂, f⟩ ≠ µ` in `R`, then `h = ⟨a ⊗ b, f⟩ - µ'` is nonzero, since `π_canon(h)` is the
difference `⟨v₁ ⊗ v₂, f⟩ - µ` ([BGKLSW26, proof of Theorem 4.7, below (44)]). -/
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

/-- Reduction modulo `q` followed by evaluation at `α ∈ 𝔽_qᵏ`: the maps `π_rand` of
[BGKLSW26, Lemma 4.3]. -/
noncomputable def reduceAt (q : ℕ) (α : Fin k → ZMod q) : MvPolynomial (Fin k) ℤ →+* ZMod q :=
  (eval α).comp (map (Int.castRingHom (ZMod q)))

@[simp]
theorem reduceAt_apply (q : ℕ) (α : Fin k → ZMod q) (h : MvPolynomial (Fin k) ℤ) :
    reduceAt q α h = eval α (map (Int.castRingHom (ZMod q)) h) := rfl

/-- The points `α ∈ 𝔽_qᵏ` at which the reduced claim (43) of [BGKLSW26],
`⟨π_rand(a) ⊗ π_rand(b), π_q(f)⟩ = π_rand(µ')`, holds are exactly the zeros of `h mod q`. -/
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

/-- **[BGKLSW26, Lemma 4.3] applied to the error polynomial of Theorem 4.7.**

Let `π_canon : ℤ[X₁, …, X_k] → R` be a ring homomorphism with lifts `a`, `b` of the tensor factors
`v₁`, `v₂` of the weight vector, of total degree `≤ D` and coefficients bounded by `N`. Let `f` be a
vector of bits and let `µ'` be a polynomial of total degree `≤ 2D` with coefficients bounded by
`T · ℓ · N²`, where `T = C(D + k, k)` and `ℓ = |ι₁| · |ι₂|`, such that `π_canon(µ') = µ`. If the
claim `⟨v₁ ⊗ v₂, f⟩ = µ` is false in `R`, then for a nonempty set `P` of primes `≥ q_min ≥ 2`, the
probability over a uniform prime `q ∈ P` and a uniform point `α ∈ 𝔽_qᵏ` that the reduced claim
`⟨π_rand(a) ⊗ π_rand(b), π_q(f)⟩ = π_rand(µ')` holds is at most
`log_{q_min} (2 · T · ℓ · N²) / |P| + 2 · D / q_min`. -/
theorem avg_card_claim_le (πc : MvPolynomial (Fin k) ℤ →+* R)
    {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R}
    {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i) (hb : ∀ j, πc (b j) = v₂ j) {f : ι₁ × ι₂ → ℕ}
    (hf : ∀ p, f p ≤ 1) {μ : R} {μ' : MvPolynomial (Fin k) ℤ} (hμ : πc μ' = μ)
    (hfalse : ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : R) ≠ μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμD : μ'.totalDegree ≤ 2 * D)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤ (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2)
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) (hPne : P.Nonempty) {qmin : ℕ} (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q) :
    (∑ q ∈ P, (Nat.card {α : Fin k → ZMod q //
        ∑ p : ι₁ × ι₂, reduceAt q α (a p.1) * reduceAt q α (b p.2) * (f p : ZMod q) =
          reduceAt q α μ'} : ℝ) / (q : ℝ) ^ k) / #P ≤
      (Nat.log qmin (2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2) : ℝ) / #P +
        ((2 * D : ℕ) : ℝ) / qmin := by
  have key := avg_zeroCountMod_div_le (claimPoly_ne_zero πc ha hb f hμ hfalse)
    (totalDegree_claimPoly_le haD hbD hμD)
    (natAbs_coeff_claimPoly_le hf haD haN hbN hμN) hP hPne hq2 hqmin
  simpa only [zeroCountMod_claimPoly] using key

/-- The same bound in the form of [BGKLSW26, Lemma 4.3]:
`2D / q_min + log₂ (2 · T · ℓ · N²) / (⌊log₂ q_min⌋ · |P|)`. -/
theorem avg_card_claim_le_logb (πc : MvPolynomial (Fin k) ℤ →+* R)
    {a : ι₁ → MvPolynomial (Fin k) ℤ} {b : ι₂ → MvPolynomial (Fin k) ℤ} {v₁ : ι₁ → R}
    {v₂ : ι₂ → R} (ha : ∀ i, πc (a i) = v₁ i) (hb : ∀ j, πc (b j) = v₂ j) {f : ι₁ × ι₂ → ℕ}
    (hf : ∀ p, f p ≤ 1) {μ : R} {μ' : MvPolynomial (Fin k) ℤ} (hμ : πc μ' = μ)
    (hfalse : ∑ p : ι₁ × ι₂, v₁ p.1 * v₂ p.2 * (f p : R) ≠ μ) {D N : ℕ}
    (haD : ∀ i, (a i).totalDegree ≤ D) (hbD : ∀ j, (b j).totalDegree ≤ D)
    (haN : ∀ i s, ((a i).coeff s).natAbs ≤ N) (hbN : ∀ j s, ((b j).coeff s).natAbs ≤ N)
    (hμD : μ'.totalDegree ≤ 2 * D)
    (hμN : ∀ s, (μ'.coeff s).natAbs ≤ (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2)
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) (hPne : P.Nonempty) {qmin : ℕ} (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q) :
    (∑ q ∈ P, (Nat.card {α : Fin k → ZMod q //
        ∑ p : ι₁ × ι₂, reduceAt q α (a p.1) * reduceAt q α (b p.2) * (f p : ZMod q) =
          reduceAt q α μ'} : ℝ) / (q : ℝ) ^ k) / #P ≤
      Real.logb 2 ((2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2 : ℕ) : ℝ) /
          (Nat.log 2 qmin * #P) + ((2 * D : ℕ) : ℝ) / qmin := by
  have hne := claimPoly_ne_zero πc ha hb f hμ hfalse
  have hM := natAbs_coeff_claimPoly_le hf haD haN hbN hμN
  obtain ⟨s, hs⟩ := ne_zero_iff.1 hne
  have hM1 : 1 ≤ 2 * (D + k).choose k * Fintype.card (ι₁ × ι₂) * N ^ 2 :=
    (Int.natAbs_pos.2 hs).trans_le (hM s)
  have key := avg_zeroCountMod_div_le_logb hne (totalDegree_claimPoly_le haD hbD hμD) hM hM1 hP
    hPne hq2 hqmin
  simpa only [zeroCountMod_claimPoly] using key

end Fingerprint

end BitZ
