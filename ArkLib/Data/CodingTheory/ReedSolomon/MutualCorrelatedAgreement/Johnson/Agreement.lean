/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.BaseEquation
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.JohnsonCertificate

/-!
# Exact Johnson correlated agreement in every characteristic

A message polynomial has degree at most `D`, so the code dimension is `D + 1`. The Johnson
agreement fraction is `a = √(D / n) + η` with slack `η > 0`. The finite Johnson interpolation
certificate is a nonzero ordinary equation whose roots include every candidate polynomial above the
agreement threshold. The exceptional-challenge bound for ordinary equations then gives one set of
at most `johnsonExceptionCount n D A η` challenges, fixed before the challenge and candidate,
outside which every close candidate `P` on the received line `f + z g` is `P₀ + z P₁` with
`Agr(f + z g, P) = Agr(f, P₀) ∩ Agr(g, P₁)`. The field may be infinite and have any
characteristic.

## Main statements

* `ReedSolomon.exists_johnson_line_exactCorrelatedPair`: the exceptional-set bound for an
  integer agreement threshold `A ≥ a n`.
* `ReedSolomon.exists_johnson_line_exactCorrelatedPair_ceil`: the same bound at the threshold
  `⌈a n⌉₊`.
* `ReedSolomon.exists_johnson_line_exactCorrelatedPair_of_gap`: when `4 (k - 1) ≤ δ² n` and the
  agreement exceeds `k + δ n`, fewer than `(343 / 3) n²` challenges are exceptional.

## References

* [BCHKS25]
* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

open Classical in
/-- **Johnson exact correlated agreement.** For distinct evaluation points and received words
`f g`, one set of at most `johnsonExceptionCount n D A η` challenges is chosen before the challenge
and candidate. Outside it, every polynomial of degree at most `D` agreeing with `f + z g` on at
least `A ≥ (√(D / n) + η) n` points has an exact correlated pair. -/
theorem exists_johnson_line_exactCorrelatedPair
    {F : Type*} [Field F] {n D A : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ johnsonExceptionCount n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  classical
  have hDlt : D < n := by omega
  obtain ⟨cert⟩ := exists_johnson_symbolic_certificate hD hDn heta hthreshold
    (k := D + 1) le_rfl domain f g
  have hQ : cert.Q ≠ 0 := by
    intro hz
    apply (cert.specialization_sound (RingHom.id F) 0).1
    rw [hz, map_zero]
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryEquation_base domain f g cert.Q D
    (johnsonH n D eta) (johnsonMu n D eta) A hQ (by omega)
    (johnsonMu_pos hD hDlt) (johnson_degree_succ_le_agreement hD hDlt heta hthreshold)
    hAn cert.challengeDegree_le cert.jetDegree_le
  have hcardReal : (ex.card : ℝ) ≤
      (ordinaryFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
        (johnsonMu n D eta) (johnsonH n D eta) : ℝ) := by exact_mod_cast hcard
  refine ⟨ex, ?_, ?_⟩
  · simpa only [ordinaryFactorRaw, johnsonExceptionCount, johnsonTheta, Rat.cast_add,
      Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat] using hcardReal
  · intro z hz P hdegree hagree
    apply hgood z hz P hdegree _ hagree
    have hsound := (cert.specialization_sound (RingHom.id F) z).2
      (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) P hdegree hagree
      (fun i hi => (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id F) z = (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    simpa only [heval, challengeSpecialization] using hsound

open Classical in
/-- **Johnson exact correlated agreement at the rounded threshold.** With
`a = √(D / n) + η ≤ 1`, the integer threshold `⌈a n⌉₊` admits one set of at most
`johnsonExceptionCount n D ⌈a n⌉₊ η` exceptional challenges. -/
theorem exists_johnson_line_exactCorrelatedPair_ceil
    {F : Type*} [Field F] {n D : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        johnsonExceptionCount n D ⌈johnsonAgreement n D eta * n⌉₊ eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        ⌈johnsonAgreement n D eta * n⌉₊ ≤
          (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P :=
  exists_johnson_line_exactCorrelatedPair domain f g hD hDn heta (Nat.le_ceil _)
    (Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)]))

open Classical in
/-- **Johnson exact correlated agreement from an agreement gap.** If `2 ≤ k`,
`4 (k - 1) ≤ δ² n` and `k + δ n ≤ A ≤ n`, then the Johnson multiplicity is three at slack `δ / 2`,
and one set of fewer than `(343 / 3) n²` challenges is exceptional for exact correlated agreement
of degree-`< k` candidates. -/
theorem exists_johnson_line_exactCorrelatedPair_of_gap
    {F : Type*} [Field F] {n k A : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (hδ : 0 < δ) (hk : 2 ≤ k)
    (hscale : 4 * ((k : ℝ) - 1) ≤ δ ^ 2 * n) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) < (343 / 3 : ℝ) * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  let D := k - 1
  let eta := δ / 2
  have hD : 1 ≤ D := by omega
  have hDk : D + 1 = k := by omega
  have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
  have hkPos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnPos : (0 : ℝ) < n := by
    have hkA : (k : ℝ) ≤ A := hgap.trans' (le_add_of_nonneg_right (by nlinarith))
    linarith
  have hklt : k < n := by
    have : (k : ℝ) < n := by nlinarith [mul_pos hδ hnPos]
    exact_mod_cast this
  have hDn : D ≤ n - 2 := by omega
  have heta : 0 < eta := by positivity
  have hDR : (D : ℝ) = k - 1 := by
    simp only [D, Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  have hrhoBound : johnsonRhoMinus n D ≤ (δ / 2) ^ 2 := by
    unfold johnsonRhoMinus
    apply (div_le_iff₀ hnPos).2
    nlinarith
  have hsqrt : √(johnsonRhoMinus n D) ≤ δ / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by simpa using hrhoBound⟩
  have hthreshold : johnsonAgreement n D eta * n ≤ A := by
    unfold johnsonAgreement
    dsimp only [eta]
    have hsqrtMul := mul_le_mul_of_nonneg_right hsqrt hnPos.le
    nlinarith
  have hM : johnsonM n D eta = 3 := by
    unfold johnsonM
    rw [max_eq_right]
    apply Nat.ceil_le.mpr
    have hratio : √(johnsonRhoMinus n D) / δ ≤ 1 / 2 := (div_le_iff₀ hδ).2 (by linarith)
    rw [show (2 : ℝ) * eta = δ by ring]
    exact hratio.trans (by norm_num)
  have hclosed := johnsonExceptionCount_lt_closed hD hDn heta hthreshold
  have hclosed' : johnsonExceptionCount n D A eta < (343 / 3 : ℝ) * (n : ℝ) ^ 2 := by
    unfold johnsonT at hclosed
    rw [hM] at hclosed
    norm_num at hclosed
    have hDPos : (0 : ℝ) < D := by exact_mod_cast hD
    have hscale' : (343 / 3 : ℝ) * (n : ℝ) ^ 2 / D ≤ (343 / 3 : ℝ) * (n : ℝ) ^ 2 := by
      apply (div_le_iff₀ hDPos).2
      have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hD
      nlinarith [sq_nonneg (n : ℝ)]
    apply hclosed.trans_le
    rw [show johnsonRhoMinus n D = (D : ℝ) / n by rfl]
    calc
      (8 / 3 : ℝ) * n * (343 / 8) / ((D : ℝ) / n) = (343 / 3 : ℝ) * n ^ 2 / D := by
        field_simp
      _ ≤ _ := hscale'
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_johnson_line_exactCorrelatedPair domain f g hD hDn heta hthreshold hAn
  refine ⟨exceptional, hcard.trans_lt hclosed', ?_⟩
  intro z hz P hdegree hagree
  have hdegree' : P.degree < (D : WithBot ℕ) + 1 := by
    rw [show (D : WithBot ℕ) + 1 = (k : WithBot ℕ) by norm_cast]
    exact hdegree
  simpa only [hDk] using hgood z hz P hdegree' hagree

end ReedSolomon
