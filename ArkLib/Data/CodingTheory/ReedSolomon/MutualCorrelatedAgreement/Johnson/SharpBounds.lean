/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equations.SharpEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Ordinary.JohnsonCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
/-!
# Sharp finite Johnson correlated agreement

The literal Johnson interpolation recipe constructs the ordinary equation. Under the additional
finite guard `johnsonMu n D eta ≤ D`, the sharp arbitrary-equation transfer gives the printed
`ESharp` exceptional bound. Uniform finite-field challenge sampling then divides this raw bound
by the field cardinality, retaining the trivial cap of one.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

noncomputable section

open Classical in
/-- Characteristic-free finite Johnson correlated agreement with the literal sharp charge.
The primitive equation and every factorwise Frobenius choice are constructed internally. -/
theorem exists_exceptional_johnsonMCA_sharp
    {F : Type*} [Field F] {n D A : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n)
    (hmuD : johnsonMu n D eta ≤ D) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ johnsonESharp n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i => f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  classical
  obtain ⟨cert⟩ := exists_johnson_symbolic_certificate hD hDn heta ha hthreshold hAn
    (k := D + 1) le_rfl domain f g
  have hQ : cert.Q ≠ 0 := by
    intro hz
    have hspec := (cert.specialization_sound (RingHom.id F) 0).1
    apply hspec
    rw [hz, map_zero]
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_exceptional_ordinaryEquation_sharp_base domain f g cert.Q D
      (johnsonH n D eta) (johnsonMu n D eta) A hQ (by omega)
      (johnsonMu_pos hD hDn) hmuD
      (johnson_degree_succ_le_agreement hD hDn heta hthreshold)
      hAn cert.challengeDegree_le cert.jetDegree_le
  have hcardReal : (ex.card : ℝ) ≤
      (ordinaryFactorSharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
          (johnsonMu n D eta) (johnsonH n D eta) : ℝ) := by
    exact_mod_cast hcard
  refine ⟨ex, ?_, ?_⟩
  · have hmu : 1 ≤ johnsonMu n D eta := johnsonMu_pos hD hDn
    have htwoD : 1 ≤ 2 * D := by omega
    have htwoMu : 1 ≤ 2 * johnsonMu n D eta := by omega
    simp only [ordinaryFactorSharpRaw, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Nat.cast_add, Nat.cast_mul] at hcardReal
    rw [Nat.cast_sub htwoD, Nat.cast_sub htwoMu] at hcardReal
    unfold johnsonESharp johnsonTheta
    dsimp only
    rw [Nat.cast_sub htwoMu]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hcardReal
  · intro z hz P hdegree hagree
    apply hgood z hz P hdegree _ hagree
    have hsound := (cert.specialization_sound (RingHom.id F) z).2
      (polynomialAgreementSet domain (fun i => f i + z * g i) P) P hdegree hagree
      (fun i hi => (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id F) z =
        (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    simpa only [heval, challengeSpecialization] using hsound

open Classical in
/-- The sharp Johnson exceptional bound controls the canonical affine-line MCA failure
probability over every finite field. -/
theorem johnson_mcaError_le_sharp
    {F : Type} [Field F] [Fintype F] {n D : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hmuD : johnsonMu n D eta ≤ D) :
    mcaError (AffineLineGenerator F) (code domain (D + 1))
        (1 - johnsonAgreement n D eta) ≤
      min 1 (ENNReal.ofReal
        (johnsonESharp n D ⌈johnsonAgreement n D eta * n⌉₊ eta /
          (Fintype.card F : ℝ))) := by
  classical
  let A := ⌈johnsonAgreement n D eta * n⌉₊
  have hAn : A ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])
  have hthreshold : johnsonAgreement n D eta * n ≤ A := Nat.le_ceil _
  have hline : LineExactAgreementBound domain (D + 1) A (johnsonESharp n D A eta) := by
    intro f g
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_johnsonMCA_sharp
      domain f g hD hDn heta ha hthreshold hAn hmuD
    refine ⟨ex, hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP hagree
    refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · simpa [mappedDomain] using hset
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  have heq : (n : ℝ) * (1 - (1 - johnsonAgreement n D eta)) =
      johnsonAgreement n D eta * n := by ring
  rw [heq]

end

end ReedSolomon
