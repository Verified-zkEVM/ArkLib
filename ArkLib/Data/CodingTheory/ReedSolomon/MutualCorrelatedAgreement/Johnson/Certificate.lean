/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equations.BaseEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Ordinary.JohnsonCertificate
/-!
# Finite Johnson correlated agreement in every characteristic

The literal Johnson recipe constructs a primitive ordinary equation. Its roots include all
polynomials above the agreement threshold, and the all-characteristic ordinary transfer
produces one exceptional set with the finite `E0` charge.
-/

@[expose] public section

namespace ReedSolomon
open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

open Classical in
/-- Characteristic-free finite Johnson correlated agreement with the literal finite E0.
The exceptional set is chosen before every close polynomial, and agreement-set equality is exact. -/
theorem exists_exceptional_johnsonMCA
    {F : Type*} [Field F] {n D A : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ johnsonE0 n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  classical
  obtain ⟨cert⟩ := exists_johnson_symbolic_certificate hD hDn heta ha hthreshold hAn
    (k := D + 1) le_rfl domain f g
  have hQ : cert.Q ≠ 0 := by
    intro hz
    have hspec := (cert.specialization_sound (RingHom.id F) 0).1
    apply hspec
    rw [hz, map_zero]
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryEquation_base domain f g cert.Q D
    (johnsonH n D eta) (johnsonMu n D eta) A hQ (by omega)
    (johnsonMu_pos hD hDn) (johnson_degree_succ_le_agreement hD hDn heta hthreshold)
    hAn cert.challengeDegree_le cert.jetDegree_le
  have hcardReal : (ex.card : ℝ) ≤
      (ordinaryFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
        (johnsonMu n D eta) (johnsonH n D eta) : ℝ) := by exact_mod_cast hcard
  refine ⟨ex, ?_, ?_⟩
  · simpa only [ordinaryFactorRaw, johnsonE0, johnsonTheta, Rat.cast_add, Rat.cast_mul,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
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

end ReedSolomon
