/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.JohnsonCurveCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equation
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode
/-!
# Exact Johnson agreement for polynomial curves

A single exceptional set controls every low-degree candidate on a polynomial received curve,
in every characteristic. The scaled primitive Johnson certificate supplies the ordinary equation;
the ordinary factor bound charges at most twice the curve degree times the line exception count.
The constant curve has no exceptional challenges.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

private theorem ordinaryFactorRaw_double_height_le (theta : ℚ) (n D B H : ℕ)
    (htheta : 0 ≤ theta) :
    ordinaryFactorRaw theta n D B (2 * H) ≤ 2 * ordinaryFactorRaw theta n D B H := by
  unfold ordinaryFactorRaw
  push_cast
  have htail : 0 ≤ theta * B + ((n - D - 1 : ℕ) : ℚ) * B := by positivity
  nlinarith only [htail]

open Classical in
/-- Outside one exceptional set of at most `2ℓ` times the finite Johnson count, every
sufficiently agreeing candidate has exact power agreement with the coefficient words. -/
theorem exists_johnson_curve_exactPowerAgreement
    {F : Type*} [Field F] {n D A ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 2 * ℓ * johnsonExceptionCount n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · obtain ⟨ex, hcard, hgood⟩ := uniformExactPowerAgreement_singleton domain values (D + 1) A
    exact ⟨ex, by simpa using (show (ex.card : ℝ) ≤ 0 by exact_mod_cast hcard), hgood⟩
  let H := curveInterpolationHeight ℓ (johnsonH n D eta)
  let B := johnsonMu n D eta
  let theta : ℚ := ((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)
  have hDlt : D < n := by omega
  have hDA := johnson_degree_succ_le_agreement hD hDlt heta hthreshold
  have hB : 0 < B := johnsonMu_pos hD hDlt
  obtain ⟨cert⟩ := exists_johnson_curve_symbolic_certificate hD hDn heta hthreshold
    (k := D + 1) le_rfl hℓ domain
    (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun i ↦ powerBatchedCoordinate_natDegree_le _)
  obtain ⟨ex, hcard, hgood⟩ := exists_baseExceptional_ordinaryPowerEquation domain values
    cert.Q D H B (D + 1) A cert.nonzero (by omega) hℓ (by omega) hDA
    cert.challengeDegree_le ((jetDegree_le_total cert.Q 0).trans cert.jetTotalDegree_le)
  rw [ordinaryUnifiedPowerFactorAtOrHeight_of_pos n D ℓ B H A (D + 1) hB,
    ordinaryUnifiedPowerFactorAt_succ_eq n D ℓ B H A hDA hAn] at hcard
  have hh : H ≤ ℓ * (2 * johnsonH n D eta) := by
    have hhpos : 0 < johnsonH n D eta :=
      hB.trans_le (johnsonMu_le_H hD hDlt)
    exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left ℓ (by omega))
  have hbound : (ex.card : ℚ) ≤
      (2 * ℓ : ℕ) * ordinaryFactorRaw theta n D B (johnsonH n D eta) := by
    calc
      _ ≤ ordinaryUnifiedPowerFactorRaw theta n D ℓ B H := hcard
      _ ≤ ordinaryCurveFactorRaw theta n D ℓ B H :=
        ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw n ℓ B H (by positivity) hD
      _ ≤ ℓ * ordinaryFactorRaw theta n D B (2 * johnsonH n D eta) :=
        ordinaryCurveFactorRaw_le_line_mul theta n D ℓ B H _ (by positivity) hh
      _ ≤ ℓ * (2 * ordinaryFactorRaw theta n D B (johnsonH n D eta)) :=
        mul_le_mul_of_nonneg_left (ordinaryFactorRaw_double_height_le theta n D B _
          (by positivity)) (by positivity)
      _ = _ := by push_cast; ring
  have hcardReal : (ex.card : ℝ) ≤ (2 * ℓ : ℕ) *
      (ordinaryFactorRaw theta n D B (johnsonH n D eta) : ℝ) := by exact_mod_cast hbound
  refine ⟨ex, ?_, ?_⟩
  · simpa only [ordinaryFactorRaw, johnsonExceptionCount, johnsonTheta, theta, B,
      Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcardReal
  · intro z hz P hP hA
    apply hgood z hz P hP _ hA
    have hsound := (cert.specialization_sound (RingHom.id F) z).2.2
      (polynomialAgreementSet domain (powerBatchedWord values z) P) P hP hA
      (fun i hi ↦ by
        simpa only [RingHom.id_apply, eval₂_powerBatchedCoordinate_eq_powerBatchedWord]
          using (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id F) z = (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    simpa only [heval, challengeSpecialization] using hsound

end ReedSolomon
