/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Nam Khanh Ngo
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.JohnsonCurveCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equation
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode
/-!
# Exact Johnson agreement for polynomial curves

A single exceptional set controls every low-degree candidate on a polynomial received curve,
in every characteristic. The scaled primitive Johnson certificate supplies the ordinary equation.
The curve height `ℓ (h + 1) - 1` is at most `ℓ (h + 1)`, so the ordinary factor bound charges at
most the curve degree times the line exception count at height `h + 1`
(`exists_johnson_curve_exactPowerAgreement_succHeight`). That count is at most twice the line
count (`exists_johnson_curve_exactPowerAgreement`) and below the closed bound `(8/3) n t³ / ρ₋`
(`exists_johnson_curve_exactPowerAgreement_closed`). The constant curve has no exceptional
challenges.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative

private theorem ordinaryFactorRaw_johnsonH_succ_eq (n D A : ℕ) (eta : ℝ) :
    ((ordinaryFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D (johnsonMu n D eta)
        (johnsonH n D eta + 1) : ℚ) : ℝ) = johnsonSuccExceptionCount n D A eta := by
  unfold ordinaryFactorRaw johnsonSuccExceptionCount johnsonTheta
  push_cast
  ring

open Classical in
/-- Outside one exceptional set of at most `ℓ` times the Johnson count at height `h + 1`, every
sufficiently agreeing candidate has exact power agreement with the coefficient words. -/
theorem exists_johnson_curve_exactPowerAgreement_succHeight
    {F : Type*} [Field F] {n D A ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ ℓ * johnsonSuccExceptionCount n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  by_cases hAn : A ≤ n
  swap
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      unfold johnsonSuccExceptionCount johnsonTheta
      positivity
    · intro z hz P hP hagree
      have hcard := Finset.card_le_univ
        (polynomialAgreementSet domain (powerBatchedWord values z) P)
      simp only [Fintype.card_fin] at hcard
      omega
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · obtain ⟨ex, hcard, hgood⟩ := uniformExactPowerAgreement_singleton domain values (D + 1) A
    exact ⟨ex, by simpa using (show (ex.card : ℝ) ≤ 0 by exact_mod_cast hcard), hgood⟩
  let H := curveInterpolationHeight ℓ (johnsonH n D eta)
  let B := johnsonMu n D eta
  let theta : ℚ := ((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)
  have hDlt : D < n := by omega
  have hDA := johnson_degree_succ_le_agreement hDlt heta hthreshold
  have hB : 0 < B := johnsonMu_pos hD hDlt
  obtain ⟨cert⟩ := exists_johnson_curve_symbolic_certificate hD hDn heta hthreshold
    (k := D + 1) le_rfl hℓ domain
    (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun i ↦ powerBatchedCoordinate_natDegree_le _)
  obtain ⟨ex, hcard, hgood⟩ := exists_baseExceptional_ordinaryPowerEquation domain values
    cert.Q D H B (D + 1) A cert.nonzero (by omega) (by omega) hDA
    cert.challengeDegree_le ((jetDegree_le_total cert.Q 0).trans cert.jetTotalDegree_le)
  rw [ordinaryUnifiedPowerFactorAtOrHeight_of_pos n D ℓ B H A (D + 1) hB,
    ordinaryUnifiedPowerFactorAt_succ_eq n D ℓ B H A hDA hAn] at hcard
  have hh : H ≤ ℓ * (johnsonH n D eta + 1) := Nat.sub_le _ _
  have hbound : (ex.card : ℚ) ≤ ℓ * ordinaryFactorRaw theta n D B (johnsonH n D eta + 1) := by
    calc
      _ ≤ ordinaryUnifiedPowerFactorRaw theta n D ℓ B H := hcard
      _ ≤ ordinaryCurveFactorRaw theta n D ℓ B H :=
        ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw n ℓ B H (by positivity) hD
      _ ≤ ℓ * ordinaryFactorRaw theta n D B (johnsonH n D eta + 1) :=
        ordinaryCurveFactorRaw_le_line_mul theta n D ℓ B H _ (by positivity) hh
  have hcardReal : (ex.card : ℝ) ≤
      (ℓ : ℝ) * (ordinaryFactorRaw theta n D B (johnsonH n D eta + 1) : ℝ) := by
    exact_mod_cast hbound
  refine ⟨ex, ?_, ?_⟩
  · rwa [← ordinaryFactorRaw_johnsonH_succ_eq]
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

open Classical in
/-- Outside one exceptional set of at most `2ℓ` times the finite Johnson count, every
sufficiently agreeing candidate has exact power agreement with the coefficient words. -/
theorem exists_johnson_curve_exactPowerAgreement
    {F : Type*} [Field F] {n D A ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 2 * ℓ * johnsonExceptionCount n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_johnson_curve_exactPowerAgreement_succHeight domain values hD hDn heta hthreshold
  refine ⟨ex, hcard.trans ?_, hgood⟩
  exact mul_le_mul_of_nonneg_left (johnsonSuccExceptionCount_le_two_mul hD (by omega))
    (Nat.cast_nonneg ℓ) |>.trans_eq (by ring)

open Classical in
/-- Outside one exceptional set of at most `ℓ (8/3) n t³ / ρ₋` challenges, every sufficiently
agreeing candidate has exact power agreement with the coefficient words. This is the line bound
of `johnsonExceptionCount_lt_closed` charged once per unit of curve degree. -/
theorem exists_johnson_curve_exactPowerAgreement_closed
    {F : Type*} [Field F] {n D A ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        ℓ * ((8 / 3 : ℝ) * n * johnsonT n D eta ^ 3 / johnsonRhoMinus n D) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_johnson_curve_exactPowerAgreement_succHeight domain values hD hDn heta hthreshold
  exact ⟨ex, hcard.trans (mul_le_mul_of_nonneg_left
    (johnsonSuccExceptionCount_lt_closed hD hDn heta hthreshold).le (Nat.cast_nonneg ℓ)), hgood⟩

end ReedSolomon
