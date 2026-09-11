/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Certificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Index
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.UnifiedCurve
/-! # Johnson correlated agreement for polynomial challenge curves -/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative
open CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

/-- The exact finite ordinary Johnson charge for a degree-`ℓ` challenge curve. -/
noncomputable def johnsonPowerE0 (n D A ℓ : ℕ) (eta : ℝ) : ℝ :=
  (ordinaryUnifiedPowerFactorRaw
    (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ
      (johnsonMu n D eta) (johnsonPowerHeight ℓ (johnsonH n D eta)) : ℚ)

/-- The unified polynomial-curve charge is at most `ℓ` copies of its degree-one charge whenever
its coefficient height is at most `ℓ` times the line height. -/
theorem ordinaryUnifiedPowerFactorRaw_le_mul_lineCharge
    (theta : ℚ) (n D ℓ B h H : ℕ)
    (htheta : 0 ≤ theta) (hh : h ≤ ℓ * H) :
    ordinaryUnifiedPowerFactorRaw theta n D ℓ B h ≤
      ℓ * ordinaryUnifiedPowerFactorRaw theta n D 1 B H := by
  have hfirst : (2 * B - 1) * h ≤ (2 * B - 1) * (ℓ * H) :=
    Nat.mul_le_mul_left _ hh
  have hmixed : ℓ * B + h * ordinaryPsi D B ≤
      ℓ * (B + H * ordinaryPsi D B) := by
    calc
      ℓ * B + h * ordinaryPsi D B ≤ ℓ * B + (ℓ * H) * ordinaryPsi D B := by
        gcongr
      _ = ℓ * (B + H * ordinaryPsi D B) := by ring
  have hrhs : ℓ * ordinaryUnifiedPowerFactorRaw theta n D 1 B H =
      (((2 * B - 1) * (ℓ * H) : ℕ) : ℚ) +
        theta * ((ℓ * (B + H * ordinaryPsi D B) : ℕ) : ℚ) +
        ((ℓ * ((n - D - 1) * B) : ℕ) : ℚ) := by
    unfold ordinaryUnifiedPowerFactorRaw
    push_cast
    ring
  rw [hrhs]
  unfold ordinaryUnifiedPowerFactorRaw
  exact add_le_add
    (add_le_add (by exact_mod_cast hfirst)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hmixed) htheta)) le_rfl

/-- The exact finite curve charge is linear in the curve degree, against the ordinary line
charge with the one-slot height allowance used by the scaled interpolation certificate. -/
theorem johnsonPowerE0_le_mul_lineCharge (n D A ℓ : ℕ) (eta : ℝ) :
    johnsonPowerE0 n D A ℓ eta ≤
      (ℓ : ℝ) *
        (ordinaryUnifiedPowerFactorRaw
          (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
            1 (johnsonMu n D eta) (johnsonH n D eta + 1) : ℚ) := by
  unfold johnsonPowerE0
  norm_cast
  exact ordinaryUnifiedPowerFactorRaw_le_mul_lineCharge
    (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ
      (johnsonMu n D eta) (johnsonPowerHeight ℓ (johnsonH n D eta))
      (johnsonH n D eta + 1) (by positivity)
      (johnsonPowerHeight_le ℓ (johnsonH n D eta))

/-- In the Johnson parameter range, the unified degree-one charge is bounded by the former
ordinary line charge.  This keeps the old line-envelope comparison available to downstream
asymptotic estimates without using it in the recovery theorem. -/
theorem johnsonPowerE0_le_mul_legacyLineCharge
    {n D A ℓ : ℕ} {eta : ℝ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    johnsonPowerE0 n D A ℓ eta ≤
      (ℓ : ℝ) *
        (ordinaryFactorRaw
          (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
            (johnsonMu n D eta) (johnsonH n D eta + 1) : ℚ) := by
  let theta : ℚ := ((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)
  let B := johnsonMu n D eta
  let H := johnsonH n D eta + 1
  have hB : 1 ≤ B := johnsonMu_pos hD hDn
  have hpsi : ordinaryPsi D B ≤ 4 * D * B := ordinaryPsi_le_four_mul hD hB
  have hline : ordinaryUnifiedPowerFactorRaw theta n D 1 B H ≤
      ordinaryFactorRaw theta n D B H := by
    unfold ordinaryUnifiedPowerFactorRaw ordinaryFactorRaw
    have htheta : 0 ≤ theta := by positivity
    have hmixed : B + H * ordinaryPsi D B ≤ H + B + 4 * D * B * H := by
      nlinarith [Nat.zero_le H]
    exact add_le_add
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (by
          exact_mod_cast (show 1 * B + H * ordinaryPsi D B ≤
            H + B + 4 * D * B * H by simpa using hmixed)) htheta)) (by simp)
  exact (johnsonPowerE0_le_mul_lineCharge n D A ℓ eta).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hline) (Nat.cast_nonneg ℓ))

open Classical in
/-- Characteristic-free finite Johnson recovery for a polynomial received curve. The exceptional
set precedes the challenge and every candidate, and the conclusion gives full exact agreement. -/
theorem exists_exceptional_johnsonPowerMCA
    {F : Type*} [Field F] {n D A ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n)
    (hℓ : 0 < ℓ) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ johnsonPowerE0 n D A ℓ eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  obtain ⟨cert⟩ := exists_johnsonPower_symbolic_certificate hD hDn heta ha
    hthreshold hAn (k := D + 1) le_rfl hℓ domain values
  have hQ : cert.Q ≠ 0 := by
    intro hz
    have hspec := (cert.specialization_sound (RingHom.id F) 0).1
    apply hspec
    rw [hz, map_zero]
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryPowerEquation_base_unified
    domain values cert.Q D (johnsonPowerHeight ℓ (johnsonH n D eta))
      (johnsonMu n D eta) A hQ (by omega) hℓ
      (johnsonMu_pos hD hDn)
      (johnson_degree_succ_le_agreement hD hDn heta hthreshold)
      hAn cert.challengeDegree_le cert.jetDegree_le
  have hcardReal : (ex.card : ℝ) ≤
      (ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ
          (johnsonMu n D eta) (johnsonPowerHeight ℓ (johnsonH n D eta)) : ℚ) := by
    exact_mod_cast hcard
  refine ⟨ex, ?_, ?_⟩
  · exact hcardReal
  · intro z hz P hdegree hagree
    apply hgood z hz P hdegree _ hagree
    have hsound := (cert.specialization_sound (RingHom.id F) z).2
      (polynomialAgreementSet domain (powerBatchedWord values z) P) P hdegree hagree
      (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id F) z =
        (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    simpa only [heval, challengeSpecialization] using hsound

open Classical in
/-- The finite Johnson curve theorem as a uniform exact-power certificate at the rounded
agreement threshold. -/
theorem johnsonPower_uniformExactAgreement_at_ceil
    {F : Type*} [Field F] {n D ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1) (hℓ : 0 < ℓ) :
    UniformExactPowerAgreement domain values (D + 1)
      ⌈johnsonAgreement n D eta * n⌉₊
      ⌈johnsonPowerE0 n D ⌈johnsonAgreement n D eta * n⌉₊ ℓ eta⌉₊ := by
  let A := ⌈johnsonAgreement n D eta * n⌉₊
  have hAn : A ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_johnsonPowerMCA
    domain values hD hDn heta ha (Nat.le_ceil _) hAn hℓ
  refine ⟨ex, ?_, hgood⟩
  have hcard' : (ex.card : ℝ) ≤
      (⌈johnsonPowerE0 n D A ℓ eta⌉₊ : ℕ) := hcard.trans (Nat.le_ceil _)
  exact_mod_cast hcard'

open Classical in
/-- Every-subset Johnson recovery for polynomial curves on arbitrary finite coordinates. -/
theorem exists_exceptional_johnsonPowerMCA_arbitrary_index
    {ι : Type} [Fintype ι] {F : Type} [Field F]
    (domain : ι ↪ F) (ℓ D : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) (hℓ : 0 < ℓ)
    (U : Fin (ℓ + 1) → ι → F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        ⌈johnsonPowerE0 (Fintype.card ι) D
          ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ ℓ eta⌉₊ ∧
      ∀ z, z ∉ exceptional → ∀ T : Finset ι,
        (T.card : ℝ) ≥ Fintype.card ι *
          (1 - (1 - johnsonAgreement (Fintype.card ι) D eta)) →
        projectedWord (fun i ↦ ∑ t, z ^ t.val • U t i) T ∈
          projectedCodeSubmod (code domain (D + 1)) T →
        ∃ p : Fin (ℓ + 1) → code domain (D + 1),
          ∀ t i, i ∈ T → (p t).val i = U t i := by
  let n := Fintype.card ι
  let A := ⌈johnsonAgreement n D eta * n⌉₊
  apply exists_exceptional_powerMCA_arbitrary_index domain ℓ (D + 1) A
    ⌈johnsonPowerE0 n D A ℓ eta⌉₊ (1 - johnsonAgreement n D eta)
  · simp only [sub_sub_cancel]
    rw [show (Fintype.card ι : ℝ) * johnsonAgreement (Fintype.card ι) D eta =
        johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι by ring]
  · exact johnsonPower_uniformExactAgreement_at_ceil _ _ hD hDn heta ha hℓ

open Classical in
/-- Canonical finite-field MCA bound for the univariate-powers generator. -/
theorem johnsonPower_mcaError_le_arbitrary_index
    {ι : Type} [Fintype ι] {F : Type} [Field F] [Fintype F]
    (domain : ι ↪ F) (ℓ D : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) (hℓ : 0 < ℓ) :
    mcaError (univariatePowersGenerator F ℓ) (code domain (D + 1))
        (1 - johnsonAgreement (Fintype.card ι) D eta) ≤
      ENNReal.ofReal
        (⌈johnsonPowerE0 (Fintype.card ι) D
            ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ ℓ eta⌉₊ /
          (Fintype.card F : ℝ)) := by
  let n := Fintype.card ι
  let A := ⌈johnsonAgreement n D eta * n⌉₊
  apply power_mcaError_le_arbitrary_index domain ℓ (D + 1) A
    ⌈johnsonPowerE0 n D A ℓ eta⌉₊ (1 - johnsonAgreement n D eta)
  · simp only [sub_sub_cancel]
    rw [show (Fintype.card ι : ℝ) * johnsonAgreement (Fintype.card ι) D eta =
        johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι by ring]
  · intro U
    exact johnsonPower_uniformExactAgreement_at_ceil _ _ hD hDn heta ha hℓ

end ReedSolomon
