/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.CertificateBound
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.PowerToLine
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.UniformRateCertificate
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Uniform exact correlated agreement with the three-halves exponent -/

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

/-- One exceptional set explains every close polynomial on the received polynomial curve. -/
theorem exists_uniformRatePartition_curveMCA {F E : Type u} [Field F] [Field E]
    [DecidableEq E] [IsAlgClosed E]
    {δ : ℝ} {n k A ℓ : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant δ
        (uniformRatePartitionJetBound δ) (150 * uniformRatePartitionJetBound δ)
        (uniformRatePartitionOrder δ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  obtain ⟨e⟩ := exists_uniformRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformRatePartitionOrder_ge_500 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformRatePartitionMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionClosedMultiplicity_ge_order hd)
  obtain ⟨hsize, hmn, hν, hνn⟩ := uniformRatePartition_integer_guards hδ hδone hm hn
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδone hd hn hAn domain
    (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun _ ↦ powerBatchedCoordinate_natDegree_le _)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast h
  have hchar' : ringChar F = 0 ∨
      max (e.ambientDegree + 1 - 1) (uniformRatePartitionJetBound δ) < ringChar F := by
    apply hchar.imp_right
    intro hc
    have hD := e.ambient_le
    exact (max_lt (by omega) hνn).trans_le hc
  exact exists_curveMCA_of_certificate_of_jetCharacteristic domain values iota cert hk e.message_le
    (by omega) (by have := e.order_le; omega) e.ambient_le hkA hAn hν
    (by positivity) hℓ le_rfl hδ hδone.le hgap hchar'

open Classical in
/-- The base-field uniform curve theorem includes the prime-field boundary `q = n`. -/
theorem exists_uniformRatePartition_baseCurveMCA {F : Type u} [Field F]
    {δ : ℝ} {n k A ℓ : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant δ
        (uniformRatePartitionJetBound δ) (150 * uniformRatePartitionJetBound δ)
        (uniformRatePartitionOrder δ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  obtain ⟨ex, hc, hg⟩ := exists_uniformRatePartition_curveMCA hδ hδsmall hn hk hgap hAn hℓ
    domain values iota hchar
  obtain ⟨ex', hc', hg'⟩ := exists_exceptional_powerAgreement_descend domain values iota k A ex hg
  exact ⟨ex', (Nat.cast_le.mpr hc').trans hc, hg'⟩

open Classical in
/-- Exact line MCA for the uniform parameters, with the actual message-rate gap. -/
theorem exists_uniformRatePartition_lineMCA {F : Type u} [Field F]
    {δ : ℝ} {n k A : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant δ
        (uniformRatePartitionJetBound δ) (150 * uniformRatePartitionJetBound δ)
        (uniformRatePartitionOrder δ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨ex, hc, hg⟩ := exists_uniformRatePartition_baseCurveMCA hδ hδsmall hn hk hgap hAn
    (by norm_num : 0 < 1) domain ![f, g] hchar
  refine ⟨ex, by simpa only [Nat.cast_one, one_mul] using hc, ?_⟩
  intro z hz P hP hA
  have hw : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
    funext i
    simp [powerBatchedWord, Fin.sum_univ_two]
  have h := hg z hz P hP (by rwa [hw])
  simpa using exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P h

end ReedSolomon
