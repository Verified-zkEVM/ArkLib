/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.CertificateBound
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.RateCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformEnvelope
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Fin.VecNotation

/-!
# Uniform rate-partition exact correlated agreement

For `0 < δ < 6/25`, the uniform recipe takes `d = ⌈exp (3/(2δ))⌉`, multiplicity
`m = ⌈1000 d² log(6d)⌉`, and block threshold `⌈2m/δ²⌉`. One exceptional set is chosen
before the challenge and candidate. For a power-batched curve of degree `ℓ`, its size is at
most `ℓ * C * n^(d+1)`, where `C` is the polynomial-curve agreement constant at jet cap
`⌈m/δ²⌉ - 1` and height `150` times that cap. Every close candidate outside the set has exact
power agreement with base-field constituents and the same complete agreement set.

## Main statements

* `ReedSolomon.exists_uniformRatePartition_curve_exactPowerAgreement`: extension-field curve
  agreement.
* `ReedSolomon.exists_uniformRatePartition_baseCurve_exactPowerAgreement`: base-field curve
  agreement.
* `ReedSolomon.exists_uniformRatePartition_line_exactCorrelatedPair`: exact agreement on affine
  lines.

## References

* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative.RatePartition

universe u

open Classical in
/-- The uniform rate-partition parameters give an explicit exceptional-set bound for a
power-batched received curve over an algebraically closed extension. -/
theorem exists_uniformRatePartition_curve_exactPowerAgreement {F E : Type u} [Field F] [Field E]
    [IsAlgClosed E] {δ : ℝ} {n k A ℓ : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformBlockThreshold δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ
        (uniformJetCap δ) (150 * uniformJetCap δ) (uniformDerivativeOrder δ) *
        (n : ℝ) ^ (uniformDerivativeOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  let d := uniformDerivativeOrder δ
  let ν := uniformJetCap δ
  obtain ⟨e⟩ := HiddenDerivative.RatePartition.exists_uniformRatePartitionEnvelope
    hδ hδsmall hn hk hgap hAn
  obtain ⟨hd500, hδone, hν, _hνn, hscale, hkA, hchar'⟩ :=
    HiddenDerivative.RatePartition.uniformEnvelope_exactAgreementGuards e hδ hδsmall hn hgap hchar
  obtain ⟨cert⟩ := e.exists_curve_certificate (scale := 1000) hδ hδone hd500 hscale hAn
    domain (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun _ ↦ powerBatchedCoordinate_natDegree_le _)
  have hh : 0 < 150 * ν := by positivity
  exact exists_exceptional_exactPowerAgreement_of_certificate_of_jetCharacteristic
    domain values iota cert hk e.message_le (by omega) (by have := e.order_le; omega)
    e.ambient_le hkA hAn hν hh hℓ le_rfl hδ hδone.le hgap hchar'

open Classical in
/-- The extension-field curve bound descends to challenges and candidates over the base field. -/
theorem exists_uniformRatePartition_baseCurve_exactPowerAgreement {F : Type u} [Field F]
    {δ : ℝ} {n k A ℓ : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformBlockThreshold δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ
        (uniformJetCap δ) (150 * uniformJetCap δ) (uniformDerivativeOrder δ) *
        (n : ℝ) ^ (uniformDerivativeOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  obtain ⟨exceptional, hcard, hgood⟩ := exists_uniformRatePartition_curve_exactPowerAgreement
    hδ hδsmall hn hk hgap hAn hℓ domain values iota hchar
  have hdesc : UniformExactPowerAgreement domain values k A exceptional.card :=
    uniformExactPowerAgreement_of_extension domain values iota k A exceptional hgood
  change ∃ exceptional' : Finset F, exceptional'.card ≤ exceptional.card ∧
    ∀ z ∉ exceptional', ∀ P : F[X], P.degree < k →
      A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
      HasExactPowerAgreement domain values (RingHom.id F) k z P at hdesc
  obtain ⟨exceptional', hcard', hgood'⟩ := hdesc
  refine ⟨exceptional', ?_, hgood'⟩
  exact (Nat.cast_le.mpr hcard').trans hcard

open Classical in
/-- The degree-one specialization gives exact correlated-pair agreement on every line outside
one exceptional set. -/
theorem exists_uniformRatePartition_line_exactCorrelatedPair {F : Type u} [Field F] {δ : ℝ}
    {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25) (hn : uniformBlockThreshold δ ≤ n)
    (hk : 0 < k) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ polynomialCurveProductAgreementConstant δ
        (uniformJetCap δ) (150 * uniformJetCap δ) (uniformDerivativeOrder δ) *
        (n : ℝ) ^ (uniformDerivativeOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_uniformRatePartition_baseCurve_exactPowerAgreement
    hδ hδsmall hn hk hgap hAn (by norm_num : 0 < 1) domain ![f, g] hchar
  refine ⟨exceptional, by simpa using hcard, ?_⟩
  intro z hz P hP hA
  have hword : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
    funext i
    simp [powerBatchedWord, Fin.sum_univ_two]
  have h := hgood z hz P hP (by rwa [hword])
  exact exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P h

end ReedSolomon
