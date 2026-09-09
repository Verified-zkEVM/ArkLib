/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.CertificateBound
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Adapter
/-! # Rate-dependent exact correlated agreement on polynomial curves -/

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

/-- One exceptional set controls all close polynomials on the received curve. -/
theorem exists_ratePartition_curveMCA {F E : Type u} [Field F] [Field E]
    [DecidableEq E] [IsAlgClosed E]
    {R a : ℝ} {d n k A ℓ : ℕ} (p : RatePartitionFiniteParameters R a d)
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hn : ratePartitionLength R d p.multiplicity ≤ n)
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (hℓ : 0 < ℓ) (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant (a - R)
        (ratePartitionJetBound R p.multiplicity)
        (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
          (ratePartitionFiniteRatio R a d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  obtain ⟨hdD, hDlower, hkD, hDn, hνn, hmn, hceil, hn2⟩ :=
    ratePartition_length_guards hR (hRa.trans haone) hn hkR haA
  obtain ⟨cert⟩ := exists_ratePartitionRate_certificate p hR (hRa.trans haone)
    (hR.trans hRa) hd hn hkR haA hAn domain
    (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun _ ↦ powerBatchedCoordinate_natDegree_le _)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := hkR.trans
      ((mul_le_mul_of_nonneg_right hRa.le (Nat.cast_nonneg n)).trans haA)
    exact_mod_cast h
  have hν : 0 < ratePartitionJetBound R p.multiplicity := by
    apply Nat.lt_ceil.mpr
    have hm : (0 : ℝ) < p.multiplicity := by exact_mod_cast p.multiplicity_pos
    simpa only [Nat.cast_zero] using (show (0 : ℝ) < 2 * p.multiplicity / R by positivity)
  have hh : 0 < ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
      (ratePartitionFiniteRatio R a d p.multiplicity) := lt_of_lt_of_le Nat.zero_lt_one
        (le_max_left _ _)
  have hchar' : ringChar F = 0 ∨
      max (⌊R * n⌋₊ + 1 - 1) (ratePartitionJetBound R p.multiplicity) < ringChar F := by
    apply hchar.imp_right
    intro hc
    exact (max_lt (by omega) hνn).trans_le hc
  apply exists_curveMCA_of_certificate_of_jetCharacteristic domain values iota cert hk
    (hkD.trans (Nat.le_succ _)) (by omega) (by omega) hDn hkA hAn hν hh hℓ
    le_rfl (sub_pos.mpr hRa) (by linarith) ?_ hchar'
  nlinarith
open Classical in
/-- Restrict the single exceptional set to the base field without increasing its size. -/
theorem exists_ratePartition_baseCurveMCA {F : Type u} [Field F]
    {R a : ℝ} {d n k A ℓ : ℕ} (p : RatePartitionFiniteParameters R a d)
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hn : ratePartitionLength R d p.multiplicity ≤ n)
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (hℓ : 0 < ℓ) (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant (a - R)
        (ratePartitionJetBound R p.multiplicity)
        (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
          (ratePartitionFiniteRatio R a d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  obtain ⟨ex, hc, hg⟩ := exists_ratePartition_curveMCA p hR hRa haone hd hn hk hkR haA hAn
    hℓ domain values iota hchar
  obtain ⟨ex', hc', hg'⟩ := exists_exceptional_powerAgreement_descend domain values iota k A ex hg
  exact ⟨ex', (Nat.cast_le.mpr hc').trans hc, hg'⟩

open Classical in
/-- The line specialization preserves the complete agreement set for every close polynomial. -/
theorem exists_ratePartition_lineMCA {F : Type u} [Field F]
    {R a : ℝ} {d n k A : ℕ} (p : RatePartitionFiniteParameters R a d)
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hn : ratePartitionLength R d p.multiplicity ≤ n)
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant (a - R)
        (ratePartitionJetBound R p.multiplicity)
        (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
          (ratePartitionFiniteRatio R a d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨ex, hc, hg⟩ := exists_ratePartition_baseCurveMCA p hR hRa haone hd hn hk hkR haA hAn
    (by norm_num : 0 < 1) domain ![f, g] hchar
  refine ⟨ex, by simpa only [Nat.cast_one, one_mul] using hc, ?_⟩
  intro z hz P hP hA
  have hw : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
    funext i
    simp [powerBatchedWord, Fin.sum_univ_two]
  have h := hg z hz P hP (by rwa [hw])
  simpa using exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P h
open Classical in
/-- A bare strict gate chooses the line-MCA parameters before all fields and received words. -/
theorem exists_ratePartition_lineMCA_parameters {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    (hgate : 1 < ratePartitionGamma R a d) :
    ∃ p : RatePartitionFiniteParameters R a d,
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      ratePartitionLength R d p.multiplicity ≤ n → 0 < k →
      (k : ℝ) ≤ R * n → a * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
      (ringChar F = 0 ∨ n ≤ ringChar F) →
      ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant (a - R)
          (ratePartitionJetBound R p.multiplicity)
          (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
            (ratePartitionFiniteRatio R a d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨p⟩ := exists_ratePartitionFiniteParameters hR (hR.trans hRa) (by omega) hgate
  exact ⟨p, fun _ _ _ _ _ hn hk hkR haA hAn domain f g hchar ↦
    exists_ratePartition_lineMCA p hR hRa haone hd hn hk hkR haA hAn domain f g hchar⟩

end ReedSolomon
