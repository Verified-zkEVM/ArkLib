/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.CurveBridge

/-!
# Exact agreement in the unique-decoding regime

The common decoder on a received curve identifies every close candidate by uniqueness. Excluding
the roots of the nonzero coordinate differences then upgrades common agreement to exact agreement.
-/

@[expose] public section

namespace ProximityGap

open Polynomial ReedSolomon NNReal Code
open scoped BigOperators

/-- Two codewords within the relative unique-decoding radius of the same word coincide. -/
theorem eq_of_relClose_unique
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq F]
    (C : Set (ι → F)) (u v w : ι → F) (hv : v ∈ C) (hw : w ∈ C)
    (δ : ℝ≥0) (hδ : δ ≤ relativeUniqueDecodingRadius C)
    (huv : (relHammingDist u v : ℝ≥0) ≤ δ)
    (huw : (relHammingDist u w : ℝ≥0) ≤ δ) : v = w := by
  apply eq_of_le_uniqueDecodingRadius C u hv hw
  · apply (dist_le_UDR_iff_relDist_le_relUDR C _).mpr
    exact le_trans (by simpa [relHammingDist, NNRat.cast_div, NNRat.cast_natCast] using huv) hδ
  · apply (dist_le_UDR_iff_relDist_le_relUDR C _).mpr
    exact le_trans (by simpa [relHammingDist, NNRat.cast_div, NNRat.cast_natCast] using huw) hδ

/-- The sharp unique-decoding curve count controls exact agreement with every close candidate. -/
theorem exists_exactPowerAgreement_unique_fin
    {F : Type} [Field F] [Finite F] [DecidableEq F] {n deg ℓ : ℕ} [NeZero n]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (hdeg : 0 < deg) (hdeg_le : deg ≤ n) (δ : ℝ≥0)
    (hδ : δ ≤ relativeUniqueDecodingRadius (code domain deg : Set (Fin n → F))) :
    ∃ E : Finset F, E.card ≤ ℓ * n ∧
      ∀ z ∉ E, ∀ Q : F[X], Q.degree < deg →
        ⌈(n : ℝ) * (1 - (δ : ℝ))⌉₊ ≤
          (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
        HasExactPowerAgreement domain w (RingHom.id F) deg z Q := by
  classical
  let _ := Fintype.ofFinite F
  let : NeZero deg := ⟨hdeg.ne'⟩
  have hδ1 : δ ≤ 1 := by
    have hh := hδ
    rw [relativeUniqueDecodingRadius_RS_eq (by simpa using hdeg_le)] at hh
    exact hh.trans (by
      calc _ ≤ (1 : ℝ≥0) / 2 := div_le_div_of_nonneg_right tsub_le_self (by norm_num)
           _ ≤ 1 := by norm_num)
  let S := coeffs_of_close_proximity_curve δ w (toFinset domain deg)
  have hword (z : F) : Curve.polynomialCurveEval w z = powerBatchedWord w z := by
    ext i
    simp [Curve.polynomialCurveEval, powerBatchedWord]
  by_cases hS : n * ℓ < S.card
  · obtain ⟨_, v, hv, hclose, _⟩ :=
      large_agreement_set_on_curve_implies_correlated_agreement hdeg hdeg_le hδ hS
    choose P hP hPv using fun t ↦ mem_code_iff_eval.mp (hv t)
    have hPv' (z : F) : evalOnPoints domain (Polynomial.powerBatch P z) =
        Curve.polynomialCurveEval v z := by
      funext i
      change (Polynomial.powerBatch P z).eval (domain i) = _
      simp only [Polynomial.powerBatch_eval, Curve.polynomialCurveEval,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hPv]
    obtain ⟨E, hE, hgood⟩ := exists_exceptional_exactPowerAgreement_of_polynomials domain w P hP
    refine ⟨E, by simpa using hE, fun z hz Q hQ hA ↦ ?_⟩
    have hcQ := (ceil_le_polynomialAgreementSet_card_iff domain (powerBatchedWord w z)
      Q δ hδ1).mp (by simpa using hA)
    have hcodeQ : evalOnPoints domain Q ∈ code domain deg :=
      mem_code_iff_eval.mpr ⟨Q, hQ, fun _ ↦ rfl⟩
    have hcodeP : evalOnPoints domain (Polynomial.powerBatch P z) ∈ code domain deg :=
      mem_code_iff_eval.mpr ⟨_, Polynomial.degree_powerBatch_lt P z deg hP, fun _ ↦ rfl⟩
    have heq := eq_of_relClose_unique (code domain deg) (powerBatchedWord w z)
      (evalOnPoints domain Q) (evalOnPoints domain (Polynomial.powerBatch P z))
      hcodeQ hcodeP δ hδ hcQ (by rw [hPv', ← hword]; exact_mod_cast hclose z)
    have hpoly : Q = Polynomial.powerBatch P z := by
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq Q _ domain.injective
        (fun i ↦ congrFun heq i)
      apply max_lt
      · exact (ReedSolomon.natDegree_lt_of_mem_degreeLT
          (Polynomial.mem_degreeLT.mpr hQ)).trans_le (by simpa using hdeg_le)
      · exact (ReedSolomon.natDegree_lt_of_mem_degreeLT (Polynomial.mem_degreeLT.mpr
          (Polynomial.degree_powerBatch_lt P z deg hP))).trans_le (by simpa using hdeg_le)
    rw [hpoly]
    exact hgood z hz
  · refine ⟨S, by simpa [Nat.mul_comm] using Nat.le_of_not_gt hS, fun z hz Q hQ hA ↦ ?_⟩
    exfalso
    apply hz
    change z ∈ coeffs_of_close_proximity_curve δ w (toFinset domain deg)
    simp only [coeffs_of_close_proximity_curve, Set.mem_toFinset, Set.mem_ofPred_eq]
    have hclose := (ceil_le_polynomialAgreementSet_card_iff domain (powerBatchedWord w z)
      Q δ hδ1).mp (by simpa using hA)
    have hc : evalOnPoints domain Q ∈ code domain deg :=
      mem_code_iff_eval.mpr ⟨Q, hQ, fun _ ↦ rfl⟩
    have h := (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist
      (powerBatchedWord w z) δ).mpr ⟨_, hc, hclose⟩
    simpa [toFinset, hword] using h


/-- Unique-decoding exact power agreement over any finite evaluation domain. -/
theorem exists_exactPowerAgreement_unique
    {ι F : Type} [Fintype ι] [Field F] [Finite F] [DecidableEq F]
    {deg ℓ : ℕ} (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (hdeg : 0 < deg) (hdeg_le : deg ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ ≤ relativeUniqueDecodingRadius (code domain deg : Set (ι → F))) :
    ∃ E : Finset F, E.card ≤ ℓ * Fintype.card ι ∧
      ∀ z ∉ E, ∀ Q : F[X], Q.degree < deg →
        ⌈(Fintype.card ι : ℝ) * (1 - (δ : ℝ))⌉₊ ≤
          (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
        HasExactPowerAgreement domain w (RingHom.id F) deg z Q := by
  classical
  let _ := Fintype.ofFinite F
  let : NeZero deg := ⟨hdeg.ne'⟩
  let : NeZero (Fintype.card ι) := ⟨by omega⟩
  let e := (Fintype.equivFin ι).symm
  have hδ' : δ ≤ relativeUniqueDecodingRadius
      (code (e.toEmbedding.trans domain) deg : Set (Fin (Fintype.card ι) → F)) := by
    rw [relativeUniqueDecodingRadius_RS_eq (by simpa using hdeg_le)]
    rw [relativeUniqueDecodingRadius_RS_eq hdeg_le] at hδ
    simpa using hδ
  obtain ⟨E, hE, hgood⟩ := exists_exactPowerAgreement_unique_fin
    (e.toEmbedding.trans domain) (fun t ↦ w t ∘ e) hdeg hdeg_le δ hδ'
  refine ⟨E, hE, fun z hz Q hQ hA ↦ ?_⟩
  apply hasExactPowerAgreement_of_comp_equiv e domain w z Q
  apply hgood z hz Q hQ
  change _ ≤ (polynomialAgreementSet (e.toEmbedding.trans domain)
    (powerBatchedWord w z ∘ e) Q).card
  rwa [polynomialAgreementSet_card_comp_equiv]

/-- Unique decoding gives the sharp line count needed for the affine exact-agreement transfer. -/
theorem lineExactAgreementBound_unique
    {ι F : Type} [Fintype ι] [Field F] [Finite F] [DecidableEq F]
    {deg : ℕ} (domain : ι ↪ F) (hdeg : 0 < deg) (hdeg_le : deg ≤ Fintype.card ι)
    (δ : ℝ≥0) (hδ : δ ≤ relativeUniqueDecodingRadius (code domain deg : Set (ι → F))) :
    LineExactAgreementBound domain deg
      ⌈(Fintype.card ι : ℝ) * (1 - (δ : ℝ))⌉₊ (Fintype.card ι : ℝ) := by
  classical
  let _ := Fintype.ofFinite F
  let : NeZero deg := ⟨hdeg.ne'⟩
  let : NeZero (Fintype.card ι) := ⟨by omega⟩
  let e := (Fintype.equivFin ι).symm
  apply lineExactAgreementBound_of_comp_equiv e domain
  apply lineExactAgreementBound_of_exactCorrelatedPair
  intro f g
  apply exists_line_exactCorrelatedPair_of_powerAgreement
  have hδ' : δ ≤ relativeUniqueDecodingRadius
      (code (e.toEmbedding.trans domain) deg : Set (Fin (Fintype.card ι) → F)) := by
    rw [relativeUniqueDecodingRadius_RS_eq (by simpa using hdeg_le)]
    rw [relativeUniqueDecodingRadius_RS_eq hdeg_le] at hδ
    simpa using hδ
  obtain ⟨E, hE, hgood⟩ := exists_exactPowerAgreement_unique_fin
    (e.toEmbedding.trans domain) ![f, g] hdeg hdeg_le δ hδ'
  exact ⟨E, by exact_mod_cast (show E.card ≤ Fintype.card ι by simpa using hE), hgood⟩

end ProximityGap
