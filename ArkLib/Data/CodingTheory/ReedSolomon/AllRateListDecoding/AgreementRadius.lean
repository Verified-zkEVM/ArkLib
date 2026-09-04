/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.Contracts
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Agreement thresholds and the capacity-gap radius

This module proves the exact floor-and-ceiling bridge between the integral agreement threshold

`messageDim + Nat.ceil (delta * blockLength)`

and ArkLib's relative Hamming radius

`1 - messageDim / blockLength - delta`.

It then identifies each Reed-Solomon point list with the image, under evaluation, of the set of
agreeing message polynomials. The image formulation does not require injectivity of evaluation and
therefore isolates the cardinality argument from the separate `messageDim ≤ blockLength` condition.
-/

namespace ReedSolomon
namespace AllRateListDecoding

open ListDecoding

noncomputable section

/-- The natural agreement threshold is equivalent to its real-valued unrounded inequality. -/
lemma agreementThreshold_le_iff_real {delta : ℝ} (hdelta : 0 ≤ delta)
    (blockLength messageDim agreement : ℕ) :
    agreementThreshold delta blockLength messageDim ≤ agreement ↔
      (messageDim : ℝ) + delta * blockLength ≤ agreement := by
  constructor
  · intro hThreshold
    have hCast :
        ((messageDim + Nat.ceil (delta * (blockLength : ℝ)) : ℕ) : ℝ) ≤ agreement := by
      exact_mod_cast hThreshold
    have hCeil :
        delta * (blockLength : ℝ) ≤ (Nat.ceil (delta * (blockLength : ℝ)) : ℝ) :=
      Nat.le_ceil _
    rw [Nat.cast_add] at hCast
    linarith
  · intro hReal
    have hMessageReal : (messageDim : ℝ) ≤ agreement := by
      have hProduct : 0 ≤ delta * (blockLength : ℝ) :=
        mul_nonneg hdelta (Nat.cast_nonneg blockLength)
      linarith
    have hMessage : messageDim ≤ agreement := by
      exact_mod_cast hMessageReal
    have hRemainder :
        delta * (blockLength : ℝ) ≤ ((agreement - messageDim : ℕ) : ℝ) := by
      rw [Nat.cast_sub hMessage]
      linarith
    have hCeil : Nat.ceil (delta * (blockLength : ℝ)) ≤ agreement - messageDim :=
      Nat.ceil_le.mpr hRemainder
    rw [agreementThreshold]
    omega

/-- Relative distance at the capacity-gap radius is exactly the integral agreement condition.

The distance is written from `received` to `codeword`, while agreement is written from `codeword`
to `received`, matching the two public APIs. Symmetry of Hamming distance reconciles the order. -/
lemma relHammingDist_le_capacityRadius_iff_agreementThreshold_le
    {F : Type*} [DecidableEq F] {delta : ℝ} (hdelta : 0 ≤ delta)
    {blockLength messageDim : ℕ} (hBlockLength : 0 < blockLength)
    (codeword received : Fin blockLength → F) :
    (Code.relHammingDist received codeword : ℝ) ≤
        capacityRadius delta blockLength messageDim ↔
      agreementThreshold delta blockLength messageDim ≤ Code.agree codeword received := by
  rw [agreementThreshold_le_iff_real hdelta]
  rw [Code.relHammingDist_coe]
  simp only [Fintype.card_fin]
  rw [hammingDist_comm received codeword]
  have hLengthReal : (0 : ℝ) < blockLength := by
    exact_mod_cast hBlockLength
  have hAgreementDistance :
      (Code.agree codeword received : ℝ) + (hammingDist codeword received : ℝ) =
        blockLength := by
    have hNat :
        Code.agree codeword received + hammingDist codeword received = blockLength := by
      simpa only [Fintype.card_fin] using
        (Code.agree_add_hammingDist (u := codeword) (v := received))
    exact_mod_cast hNat
  have hRadiusMul :
      capacityRadius delta blockLength messageDim * (blockLength : ℝ) =
        blockLength - messageDim - delta * blockLength := by
    rw [capacityRadius]
    field_simp
  constructor
  · intro hDistance
    have hMul := (div_le_iff₀ hLengthReal).mp hDistance
    rw [hRadiusMul] at hMul
    linarith
  · intro hAgreement
    apply (div_le_iff₀ hLengthReal).mpr
    rw [hRadiusMul]
    linarith

/-- The Reed-Solomon point list at the capacity-gap radius is exactly the evaluation image of the
degree-bounded polynomials meeting the integral agreement threshold.

This statement deliberately uses `Set.image`, so it does not need injectivity of evaluation. -/
theorem closeCodewordsRel_eq_eval_image_agreeingPolynomials
    {F : Type*} [Semiring F] [DecidableEq F] {delta : ℝ} (hdelta : 0 ≤ delta)
    {blockLength messageDim : ℕ} (hBlockLength : 0 < blockLength)
    (domain : Fin blockLength ↪ F) (received : Fin blockLength → F) :
    Code.closeCodewordsRel
        (ReedSolomon.code domain messageDim : Set (Fin blockLength → F)) received
        (capacityRadius delta blockLength messageDim) =
      (fun p : MessagePolynomial F messageDim => ReedSolomon.evalOnPoints domain p) ''
        agreeingPolynomials domain messageDim
          (agreementThreshold delta blockLength messageDim) received := by
  ext codeword
  rw [Code.mem_closeCodewordsRel_iff]
  constructor
  · rintro ⟨hCodeword, hDistance⟩
    change codeword ∈ ReedSolomon.code domain messageDim at hCodeword
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hCodeword
    rcases hCodeword with ⟨p, hDegree, hEvaluation⟩
    subst codeword
    let message : MessagePolynomial F messageDim :=
      ⟨p, Polynomial.mem_degreeLT.mpr hDegree⟩
    refine ⟨message, ?_, rfl⟩
    change agreementThreshold delta blockLength messageDim ≤
      Code.agree (ReedSolomon.evalOnPoints domain message) received
    exact (relHammingDist_le_capacityRadius_iff_agreementThreshold_le
      hdelta hBlockLength _ _).mp hDistance
  · rintro ⟨message, hAgreement, rfl⟩
    refine ⟨ReedSolomon.evalOnPoints_mem_code_of_degree_lt
      (Polynomial.mem_degreeLT.mp message.2), ?_⟩
    exact (relHammingDist_le_capacityRadius_iff_agreementThreshold_le
      hdelta hBlockLength _ _).mpr hAgreement

/-- A uniform bound on agreeing message polynomials implies the canonical `Code.Lambda` bound at
the corresponding capacity-gap radius. No injectivity or cardinality equality is needed: the
point list is an evaluation image, whose cardinality can only decrease. -/
theorem lambda_le_of_forall_agreeingPolynomials_encard_le
    {F : Type*} [Semiring F] [DecidableEq F] {delta : ℝ} (hdelta : 0 ≤ delta)
    {blockLength messageDim : ℕ} (hBlockLength : 0 < blockLength)
    (domain : Fin blockLength ↪ F) (listBound : ℕ∞)
    (hBound : ∀ received : Fin blockLength → F,
      (agreeingPolynomials domain messageDim
        (agreementThreshold delta blockLength messageDim) received).encard ≤ listBound) :
    Code.Lambda
        (ReedSolomon.code domain messageDim : Set (Fin blockLength → F))
        (capacityRadius delta blockLength messageDim) ≤ listBound := by
  rw [Code.Lambda_le_iff_forall_encard_le]
  intro received
  rw [closeCodewordsRel_eq_eval_image_agreeingPolynomials hdelta hBlockLength]
  exact (Set.encard_image_le _ _).trans (hBound received)

/-- Assemble the synchronized fixed-instance certificate from an exact decoder and the pointwise
polynomial-list bound produced by the interpolation/root-count argument. -/
def CapacityGapCertificate.ofDecoderCertificateAndPointwiseBound
    {delta : ℝ} (hdelta : 0 ≤ delta) {blockLength fieldSize messageDim listBound : ℕ}
    (hBlockLength : 0 < blockLength) (domain : Fin blockLength ↪ ZMod fieldSize)
    (decoderCertificate : DecoderCertificate domain messageDim
      (agreementThreshold delta blockLength messageDim) listBound)
    (hBound : ∀ received : Fin blockLength → ZMod fieldSize,
      (agreeingPolynomials domain messageDim
        (agreementThreshold delta blockLength messageDim) received).encard ≤
          (listBound : ℕ∞)) :
    CapacityGapCertificate delta domain messageDim listBound :=
  CapacityGapCertificate.ofDecoderCertificate delta decoderCertificate
    (lambda_le_of_forall_agreeingPolynomials_encard_le
      hdelta hBlockLength domain listBound hBound)

end
end AllRateListDecoding
end ReedSolomon
