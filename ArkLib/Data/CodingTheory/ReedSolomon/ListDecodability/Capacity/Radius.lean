/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
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

@[expose] public section

namespace ReedSolomon

open ListDecoding

noncomputable section

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

/-- Package finite pointwise lists as an extensional exact decoder and its matching capacity-gap
certificate. This construction uses classical finite-set extraction; it asserts neither an
executable interpolation/root algorithm nor a running-time bound. -/
def CapacityGapCertificate.ofPointwiseBound
    {delta : ℝ} (hdelta : 0 ≤ delta) {n q k bound : ℕ}
    (hn : 0 < n) (domain : Fin n ↪ ZMod q)
    (hBound : ∀ received : Fin n → ZMod q,
      (agreeingPolynomials domain k (agreementThreshold delta n k) received).encard ≤
        (bound : ℕ∞)) : CapacityGapCertificate delta domain k bound := by
  classical
  let finiteList := fun received ↦ Set.finite_of_encard_le_coe (hBound received)
  let certificate : DecoderCertificate domain k (agreementThreshold delta n k) bound := {
    decoder := fun received ↦ (finiteList received).toFinset
    isExact := by
      intro received p
      simp only [Set.Finite.mem_toFinset]
      rfl
    card_le := by
      intro received
      have h := hBound received
      rw [(finiteList received).encard_eq_coe_toFinset_card] at h
      exact_mod_cast h
  }
  exact CapacityGapCertificate.ofDecoderCertificateAndPointwiseBound
    hdelta hn domain certificate hBound

end
end ReedSolomon
