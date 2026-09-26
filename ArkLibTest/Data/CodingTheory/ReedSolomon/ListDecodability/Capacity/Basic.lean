/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic

/-!
# Acceptance cases for capacity-gap list-bound certificates

These cases compute a polynomial list bound and exercise the generic certificate interface,
including a concrete Reed–Solomon instance, its pointwise list conclusion, and the
oversized-threshold case.
-/

open ReedSolomon ReedSolomon.ListDecoding

private def singletonDomain : Fin 1 ↪ ZMod 2 where
  toFun _ := 0
  inj' _ _ _ := Subsingleton.elim _ _

private theorem singletonThreshold :
    capacityAgreementThreshold 1 (Fintype.card (Fin 1)) 1 = 2 := by
  simp [capacityAgreementThreshold]

private def singletonDecoder : DecoderCertificate singletonDomain 1
    (capacityAgreementThreshold 1 (Fintype.card (Fin 1)) 1) 0 where
  enumerate _ := ∅
  isExact := by
    intro received p
    constructor
    · simp
    · intro hAccept
      have hAgreement := Code.agree_le_card
        (u := ReedSolomon.evalOnPoints singletonDomain p) (v := received)
      rw [singletonThreshold] at hAccept
      have hAgreementLt : Code.agree
          (ReedSolomon.evalOnPoints singletonDomain p) received < 2 :=
        hAgreement.trans_lt (by decide)
      exact False.elim ((Nat.not_le_of_gt hAgreementLt) hAccept)
  card_le := by
    intro received
    simp

private noncomputable def singletonCapacityCertificate :
    CapacityGapCertificate 1 singletonDomain 1 0 :=
  CapacityGapCertificate.ofDecoderCertificateAndPointwiseBound
    (by norm_num) (by decide) singletonDecoder (by
      intro received
      have hEmpty : agreeingPolynomials singletonDomain 1
          (capacityAgreementThreshold 1 (Fintype.card (Fin 1)) 1) received = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hAgreement
        have hAgreementLe := Code.agree_le_card
          (u := ReedSolomon.evalOnPoints singletonDomain p) (v := received)
        have hAgreementLt : Code.agree
            (ReedSolomon.evalOnPoints singletonDomain p) received < 2 :=
          hAgreementLe.trans_lt (by decide)
        rw [singletonThreshold] at hAgreement
        exact (Nat.not_le_of_gt hAgreementLt) hAgreement
      rw [hEmpty]
      simp)

example : polynomialListBound 7 3 2 = 147 := by
  norm_num [polynomialListBound]

example : PointwiseListBound 1 singletonDomain 1 0 (fun _ => 0) :=
  singletonCapacityCertificate.pointwiseListBound _

example {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} {domain : ι ↪ F} {messageDim listBound : ℕ}
    (certificate : CapacityGapCertificate delta domain messageDim listBound)
    (received : ι → F) :
    PointwiseListBound delta domain messageDim listBound received :=
  certificate.pointwiseListBound received

example {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} {domain : ι ↪ F} {messageDim listBound : ℕ}
    (certificate : CapacityGapCertificate delta domain messageDim listBound)
    (hThreshold : Fintype.card ι < capacityAgreementThreshold delta (Fintype.card ι) messageDim)
    (received : ι → F) :
    certificate.decoderCertificate.decoder received = ∅ :=
  certificate.decoderCertificate.decoder_eq_empty_of_card_lt hThreshold received

example {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} {domain : ι ↪ F} {messageDim listBound : ℕ}
    (decoderCertificate : DecoderCertificate domain messageDim
      (capacityAgreementThreshold delta (Fintype.card ι) messageDim) listBound)
    (lambda_le :
      Code.Lambda (ReedSolomon.code domain messageDim : Set (ι → F))
        (capacityRadius delta (Fintype.card ι) messageDim) ≤ (listBound : ℕ∞)) :
    (CapacityGapCertificate.ofDecoderCertificate decoderCertificate lambda_le).decoderCertificate =
      decoderCertificate := rfl

example {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι] {delta : ℝ}
    (hdelta : 0 ≤ delta) {messageDim : ℕ} (hn : 0 < Fintype.card ι)
    (domain : ι ↪ F) (received : ι → F) :
    Code.closeCodewordsRel
        (ReedSolomon.code domain messageDim : Set (ι → F)) received
        (capacityRadius delta (Fintype.card ι) messageDim) =
      (fun p : MessagePolynomial F messageDim => ReedSolomon.evalOnPoints domain p) ''
        agreeingPolynomials domain messageDim
          (capacityAgreementThreshold delta (Fintype.card ι) messageDim) received :=
  closeCodewordsRel_eq_eval_image_agreeingPolynomials hdelta hn domain received
