/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic

/-!
# Acceptance cases for capacity-gap list-bound certificates

These cases compute a polynomial list bound and exercise the generic certificate interface,
including its pointwise list conclusion and oversized-threshold case.
-/

open ReedSolomon ReedSolomon.ListDecoding

example : polynomialListBound 7 3 2 = 147 := by
  norm_num [polynomialListBound]

example {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} {domain : ι ↪ F} {messageDim listBound : ℕ}
    (certificate : CapacityGapCertificate delta domain messageDim listBound)
    (received : ι → F) :
    PointwiseListBound delta domain messageDim listBound received :=
  certificate.pointwiseListBound received

example {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} {domain : ι ↪ F} {messageDim listBound : ℕ}
    (certificate : CapacityGapCertificate delta domain messageDim listBound)
    (hThreshold : Fintype.card ι < agreementThreshold delta (Fintype.card ι) messageDim)
    (received : ι → F) :
    certificate.decoderCertificate.decoder received = ∅ :=
  certificate.empty_of_threshold_exceeds hThreshold received

example {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} {domain : ι ↪ F} {messageDim listBound : ℕ}
    (decoderCertificate : DecoderCertificate domain messageDim
      (agreementThreshold delta (Fintype.card ι) messageDim) listBound)
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
          (agreementThreshold delta (Fintype.card ι) messageDim) received :=
  closeCodewordsRel_eq_eval_image_agreeingPolynomials hdelta hn domain received
