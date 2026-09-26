/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Capacity

/-!
# Capacity-gap list-bound certificates

This module defines uniform polynomial-list bounds and certificates for a fixed Reed–Solomon
instance. A certificate synchronizes an exact finite decoder, the polynomial agreement list, and
the canonical point-list bound at the capacity-gap radius. The uniform propositions specify
all-rate prime-field bounds and their large-gap and weighted-support regimes.

## Main statements

* `polynomialListBound`: the field-size polynomial bound from a prefactor and exponent.
* `CapacityGapCertificate`: an exact decoder, a `Code.Lambda` bound, and the oversized-threshold
  empty-list property.
* `CapacityGapCertificate.pointwiseListBound`: the decoder certificate bounds each polynomial
  agreement list and makes it empty above the block length.
* `CapacityGapCertificate.ofDecoderCertificate` and
  `CapacityGapCertificate.ofDecoderCertificateAndPointwiseBound`: package exact decoders with
  their radius or pointwise-list bound.
* `CapacityGapCertificate.ofPointwiseBound`: construct an exact decoder from a pointwise list
  bound and package its capacity-radius certificate.
* `lambda_le_of_forall_agreeingPolynomials_encard_le`: a pointwise polynomial-list bound gives
  the corresponding `Code.Lambda` bound.
* `closeCodewordsRel_eq_eval_image_agreeingPolynomials`: the capacity-radius point list is the
  evaluation image of the integral-threshold agreement list.
* `UniformPrimeFieldCapacityListBound`, `QuarterGapListBound`, `WeightedSupportListBound`:
  uniform list-bound specifications for the full, large-gap, and weighted-support regimes.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open ListDecoding

noncomputable section

/-- A natural-number list bound with a fixed prefactor and field-size exponent. -/
def polynomialListBound (fieldSize listFactor listExponent : ℕ) : ℕ :=
  listFactor * fieldSize ^ listExponent

/-- A fixed-instance certificate synchronizing an exact decoder and a capacity-radius bound.

The coordinate type may be any finite type. Its cardinality determines the agreement threshold
and relative radius. -/
structure CapacityGapCertificate (delta : ℝ) {ι F : Type*} [Semiring F] [DecidableEq F]
    [Fintype ι] (domain : ι ↪ F) (messageDim listBound : ℕ) where
  /-- An exact decoder for the integral agreement threshold. -/
  decoderCertificate : DecoderCertificate domain messageDim
    (capacityAgreementThreshold delta (Fintype.card ι) messageDim) listBound
  /-- The canonical maximized point-list bound at the capacity-gap radius. -/
  lambda_le :
    Code.Lambda (ReedSolomon.code domain messageDim : Set (ι → F))
      (capacityRadius delta (Fintype.card ι) messageDim) ≤ (listBound : ℕ∞)
  /-- The requested list is empty when its integral threshold exceeds the block length. -/
  empty_of_threshold_exceeds :
    Fintype.card ι < capacityAgreementThreshold delta (Fintype.card ι) messageDim →
      ∀ received, decoderCertificate.decoder received = ∅

/-- Package an exact decoder and a `Lambda` bound into a capacity-gap certificate. -/
def CapacityGapCertificate.ofDecoderCertificate {delta : ℝ}
    {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι] {domain : ι ↪ F}
    {messageDim listBound : ℕ}
    (decoderCertificate : DecoderCertificate domain messageDim
      (capacityAgreementThreshold delta (Fintype.card ι) messageDim) listBound)
    (lambda_le :
      Code.Lambda (ReedSolomon.code domain messageDim : Set (ι → F))
        (capacityRadius delta (Fintype.card ι) messageDim) ≤ (listBound : ℕ∞)) :
    CapacityGapCertificate delta domain messageDim listBound where
  decoderCertificate := decoderCertificate
  lambda_le := lambda_le
  empty_of_threshold_exceeds hThreshold received :=
    decoderCertificate.decoder_eq_empty_of_card_lt hThreshold received

/-- The pointwise combinatorial content for one received word. -/
def PointwiseListBound {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (delta : ℝ) (domain : ι ↪ F) (messageDim listBound : ℕ)
    (received : ι → F) : Prop :=
  (agreeingPolynomials domain messageDim
      (capacityAgreementThreshold delta (Fintype.card ι) messageDim) received).encard ≤
        (listBound : ℕ∞) ∧
    (Fintype.card ι < capacityAgreementThreshold delta (Fintype.card ι) messageDim →
      agreeingPolynomials domain messageDim
        (capacityAgreementThreshold delta (Fintype.card ι) messageDim) received = ∅)

/-- A capacity-gap certificate supplies the pointwise polynomial-list bound at every received
word. -/
theorem CapacityGapCertificate.pointwiseListBound {delta : ℝ}
    {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι] {domain : ι ↪ F}
    {messageDim listBound : ℕ}
    (certificate : CapacityGapCertificate delta domain messageDim listBound)
    (received : ι → F) :
    PointwiseListBound delta domain messageDim listBound received := by
  have hSet : agreeingPolynomials domain messageDim
      (capacityAgreementThreshold delta (Fintype.card ι) messageDim) received =
    (certificate.decoderCertificate.decoder received :
      Set (MessagePolynomial F messageDim)) := by
    ext p
    change capacityAgreementThreshold delta (Fintype.card ι) messageDim ≤
        Code.agree (ReedSolomon.evalOnPoints domain p) received ↔
      p ∈ certificate.decoderCertificate.decoder received
    exact ⟨certificate.decoderCertificate.mem_of_agreement_le,
      certificate.decoderCertificate.agreement_le_of_mem⟩
  constructor
  · rw [hSet, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast certificate.decoderCertificate.card_le received
  · intro hThreshold
    rw [hSet]
    simpa using certificate.decoderCertificate.decoder_eq_empty_of_card_lt hThreshold received

/-- The capacity-radius point list is the evaluation image of the agreeing message polynomials. -/
theorem closeCodewordsRel_eq_eval_image_agreeingPolynomials
    {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι] {delta : ℝ}
    (hdelta : 0 ≤ delta) {messageDim : ℕ} (hn : 0 < Fintype.card ι)
    (domain : ι ↪ F) (received : ι → F) :
    Code.closeCodewordsRel
        (ReedSolomon.code domain messageDim : Set (ι → F)) received
        (capacityRadius delta (Fintype.card ι) messageDim) =
      (fun p : MessagePolynomial F messageDim => ReedSolomon.evalOnPoints domain p) ''
        agreeingPolynomials domain messageDim
          (capacityAgreementThreshold delta (Fintype.card ι) messageDim) received := by
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
    change capacityAgreementThreshold delta (Fintype.card ι) messageDim ≤
      Code.agree (ReedSolomon.evalOnPoints domain message) received
    exact (relHammingDist_le_capacityRadius_iff_capacityAgreementThreshold_le
      hdelta hn _ _).mp hDistance
  · rintro ⟨message, hAgreement, rfl⟩
    refine ⟨ReedSolomon.evalOnPoints_mem_code_of_degree_lt
      (Polynomial.mem_degreeLT.mp message.2), ?_⟩
    exact (relHammingDist_le_capacityRadius_iff_capacityAgreementThreshold_le
      hdelta hn _ _).mpr hAgreement

/-- The Lambda bound associated with a pointwise bound on polynomial agreement lists. -/
theorem lambda_le_of_forall_agreeingPolynomials_encard_le
    {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι] {delta : ℝ}
    (hdelta : 0 ≤ delta) (hn : 0 < Fintype.card ι) {domain : ι ↪ F} {messageDim : ℕ}
    (listBound : ℕ∞)
    (hBound : ∀ received : ι → F,
      (agreeingPolynomials domain messageDim
        (capacityAgreementThreshold delta (Fintype.card ι) messageDim) received).encard ≤
          listBound) :
    Code.Lambda (ReedSolomon.code domain messageDim : Set (ι → F))
      (capacityRadius delta (Fintype.card ι) messageDim) ≤ listBound := by
  rw [Code.Lambda_le_iff_forall_encard_le]
  intro received
  rw [closeCodewordsRel_eq_eval_image_agreeingPolynomials hdelta hn]
  exact (Set.encard_image_le _ _).trans (hBound received)

/-- Package an exact decoder and a pointwise polynomial-list bound as a capacity-gap
certificate. -/
def CapacityGapCertificate.ofDecoderCertificateAndPointwiseBound {delta : ℝ}
    (hdelta : 0 ≤ delta) {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (hn : 0 < Fintype.card ι) {domain : ι ↪ F} {messageDim listBound : ℕ}
    (decoderCertificate : DecoderCertificate domain messageDim
      (capacityAgreementThreshold delta (Fintype.card ι) messageDim) listBound)
    (hBound : ∀ received : ι → F,
      (agreeingPolynomials domain messageDim
        (capacityAgreementThreshold delta (Fintype.card ι) messageDim) received).encard ≤
          (listBound : ℕ∞)) :
    CapacityGapCertificate delta domain messageDim listBound :=
  CapacityGapCertificate.ofDecoderCertificate decoderCertificate
    (lambda_le_of_forall_agreeingPolynomials_encard_le hdelta hn
      (domain := domain) (messageDim := messageDim) listBound hBound)

/-- A pointwise finite-list bound gives an exact decoder and its capacity-radius certificate. -/
def CapacityGapCertificate.ofPointwiseBound {delta : ℝ}
    {ι F : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (hdelta : 0 ≤ delta) (hn : 0 < Fintype.card ι) {domain : ι ↪ F}
    {messageDim listBound : ℕ}
    (hBound : ∀ received : ι → F,
      (agreeingPolynomials domain messageDim
        (capacityAgreementThreshold delta (Fintype.card ι) messageDim) received).encard ≤
          (listBound : ℕ∞)) :
    CapacityGapCertificate delta domain messageDim listBound := by
  classical
  let finiteList := fun received ↦ Set.finite_of_encard_le_coe (hBound received)
  let decoderCertificate : DecoderCertificate domain messageDim
      (capacityAgreementThreshold delta (Fintype.card ι) messageDim) listBound := {
    enumerate := fun received ↦ (finiteList received).toFinset
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
    hdelta hn decoderCertificate hBound

/-- For every fixed positive gap, one polynomial list bound works at every code rate. The
prefactor, exponent, and block threshold depend only on the gap. -/
def UniformPrimeFieldCapacityListBound : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ blockLengthThreshold listFactor listExponent : ℕ,
      0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ domain : Fin blockLength ↪ ZMod fieldSize,
          Nonempty (CapacityGapCertificate delta domain messageDim
            (polynomialListBound fieldSize listFactor listExponent))

/-- Uniform certificates at gaps of at least one quarter. For gaps below one half, every list has
strictly fewer than four times the field size elements; at least one half, each has size at most
one. -/
def QuarterGapListBound : Prop :=
  ∀ delta : ℝ, (1 / 4 : ℝ) ≤ delta → delta < 1 →
    ∃ blockLengthThreshold : ℕ,
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ domain : Fin blockLength ↪ ZMod fieldSize,
          let listBound := if (1 / 2 : ℝ) ≤ delta then 1 else 4 * fieldSize
          Nonempty (CapacityGapCertificate delta domain messageDim listBound) ∧
            (delta < (1 / 2 : ℝ) →
              ∀ received : Fin blockLength → ZMod fieldSize,
                (agreeingPolynomials domain messageDim
                  (capacityAgreementThreshold delta blockLength messageDim) received).encard <
                    ((4 * fieldSize : ℕ) : ℕ∞))

/-- Below gap one quarter, weighted-support parameters give list bounds `B(delta) * q^(2d)`
for all prime fields `q ≥ n`, and `B(delta) * q^d` under `LargeFieldCondition`, once `n ≥ 8m`.
The prefactor depends only on the gap. -/
def WeightedSupportListBound : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < (1 / 4 : ℝ) →
    let derivOrder := capacityDerivativeOrder delta
    let multiplicity := weightedSupportMultiplicity derivOrder
    0 < multiplicity ∧
    ∃ listFactor : ℕ, 0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        8 * multiplicity ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ domain : Fin blockLength ↪ ZMod fieldSize,
          Nonempty (CapacityGapCertificate delta domain messageDim
            (listFactor * fieldSize ^ (2 * derivOrder))) ∧
          (LargeFieldCondition delta blockLength messageDim fieldSize derivOrder multiplicity →
            Nonempty (CapacityGapCertificate delta domain messageDim
              (listFactor * fieldSize ^ derivOrder)))

end
end ReedSolomon
