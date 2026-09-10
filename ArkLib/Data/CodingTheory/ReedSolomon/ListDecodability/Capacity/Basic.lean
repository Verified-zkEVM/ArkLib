/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Capacity
/-!
# Capacity-gap parameters and list-bound certificates

This module defines parameters and extensional certificates for all-rate list decoding. For each
positive capacity gap `delta`, the list prefactor and exponent are chosen before the block length,
dimension, prime field, evaluation set, and received word. These propositions certify neither
the derivative order of a construction nor an efficient implementation. Construction witnesses
are specified separately in `HiddenDerivative/Interpolation/Certificates.lean`.

The primary finite threshold is

`messageDim + Nat.ceil (delta * blockLength)`.

The contracts expose both the exact polynomial list at that threshold and ArkLib's canonical
`Code.Lambda` value at relative radius `1 - messageDim / blockLength - delta`. When the threshold
exceeds the block length, the exact list is required to be empty explicitly.

The paper-facing theorem is `exists_capacity_list` in `Capacity.lean`. The certificates here
support its interpolation, counting, and relative-radius interfaces; they are not algorithmic
specifications.

## References

* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed-Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], ECCC TR26-164.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], manuscript.
-/

@[expose] public section

namespace ReedSolomon

open ListDecoding

noncomputable section

/-- A polynomial list bound. Both the prefactor and exponent may depend on the gap, but neither
parameter purports to be a derivative order of an algorithm. -/
def polynomialListBound (fieldSize listFactor listExponent : ℕ) : ℕ :=
  listFactor * fieldSize ^ listExponent

/-- A fixed-instance certificate synchronizing exact polynomial decoding and `Code.Lambda`.

The last field deliberately records the `agreementThreshold > blockLength` case, even though it
also follows from exactness. Keeping the branch in the capstone interface prevents it from being
lost when the threshold and radius formulations are connected through floor and ceiling lemmas. -/
structure CapacityGapCertificate (delta : ℝ) {blockLength fieldSize : ℕ}
    (domain : Fin blockLength ↪ ZMod fieldSize) (messageDim listBound : ℕ) where
  /-- An exact decoder for the integral agreement threshold. -/
  decoderCertificate : DecoderCertificate domain messageDim
    (agreementThreshold delta blockLength messageDim) listBound
  /-- The canonical maximized point-list bound at the capacity-gap radius. -/
  lambda_le :
    Code.Lambda (ReedSolomon.code domain messageDim : Set (Fin blockLength → ZMod fieldSize))
      (capacityRadius delta blockLength messageDim) ≤ (listBound : ℕ∞)
  /-- The requested list is empty when the integral threshold exceeds the block length. -/
  empty_of_threshold_exceeds :
    blockLength < agreementThreshold delta blockLength messageDim →
      ∀ received, decoderCertificate.decoder received = ∅

/-- Package an exact decoder and a `Lambda` bound into a capacity-gap certificate. The explicit
oversized-threshold field is discharged from exactness rather than imposed as new evidence. -/
def CapacityGapCertificate.ofDecoderCertificate (delta : ℝ)
    {blockLength fieldSize : ℕ} {domain : Fin blockLength ↪ ZMod fieldSize}
    {messageDim listBound : ℕ}
    (decoderCertificate : DecoderCertificate domain messageDim
      (agreementThreshold delta blockLength messageDim) listBound)
    (lambda_le :
      Code.Lambda (ReedSolomon.code domain messageDim : Set (Fin blockLength → ZMod fieldSize))
        (capacityRadius delta blockLength messageDim) ≤ (listBound : ℕ∞)) :
    CapacityGapCertificate delta domain messageDim listBound where
  decoderCertificate := decoderCertificate
  lambda_le := lambda_le
  empty_of_threshold_exceeds hThreshold received :=
    decoderCertificate.decoder_eq_empty_of_card_lt (by simpa using hThreshold) received

/-- The pointwise combinatorial content for one received word. -/
def PointwiseListBound {blockLength fieldSize : ℕ}
    (delta : ℝ) (domain : Fin blockLength ↪ ZMod fieldSize)
    (messageDim listBound : ℕ) (received : Fin blockLength → ZMod fieldSize) : Prop :=
  (agreeingPolynomials domain messageDim
      (agreementThreshold delta blockLength messageDim) received).encard ≤
        (listBound : ℕ∞) ∧
    (blockLength < agreementThreshold delta blockLength messageDim →
      agreeingPolynomials domain messageDim
        (agreementThreshold delta blockLength messageDim) received = ∅)

/-- A capacity-gap certificate supplies the pointwise polynomial-list bound at every received
word. This checks that the `Finset` decoder and set-valued combinatorial views cannot drift. -/
theorem CapacityGapCertificate.pointwiseListBound {delta : ℝ}
    {blockLength fieldSize : ℕ} {domain : Fin blockLength ↪ ZMod fieldSize}
    {messageDim listBound : ℕ}
    (certificate : CapacityGapCertificate delta domain messageDim listBound)
    (received : Fin blockLength → ZMod fieldSize) :
    PointwiseListBound delta domain messageDim listBound received := by
  constructor
  · have hSet :
        agreeingPolynomials domain messageDim
            (agreementThreshold delta blockLength messageDim) received =
          (certificate.decoderCertificate.decoder received :
            Set (MessagePolynomial (ZMod fieldSize) messageDim)) := by
      ext p
      change
        agreementThreshold delta blockLength messageDim ≤
            Code.agree (ReedSolomon.evalOnPoints domain p) received ↔
          p ∈ certificate.decoderCertificate.decoder received
      exact (certificate.decoderCertificate.isExact received p).symm
    rw [hSet, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast certificate.decoderCertificate.card_le received
  · intro hThreshold
    exact agreeingPolynomials_eq_empty_of_card_lt (by simpa using hThreshold) received

/-- For every fixed positive gap, one polynomial list bound works at every code rate. The
prefactor, exponent, and block threshold depend only on the gap. Each certificate includes the
exact list, relative-radius bound, and empty oversized-threshold case, but no running-time claim. -/
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

/-- A uniform capacity-gap certificate bounds the polynomial list at every received word. -/
theorem UniformPrimeFieldCapacityListBound.exists_uniform_pointwise_bound
    (h : UniformPrimeFieldCapacityListBound) {delta : ℝ} (hdelta : 0 < delta) (hOne : delta < 1) :
    ∃ N B E : ℕ, 0 < B ∧ ∀ n k q : ℕ,
      N ≤ n → 0 < k → k ≤ n → q.Prime → n ≤ q →
      ∀ (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q),
        PointwiseListBound delta domain k (polynomialListBound q B E) received := by
  obtain ⟨N, B, E, hB, hCertificate⟩ := h delta hdelta hOne
  refine ⟨N, B, E, hB, fun n k q hn hk hkn hq hnq domain received ↦ ?_⟩
  obtain ⟨certificate⟩ := hCertificate n k q hn hk hkn hq hnq domain
  exact certificate.pointwiseListBound received

/-- Capacity lists have size at most one for gaps at least one half and strictly less than `4q`
for gaps between one quarter and one half. This asserts list cardinalities, not an interpolation
construction or an efficient decoding algorithm. -/
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
                  (agreementThreshold delta blockLength messageDim) received).encard <
                    ((4 * fieldSize : ℕ) : ℕ∞))

/-- Below gap one quarter, weighted-support parameters give list bounds `B(delta) * q^(2d)`
for all prime fields `q ≥ n` and `B(delta) * q^d` under `LargeFieldCondition`, once `n ≥ 8m`.
The prefactor depends only on the gap. These are exact-list bounds, with no runtime guarantee;
order-indexed interpolants are specified by `WeightedSupportConstruction`. -/
def WeightedSupportListBound : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < (1 / 4 : ℝ) →
    let derivOrder := capacityDerivativeOrder delta
    let multiplicity := weightedSupportMultiplicity delta
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
