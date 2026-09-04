/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Specification
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Contracts for all-rate Reed-Solomon list decoding up to capacity

This module freezes proposition-valued targets for the all-rate strengthening of hidden-derivative
list decoding. For each positive capacity gap `delta`, all global parameters are chosen before the
block length, dimension, prime field, evaluation set, and received word. In particular, the
derivative order depends on `delta` alone and not on the code rate.

The primary finite threshold is

`messageDim + Nat.ceil (delta * blockLength)`.

The contracts expose both the exact polynomial list at that threshold and ArkLib's canonical
`Code.Lambda` value at relative radius `1 - messageDim / blockLength - delta`. When the threshold
exceeds the block length, the exact list is required to be empty explicitly.

No declaration in this file asserts that these targets have been proved. They are definitions of
the propositions to be discharged by later modules.

## References

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed-Solomon Codes
  up to Capacity in the Low-Rate Regime*, ECCC TR26-164.
* Dao and Thaler, *Reed-Solomon List Decoding at All Rates via Hidden Derivatives*, manuscript.
-/

namespace ReedSolomon
namespace AllRateListDecoding

open ListDecoding

noncomputable section

/-- The absolute agreement threshold used by the all-rate theorem. -/
def agreementThreshold (delta : ℝ) (blockLength messageDim : ℕ) : ℕ :=
  messageDim + Nat.ceil (delta * (blockLength : ℝ))

/-- The corresponding real-valued radius in ArkLib's `Code.Lambda` convention. -/
def capacityRadius (delta : ℝ) (blockLength messageDim : ℕ) : ℝ :=
  1 - (messageDim : ℝ) / blockLength - delta

/-- The set of all degree-bounded polynomials meeting the absolute agreement threshold. -/
def agreeingPolynomials {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (messageDim minAgreement : ℕ) (received : index → F) :
    Set (MessagePolynomial F messageDim) :=
  {p | minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received}

/-- No polynomial can meet an agreement threshold strictly larger than the block length. -/
theorem agreeingPolynomials_eq_empty_of_card_lt {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement : ℕ} (hThreshold : Fintype.card index < minAgreement)
    (received : index → F) :
    agreeingPolynomials domain messageDim minAgreement received = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  change minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received at hp
  exact (Nat.not_le_of_lt hThreshold)
    (hp.trans (Code.agree_le_card (u := ReedSolomon.evalOnPoints domain p) (v := received)))

/-- A list bound with a gap-dependent prefactor and exponent overhead.

The exponent is written as `2 * derivOrder + exponentOverhead`, so an initial
`q ^ (4 * derivOrder + 6)` bound is represented by choosing
`exponentOverhead = 2 * derivOrder + 6`. -/
def qualitativeListBound
    (fieldSize derivOrder listFactor exponentOverhead : ℕ) : ℕ :=
  listFactor * fieldSize ^ (2 * derivOrder + exponentOverhead)

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

/-- **Qualitative all-rate combinatorial target.**

For every fixed positive gap, the derivative order, block-length threshold, list prefactor, and
exponent overhead are selected before every code parameter. The conclusion gives both the
canonical `Lambda` bound and the exact pointwise polynomial-list bound. -/
def QualitativeCombinatorialStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ derivOrder blockLengthThreshold listFactor exponentOverhead : ℕ,
      0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ (domain : Fin blockLength ↪ ZMod fieldSize),
          let listBound := qualitativeListBound fieldSize derivOrder listFactor exponentOverhead
          Code.Lambda
              (ReedSolomon.code domain messageDim : Set (Fin blockLength → ZMod fieldSize))
              (capacityRadius delta blockLength messageDim) ≤ (listBound : ℕ∞) ∧
            ∀ received : Fin blockLength → ZMod fieldSize,
              PointwiseListBound delta domain messageDim listBound received

/-- **Qualitative all-rate exact-decoder target.**

This strengthens the combinatorial target with one exact decoder for every evaluation set. Its
specification quantifies over all received words internally. -/
def QualitativeExactDecoderStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ derivOrder blockLengthThreshold listFactor exponentOverhead : ℕ,
      0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ domain : Fin blockLength ↪ ZMod fieldSize,
          Nonempty <| CapacityGapCertificate delta domain messageDim
            (qualitativeListBound fieldSize derivOrder listFactor exponentOverhead)

/-- **Combined qualitative capstone.**

This is the phase-one target: all rates, arbitrary distinct evaluation points, prime fields of
size at least the block length, and a derivative order depending only on the fixed capacity gap.
The constants may be weaker than the manuscript's optimized constants. -/
def QualitativeAllRateStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∃ derivOrder blockLengthThreshold listFactor exponentOverhead : ℕ,
      0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ (domain : Fin blockLength ↪ ZMod fieldSize),
          let listBound := qualitativeListBound fieldSize derivOrder listFactor exponentOverhead
          Nonempty (CapacityGapCertificate delta domain messageDim listBound) ∧
            ∀ received : Fin blockLength → ZMod fieldSize,
              PointwiseListBound delta domain messageDim listBound received

/-- The derivative order in the strong quantitative target.

The constant `172 / 25` is the exact rational representation of `6.88`. -/
def strongDerivativeOrder (delta : ℝ) : ℕ :=
  if (1 / 2 : ℝ) ≤ delta then 0
  else if (1 / 4 : ℝ) ≤ delta then 1
  else Nat.ceil (Real.exp (((172 : ℝ) / 25) / delta))

/-- The larger-field condition under which the strong target improves its exponent from `2d`
to `d`. The interpolation multiplicity is selected as a function of the gap before the code
parameters. -/
def LargeFieldCondition (delta : ℝ) (blockLength messageDim fieldSize multiplicity : ℕ) :
    Prop :=
  2 * multiplicity * agreementThreshold delta blockLength messageDim ≤ fieldSize

/-- **Strong quantitative all-rate target.**

This target fixes the optimized derivative order, asks for a `C(delta) * q^(2d)` list bound over
all prime fields of size at least `n`, and asks for `C(delta) * q^d` under the larger-field
condition. The block threshold, interpolation multiplicity, and prefactor are all chosen before
the code rate and field. -/
def StrongQuantitativeAllRateStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    let derivOrder := strongDerivativeOrder delta
    ∃ blockLengthThreshold multiplicity listFactor : ℕ,
      0 < multiplicity ∧ 0 < listFactor ∧
      ∀ blockLength messageDim fieldSize : ℕ,
        blockLengthThreshold ≤ blockLength →
        0 < messageDim → messageDim ≤ blockLength →
        fieldSize.Prime → blockLength ≤ fieldSize →
        ∀ domain : Fin blockLength ↪ ZMod fieldSize,
          Nonempty (CapacityGapCertificate delta domain messageDim
            (listFactor * fieldSize ^ (2 * derivOrder))) ∧
          (LargeFieldCondition delta blockLength messageDim fieldSize multiplicity →
            Nonempty (CapacityGapCertificate delta domain messageDim
              (listFactor * fieldSize ^ derivOrder)))

end
end AllRateListDecoding
end ReedSolomon
