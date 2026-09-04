/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Data.Finset.Preimage

/-!
# Exact Reed-Solomon list-decoder specifications

This module gives an extensional interface for a Reed-Solomon list decoder. The output is a
`Finset` of polynomials in `Polynomial.degreeLT F k`, so the degree bound and duplicate-freedom are
part of the type. Exactness means that membership is equivalent to meeting an absolute agreement
threshold, measured by the canonical `Code.agree` function.

An ambient candidate generator may work at a larger design dimension and return false positives.
The final decoder filters those candidates by the target message dimension and actual agreement.
This separation is the formal interface for the ambient-padding repair: interpolation and root
finding may use `designDim`, while the requested Reed-Solomon code still uses `messageDim`.

The interface deliberately contains no running-time assertion. A later executable decoder must
separately refine this specification in an explicit cost model.
-/

namespace ReedSolomon
namespace ListDecoding

noncomputable section

/-- A Reed-Solomon message polynomial of degree strictly less than `messageDim`. -/
abbrev MessagePolynomial (F : Type*) [Semiring F] (messageDim : ℕ) :=
  Polynomial.degreeLT F messageDim

/-- A decoder whose outputs are finite, duplicate-free lists of degree-bounded polynomials. -/
abbrev Decoder (F : Type*) [Semiring F] (index : Type*) [Fintype index]
    (messageDim : ℕ) :=
  (index → F) → Finset (MessagePolynomial F messageDim)

/-- A decoder is exact at `minAgreement` when it returns precisely the degree-bounded
polynomials whose evaluations meet that absolute agreement threshold. -/
def IsExactDecoder {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (messageDim minAgreement : ℕ)
    (decoder : Decoder F index messageDim) : Prop :=
  ∀ (received : index → F) (p : MessagePolynomial F messageDim),
    p ∈ decoder received ↔
      minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received

/-- An exact decoder together with a uniform natural-number bound on every output list. -/
structure DecoderCertificate {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] (domain : index ↪ F) (messageDim minAgreement listBound : ℕ) where
  /-- The decoder being certified. -/
  decoder : Decoder F index messageDim
  /-- Soundness and completeness of the decoder output. -/
  isExact : IsExactDecoder domain messageDim minAgreement decoder
  /-- The uniform output-list bound. -/
  card_le : ∀ received, (decoder received).card ≤ listBound

/-- A certified ambient candidate generator. It may return false positives, but it contains every
degree-`< designDim` polynomial meeting the agreement threshold and has a uniform cardinality
bound. Actual-agreement and target-degree filtering are deferred to the final decoder. -/
structure CandidateCertificate {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] (domain : index ↪ F) (designDim minAgreement listBound : ℕ) where
  /-- The ambient candidate generator. -/
  candidates : (index → F) → Finset (Polynomial F)
  /-- Every sufficiently agreeing ambient polynomial appears in the candidate list. -/
  complete : ∀ (received : index → F) (p : Polynomial F),
    p ∈ Polynomial.degreeLT F designDim →
      minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received →
        p ∈ candidates received
  /-- The uniform candidate-list cardinality bound. -/
  card_le : ∀ received, (candidates received).card ≤ listBound

/-- The natural embedding from the target message space into a larger ambient design space. -/
def messagePolynomialEmbedding {F : Type*} [Semiring F] {messageDim designDim : ℕ}
    (h : messageDim ≤ designDim) :
    MessagePolynomial F messageDim ↪ MessagePolynomial F designDim where
  toFun p := ⟨p, Polynomial.degreeLT_mono h p.2⟩
  inj' _ _ hp := Subtype.ext
    (congrArg (fun r : MessagePolynomial F designDim => (r : Polynomial F)) hp)

/-- Forget the degree proof carried by a message polynomial. -/
def messagePolynomialValue {F : Type*} [Semiring F] (messageDim : ℕ) :
    MessagePolynomial F messageDim ↪ Polynomial F where
  toFun p := p
  inj' _ _ hp := Subtype.ext hp

@[simp]
lemma messagePolynomialValue_apply {F : Type*} [Semiring F] (messageDim : ℕ)
    (p : MessagePolynomial F messageDim) :
    messagePolynomialValue messageDim p = (p : Polynomial F) := rfl

/-- Filter an ambient candidate list to the target message dimension and actual agreement. -/
def CandidateCertificate.filteredDecoder {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] {domain : index ↪ F} {designDim minAgreement listBound : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (messageDim : ℕ) : Decoder F index messageDim := fun received =>
  ((certificate.candidates received).preimage (messagePolynomialValue messageDim)
      (messagePolynomialValue messageDim).injective.injOn).filter fun p =>
    minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received

/-- Membership in the filtered decoder separates into ambient-candidate membership and the
actual agreement check. -/
lemma CandidateCertificate.mem_filteredDecoder {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (received : index → F) (p : MessagePolynomial F messageDim) :
    p ∈ certificate.filteredDecoder messageDim received ↔
      (p : Polynomial F) ∈ certificate.candidates received ∧
        minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received := by
  simp only [filteredDecoder, Finset.mem_filter, Finset.mem_preimage,
    messagePolynomialValue_apply]

/-- Filtering an ambient candidate generator at a smaller message dimension produces an exact
decoder. This is the proof-level ambient-padding repair: completeness is transported along the
degree-space embedding, while the explicit agreement filter supplies soundness. -/
theorem CandidateCertificate.filteredDecoder_isExact {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (h : messageDim ≤ designDim) :
    IsExactDecoder domain messageDim minAgreement
      (certificate.filteredDecoder messageDim) := by
  intro received p
  rw [certificate.mem_filteredDecoder]
  constructor
  · exact fun hp => hp.2
  · intro hp
    refine ⟨?_, hp⟩
    exact certificate.complete received p (Polynomial.degreeLT_mono h p.2) hp

/-- Filtering and taking a preimage along the subtype embedding cannot increase the candidate-list
cardinality. -/
theorem CandidateCertificate.filteredDecoder_card_le {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (messageDim : ℕ) :
    ∀ received, (certificate.filteredDecoder messageDim received).card ≤ listBound := by
  intro received
  calc
    (certificate.filteredDecoder messageDim received).card ≤
        ((certificate.candidates received).preimage (messagePolynomialValue messageDim)
          (messagePolynomialValue messageDim).injective.injOn).card :=
      Finset.card_filter_le _ _
    _ ≤ (certificate.candidates received).card := by
      apply Finset.card_le_card_of_injOn (messagePolynomialValue messageDim)
      · intro p hp
        exact Finset.mem_preimage.mp hp
      · exact (messagePolynomialValue messageDim).injective.injOn
    _ ≤ listBound := certificate.card_le received

/-- Package explicitly filtered ambient candidates as an exact target-code decoder. -/
def CandidateCertificate.toDecoderCertificate {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (h : messageDim ≤ designDim) :
    DecoderCertificate domain messageDim minAgreement listBound where
  decoder := certificate.filteredDecoder messageDim
  isExact := certificate.filteredDecoder_isExact h
  card_le := certificate.filteredDecoder_card_le messageDim

/-- Every polynomial returned by a certified decoder meets the agreement threshold. -/
lemma DecoderCertificate.agreement_le_of_mem {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound)
    {received : index → F} {p : MessagePolynomial F messageDim}
    (hp : p ∈ certificate.decoder received) :
    minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received :=
  (certificate.isExact received p).mp hp

/-- Every degree-bounded polynomial meeting the agreement threshold is returned. -/
lemma DecoderCertificate.mem_of_agreement_le {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound)
    {received : index → F} {p : MessagePolynomial F messageDim}
    (hp : minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received) :
    p ∈ certificate.decoder received :=
  (certificate.isExact received p).mpr hp

/-- An exact decoder returns the empty list when its agreement threshold exceeds the block
length. This makes the otherwise implicit oversized-threshold branch available to capstones. -/
theorem IsExactDecoder.decoder_eq_empty_of_card_lt {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement : ℕ} {decoder : Decoder F index messageDim}
    (hExact : IsExactDecoder domain messageDim minAgreement decoder)
    (hThreshold : Fintype.card index < minAgreement) (received : index → F) :
    decoder received = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hAgreement := (hExact received p).mp hp
  exact (Nat.not_le_of_lt hThreshold)
    (hAgreement.trans (Code.agree_le_card (u := ReedSolomon.evalOnPoints domain p)
      (v := received)))

/-- The oversized-threshold consequence specialized to a certified decoder. -/
theorem DecoderCertificate.decoder_eq_empty_of_card_lt {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound)
    (hThreshold : Fintype.card index < minAgreement) (received : index → F) :
    certificate.decoder received = ∅ :=
  certificate.isExact.decoder_eq_empty_of_card_lt hThreshold received

end
end ListDecoding
end ReedSolomon
