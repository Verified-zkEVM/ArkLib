/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.Basic.Distance
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.Finset.Enumeration

/-!
# Exact Reed–Solomon list-decoder specifications

This module specializes the generic finite-enumeration interface to Reed–Solomon messages.
The generic filtering and cardinality proofs live in `ArkLib.Data.Finset.Enumeration`; this file
only supplies degree-bounded message polynomials, evaluation, and absolute agreement.

An ambient candidate generator may work at a larger design dimension and return false positives.
Its candidates are pulled back to the requested message space and filtered by actual agreement.
Thus interpolation or root finding may use `designDim`, while the exact decoder still targets
`messageDim`.

The interface contains no running-time assertion. An executable decoder must separately refine
this specification in an explicit cost model.
-/

@[expose] public section

namespace ReedSolomon
namespace ListDecoding

noncomputable section

/-- A Reed–Solomon message polynomial of degree strictly less than `messageDim`. -/
abbrev MessagePolynomial (F : Type*) [Semiring F] (messageDim : ℕ) :=
  Polynomial.degreeLT F messageDim

/-- A finite, duplicate-free list decoder for degree-bounded messages. -/
abbrev Decoder (F : Type*) [Semiring F] (index : Type*) [Fintype index]
    (messageDim : ℕ) :=
  Finset.Enumeration (index → F) (MessagePolynomial F messageDim)

/-- The Reed–Solomon acceptance predicate at an absolute agreement threshold. -/
def Accepts {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (minAgreement : ℕ)
    (received : index → F) (p : Polynomial F) : Prop :=
  minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received

/-- A decoder is exact when it returns precisely the degree-bounded messages meeting the
absolute agreement threshold. -/
def IsExactDecoder {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (messageDim minAgreement : ℕ)
    (decoder : Decoder F index messageDim) : Prop :=
  Finset.IsExactEnumeration
    (fun received (p : MessagePolynomial F messageDim) ↦
      Accepts domain minAgreement received (p : Polynomial F)) decoder

/-- An exact decoder with a uniform natural-number output bound. -/
abbrev DecoderCertificate {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] (domain : index ↪ F) (messageDim minAgreement listBound : ℕ) :=
  Finset.EnumerationCertificate
    (fun received (p : MessagePolynomial F messageDim) ↦
      Accepts domain minAgreement received p) listBound

/-- Domain-specific name for the enumeration stored in a decoder certificate. -/
abbrev DecoderCertificate.decoder {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] {domain : index ↪ F} {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound) :
    Decoder F index messageDim :=
  certificate.enumerate

/-- A certified ambient polynomial candidate generator. It may return false positives, but it
contains every degree-`< designDim` polynomial meeting the agreement threshold. -/
structure CandidateCertificate {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] (domain : index ↪ F) (designDim minAgreement listBound : ℕ) where
  /-- The ambient polynomial candidates. -/
  candidates : (index → F) → Finset (Polynomial F)
  /-- Completeness for agreeing polynomials in the ambient design space. -/
  complete : ∀ (received : index → F) (p : Polynomial F),
    p ∈ Polynomial.degreeLT F designDim →
      Accepts domain minAgreement received p → p ∈ candidates received
  /-- Uniform ambient-candidate bound. -/
  card_le : ∀ received, (candidates received).card ≤ listBound

/-- The natural embedding from a smaller target message space into a larger design space. -/
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

/-- Regard an ambient Reed–Solomon candidate certificate as a generic complete candidate
enumeration for a smaller target message space. -/
def CandidateCertificate.toFiniteEnumeration {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (h : messageDim ≤ designDim) :
    Finset.CandidateCertificate (messagePolynomialValue messageDim)
      (fun received (p : MessagePolynomial F messageDim) ↦
        Accepts domain minAgreement received (p : Polynomial F)) listBound where
  candidates := certificate.candidates
  complete := by
    intro received p hp
    exact certificate.complete received p (Polynomial.degreeLT_mono h p.2) hp
  card_le := certificate.card_le

/-- Pull an ambient candidate list back to the target message dimension and filter it by actual
agreement. -/
def CandidateCertificate.filteredDecoder {F index : Type*} [Semiring F] [DecidableEq F]
    [Fintype index] {domain : index ↪ F} {designDim minAgreement listBound : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (messageDim : ℕ) : Decoder F index messageDim :=
  Finset.filterCandidates (messagePolynomialValue messageDim)
    (fun received (p : MessagePolynomial F messageDim) ↦
      Accepts domain minAgreement received (p : Polynomial F)) certificate.candidates

/-- Membership in the filtered decoder is ambient membership together with the actual agreement
check. -/
lemma CandidateCertificate.mem_filteredDecoder {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (received : index → F) (p : MessagePolynomial F messageDim) :
    p ∈ certificate.filteredDecoder messageDim received ↔
      (p : Polynomial F) ∈ certificate.candidates received ∧
        Accepts domain minAgreement received p := by
  simpa [CandidateCertificate.filteredDecoder] using
    Finset.mem_filterCandidates (messagePolynomialValue messageDim)
      (fun received (p : MessagePolynomial F messageDim) ↦
        Accepts domain minAgreement received (p : Polynomial F))
      certificate.candidates received p

/-- Filtering a complete ambient generator at a smaller message dimension is exact. -/
theorem CandidateCertificate.filteredDecoder_isExact {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (h : messageDim ≤ designDim) :
    IsExactDecoder domain messageDim minAgreement
      (certificate.filteredDecoder messageDim) :=
  (certificate.toFiniteEnumeration h).isExact_filterCandidates

/-- Filtering and pullback cannot increase the ambient candidate-list cardinality. -/
theorem CandidateCertificate.filteredDecoder_card_le {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (messageDim : ℕ) :
    ∀ received, (certificate.filteredDecoder messageDim received).card ≤ listBound := by
  intro received
  exact (Finset.card_filterCandidates_le (messagePolynomialValue messageDim)
    (fun received (p : MessagePolynomial F messageDim) ↦
      Accepts domain minAgreement received (p : Polynomial F))
    certificate.candidates received).trans (certificate.card_le received)

/-- Package filtered ambient candidates as an exact target decoder. -/
def CandidateCertificate.toDecoderCertificate {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index]
    {domain : index ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (h : messageDim ≤ designDim) :
    DecoderCertificate domain messageDim minAgreement listBound :=
  (certificate.toFiniteEnumeration h).toEnumerationCertificate

/-- Every polynomial returned by a certified decoder meets the agreement threshold. -/
lemma DecoderCertificate.agreement_le_of_mem {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound)
    {received : index → F} {p : MessagePolynomial F messageDim}
    (hp : p ∈ certificate.decoder received) :
    minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received :=
  certificate.accepts_of_mem hp

/-- Every degree-bounded polynomial meeting the agreement threshold is returned. -/
lemma DecoderCertificate.mem_of_agreement_le {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound)
    {received : index → F} {p : MessagePolynomial F messageDim}
    (hp : minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received) :
    p ∈ certificate.decoder received :=
  certificate.mem_of_accepts hp

/-- An exact decoder is empty when its agreement threshold exceeds the block length. -/
theorem IsExactDecoder.decoder_eq_empty_of_card_lt {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement : ℕ} {decoder : Decoder F index messageDim}
    (hExact : IsExactDecoder domain messageDim minAgreement decoder)
    (hThreshold : Fintype.card index < minAgreement) (received : index → F) :
    decoder received = ∅ := by
  change Finset.IsExactEnumeration _ decoder at hExact
  apply hExact.eq_empty_of_forall_not received
  intro p hp
  exact (Nat.not_le_of_lt hThreshold)
    (hp.trans (Code.agree_le_card (u := ReedSolomon.evalOnPoints domain p) (v := received)))

/-- The oversized-threshold consequence specialized to a certified decoder. -/
theorem DecoderCertificate.decoder_eq_empty_of_card_lt {F index : Type*} [Semiring F]
    [DecidableEq F] [Fintype index] {domain : index ↪ F}
    {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound)
    (hThreshold : Fintype.card index < minAgreement) (received : index → F) :
    certificate.decoder received = ∅ := by
  apply certificate.isExact.eq_empty_of_forall_not received
  intro p hp
  exact (Nat.not_le_of_lt hThreshold)
    (hp.trans (Code.agree_le_card (u := ReedSolomon.evalOnPoints domain p) (v := received)))

end
end ListDecoding
end ReedSolomon
