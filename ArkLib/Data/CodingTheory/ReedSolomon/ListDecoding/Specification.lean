/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Exact Reed–Solomon list-decoder specifications

This file defines reusable extensional contracts for Reed–Solomon list decoding. A final decoder
returns exactly the degree-bounded polynomials meeting an absolute agreement threshold. A candidate
generator may return false positives, but it must include every polynomial meeting that threshold;
`CandidateCertificate.toDecoderCertificate` records the target obtained by filtering those
candidates by message degree and actual agreement.

The separation between `messageDim` and `designDim` is intentional. An interpolation or root-finding
algorithm may work in the larger ambient space of polynomials of degree `< designDim`, then filter
back to the target code of degree `< messageDim`. This is the interface needed to repair the
`k`/`K` gap in [BCPZZ26], and it is useful independently of that paper.

These contracts do not contain a running-time claim. Executability and machine-cost bounds are
separate properties of concrete implementations.
-/

namespace ReedSolomon
namespace ListDecoding

open Polynomial

noncomputable section

/-- A Reed–Solomon message polynomial whose degree is strictly smaller than `messageDim`. -/
abbrev MessagePolynomial (F : Type*) [Semiring F] (messageDim : ℕ) :=
  Polynomial.degreeLT F messageDim

/-- A list decoder returning degree-bounded message polynomials. -/
abbrev Decoder (F : Type*) [Semiring F] (ι : Type*) [Fintype ι] (messageDim : ℕ) :=
  (ι → F) → Finset (MessagePolynomial F messageDim)

/-- A decoder is exact at `minAgreement` when it returns precisely the message polynomials whose
Reed–Solomon evaluations agree with the received word in at least `minAgreement` positions. -/
def IsExactDecoder {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (messageDim minAgreement : ℕ)
    (decoder : Decoder F ι messageDim) : Prop :=
  ∀ (received : ι → F) (p : MessagePolynomial F messageDim),
    p ∈ decoder received ↔
      minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received

/-- A certificate packages exact decoder behavior with a uniform output-cardinality bound. It does
not assert that `decoder` is executable or that it meets any running-time bound. -/
structure DecoderCertificate {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (messageDim minAgreement listBound : ℕ) where
  /-- The decoder whose output is being certified. -/
  decoder : Decoder F ι messageDim
  /-- Soundness and completeness of the output list. -/
  isExact : IsExactDecoder domain messageDim minAgreement decoder
  /-- The uniform bound on the output-list cardinality. -/
  card_le : ∀ received, (decoder received).card ≤ listBound

/-- Every polynomial returned by a certified decoder meets its agreement threshold. -/
lemma DecoderCertificate.agreement_le_of_mem {F ι : Type*} [Semiring F] [DecidableEq F]
    [Fintype ι] {domain : ι ↪ F} {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound)
    {received : ι → F} {p : MessagePolynomial F messageDim}
    (hp : p ∈ certificate.decoder received) :
    minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received :=
  (certificate.isExact received p).mp hp

/-- Every degree-bounded polynomial meeting the agreement threshold is returned by a certified
decoder. -/
lemma DecoderCertificate.mem_of_agreement_le {F ι : Type*} [Semiring F] [DecidableEq F]
    [Fintype ι] {domain : ι ↪ F} {messageDim minAgreement listBound : ℕ}
    (certificate : DecoderCertificate domain messageDim minAgreement listBound)
    {received : ι → F} {p : MessagePolynomial F messageDim}
    (hp : minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received) :
    p ∈ certificate.decoder received :=
  (certificate.isExact received p).mpr hp

/-- A certified ambient candidate generator. It may return false positives, but it contains every
degree-`< designDim` polynomial meeting the agreement threshold and has a uniform cardinality
bound. Actual-agreement filtering is deliberately deferred to the final decoder. -/
structure CandidateCertificate {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (designDim minAgreement listBound : ℕ) where
  /-- The ambient candidate generator. -/
  candidates : (ι → F) → Finset (Polynomial F)
  /-- Every sufficiently agreeing ambient polynomial appears in the candidate list. -/
  complete : ∀ (received : ι → F) (p : MessagePolynomial F designDim),
    minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received →
      (p : Polynomial F) ∈ candidates received
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

/-- Filter an ambient candidate list to the target message dimension and actual agreement. -/
def CandidateCertificate.filteredDecoder {F ι : Type*} [Semiring F] [DecidableEq F]
    [Fintype ι] {domain : ι ↪ F} {designDim minAgreement listBound : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (messageDim : ℕ) : Decoder F ι messageDim := fun received =>
  ((certificate.candidates received).preimage (messagePolynomialValue messageDim)
      (messagePolynomialValue messageDim).injective.injOn).filter fun p =>
    minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received

/-- The filtered decoder is sound and complete at every smaller message dimension.

This is a deliberately exposed formalization target: downstream decoder work should refine this
theorem rather than restating the `messageDim`/`designDim` repair. -/
theorem CandidateCertificate.filteredDecoder_isExact {F ι : Type*} [Semiring F]
    [DecidableEq F] [Fintype ι]
    {domain : ι ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (h : messageDim ≤ designDim) :
    IsExactDecoder domain messageDim minAgreement
      (certificate.filteredDecoder messageDim) := by
  sorry

/-- Filtering a candidate list does not increase its cardinality. -/
theorem CandidateCertificate.filteredDecoder_card_le {F ι : Type*} [Semiring F]
    [DecidableEq F] [Fintype ι]
    {domain : ι ↪ F} {designDim minAgreement listBound : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (messageDim : ℕ) :
    ∀ received, (certificate.filteredDecoder messageDim received).card ≤ listBound := by
  sorry

/-- Package the explicitly filtered ambient candidates as an exact decoder certificate. -/
def CandidateCertificate.toDecoderCertificate {F ι : Type*} [Semiring F]
    [DecidableEq F]
    [Fintype ι] {domain : ι ↪ F} {designDim minAgreement listBound messageDim : ℕ}
    (certificate : CandidateCertificate domain designDim minAgreement listBound)
    (h : messageDim ≤ designDim) :
    DecoderCertificate domain messageDim minAgreement listBound where
  decoder := certificate.filteredDecoder messageDim
  isExact := certificate.filteredDecoder_isExact h
  card_le := certificate.filteredDecoder_card_le messageDim

end
end ListDecoding
end ReedSolomon
