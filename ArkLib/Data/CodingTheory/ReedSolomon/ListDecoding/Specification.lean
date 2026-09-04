/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Exact Reed-Solomon list-decoder specifications

This module gives an extensional interface for a Reed-Solomon list decoder. The output is a
`Finset` of polynomials in `Polynomial.degreeLT F k`, so the degree bound and duplicate-freedom are
part of the type. Exactness means that membership is equivalent to meeting an absolute agreement
threshold, measured by the canonical `Code.agree` function.

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
