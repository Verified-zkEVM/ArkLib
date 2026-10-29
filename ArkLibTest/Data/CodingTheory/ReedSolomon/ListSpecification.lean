/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListSpecification

/-!
# Exact-list specification acceptance tests

An impossible agreement threshold gives a complete empty ambient candidate generator. Filtering
it exercises the public certificate constructors and produces the exact empty decoder.
-/

namespace ReedSolomon.ListDecoding

private noncomputable def impossibleCandidateCertificate
    {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (designDim : ℕ) :
    CandidateCertificate domain designDim (Fintype.card index + 1) 0 where
  candidates := fun _ ↦ ∅
  complete := by
    intro received p _ hp
    exact ((Nat.not_succ_le_self _)
      (hp.trans Code.agree_le_card)).elim
  card_le := by simp

example {F index : Type*} [Semiring F] [DecidableEq F] [Fintype index]
    (domain : index ↪ F) (messageDim designDim : ℕ) (h : messageDim ≤ designDim) :
    ∃ certificate : DecoderCertificate domain messageDim (Fintype.card index + 1) 0,
      ∀ received, certificate.decoder received = ∅ := by
  let certificate := (impossibleCandidateCertificate domain designDim).toDecoderCertificate h
  refine ⟨certificate, fun received ↦ ?_⟩
  exact certificate.decoder_eq_empty_of_card_lt (by omega) received

end ReedSolomon.ListDecoding
