/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.PairAgreementBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Radius
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability
public import Mathlib.Algebra.Field.ZMod

/-!
# Reed-Solomon list bounds at gaps of at least one quarter

This module proves the large-gap list bounds of [DKTZ26] by elementary agreement counting:
distinct degree-`< k` Reed--Solomon words
agree in at most `k - 1` positions, and the exact Cauchy--Schwarz estimate from
`Code.card_mul_sq_minAgreement_sub_pairAgreement_le` bounds every finite high-agreement family.

For gaps at least one half, two candidates would agree in at least `k` positions and hence the list
has size at most one. For gaps between one quarter and one half, the identity

`(k + n / 4)^2 - n * (k - 1) = (k - n / 4)^2 + n`

gives list size at most `n - k + 1`, which is strictly less than `n` when `k ≥ 2`.
For `k = 1`, distinct constant messages have disjoint agreement sets and the threshold is at
least two, again giving strictly fewer than `n` candidates. This declarative proof supplies no
interpolation algorithm or running-time claim.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Theorem 1.1 and Section 4.1 (large-gap list bounds).
  The elementary counting proof here differs from the order-zero interpolation route of
  Theorem 3.5.
-/

@[expose] public section

namespace ReedSolomon

open ListDecoding

noncomputable section

/-- Evaluation on at least `messageDim` distinct points embeds the bounded-degree message space
into the Reed--Solomon word space. -/
private def evaluationEmbedding {F : Type*} [Field F] {blockLength messageDim : ℕ}
    (domain : Fin blockLength ↪ F) (hMessageDim : messageDim ≤ blockLength) :
    MessagePolynomial F messageDim ↪ (Fin blockLength → F) where
  toFun p := ReedSolomon.evalOnPoints domain p
  inj' p p' hEvaluation := by
    apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ domain.injective.injOn
    · simpa only [Finset.card_univ, Fintype.card_fin] using
        (Polynomial.mem_degreeLT.mp p.2).trans_le (Nat.cast_le.mpr hMessageDim)
    · simpa only [Finset.card_univ, Fintype.card_fin] using
        (Polynomial.mem_degreeLT.mp p'.2).trans_le (Nat.cast_le.mpr hMessageDim)
    · intro i _
      exact congrFun hEvaluation i

/-- The declarative exact decoder used by the order-zero certificate. It enumerates the finite
message space and retains precisely the polynomials meeting the agreement threshold. -/
@[instance_reducible]
private def messagePolynomialFintype (F : Type*) [Semiring F] [Fintype F]
    (messageDim : ℕ) : Fintype (MessagePolynomial F messageDim) :=
  Fintype.ofEquiv (Fin messageDim → F)
    (Polynomial.degreeLTEquiv F messageDim).toEquiv.symm

private def exactAgreementDecoder {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {blockLength messageDim minAgreement : ℕ} (domain : Fin blockLength ↪ F) :
    Decoder F (Fin blockLength) messageDim := fun received =>
  letI := messagePolynomialFintype F messageDim
  Finset.univ.filter fun p =>
    minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received

private lemma exactAgreementDecoder_isExact {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {blockLength messageDim minAgreement : ℕ} (domain : Fin blockLength ↪ F) :
    IsExactDecoder domain messageDim minAgreement
      (exactAgreementDecoder (minAgreement := minAgreement) domain) := by
  intro received p
  simp [exactAgreementDecoder]

/-- The exact finite decoder inherits the sharp product estimate from pairwise Reed--Solomon
agreement. This bound is shared by both low-order cases. -/
private theorem exactAgreementDecoder_card_mul_gap_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {blockLength messageDim minAgreement : ℕ} (domain : Fin blockLength ↪ F)
    (hMessageDim : 0 < messageDim) (hMessageDimLe : messageDim ≤ blockLength)
    (received : Fin blockLength → F) :
    ((exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
      domain received).card : ℝ) *
        ((minAgreement : ℝ) ^ 2 -
          (blockLength : ℝ) * ((messageDim - 1 : ℕ) : ℝ)) ≤
      (blockLength : ℝ) *
        ((blockLength : ℝ) - ((messageDim - 1 : ℕ) : ℝ)) := by
  classical
  let embedding := evaluationEmbedding domain hMessageDimLe
  let words := (exactAgreementDecoder (messageDim := messageDim)
    (minAgreement := minAgreement) domain received).map embedding
  have hPairAgreement : messageDim - 1 ≤ Fintype.card (Fin blockLength) := by
    simpa only [Fintype.card_fin] using (Nat.sub_le messageDim 1).trans hMessageDimLe
  have hClose : ∀ word ∈ words, minAgreement ≤ Code.agree word received := by
    intro word hword
    rw [Finset.mem_map] at hword
    obtain ⟨p, hp, rfl⟩ := hword
    exact (exactAgreementDecoder_isExact domain received p).mp hp
  have hPair : ∀ word ∈ words, ∀ word' ∈ words, word ≠ word' →
      Code.agree word word' ≤ messageDim - 1 := by
    intro word hword word' hword' hne
    rw [Finset.mem_map] at hword hword'
    obtain ⟨p, hp, rfl⟩ := hword
    obtain ⟨p', hp', rfl⟩ := hword'
    have hpCode : ReedSolomon.evalOnPoints domain p ∈ ReedSolomon.code domain messageDim :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p.2)
    have hpCode' : ReedSolomon.evalOnPoints domain p' ∈ ReedSolomon.code domain messageDim :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p'.2)
    have hAgreeLt := ReedSolomon.agree_lt_of_mem_code hpCode hpCode' hne
    have hAgreeLt' : Code.agree (embedding p) (embedding p') < messageDim := by
      change Code.agree (ReedSolomon.evalOnPoints domain p)
        (ReedSolomon.evalOnPoints domain p') < messageDim
      exact hAgreeLt
    omega
  have hBound := Code.card_mul_sq_minAgreement_sub_pairAgreement_le
    received words minAgreement (messageDim - 1) hPairAgreement hClose hPair
  simpa only [words, Finset.card_map, Fintype.card_fin] using hBound

/-- Above the half-gap threshold the exact agreement decoder contains at most one polynomial. -/
private theorem exactAgreementDecoder_card_le_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {blockLength messageDim minAgreement : ℕ} (domain : Fin blockLength ↪ F)
    (hMessageDim : 0 < messageDim) (hMessageDimLe : messageDim ≤ blockLength)
    (hThreshold : blockLength + (messageDim - 1) < 2 * minAgreement)
    (received : Fin blockLength → F) :
    (exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
      domain received).card ≤ 1 := by
  classical
  let embedding := evaluationEmbedding domain hMessageDimLe
  let words := (exactAgreementDecoder (messageDim := messageDim)
    (minAgreement := minAgreement) domain received).map embedding
  have hClose : ∀ word ∈ words, minAgreement ≤ Code.agree word received := by
    intro word hword
    rw [Finset.mem_map] at hword
    obtain ⟨p, hp, rfl⟩ := hword
    exact (exactAgreementDecoder_isExact domain received p).mp hp
  have hPair : ∀ word ∈ words, ∀ word' ∈ words, word ≠ word' →
      Code.agree word word' ≤ messageDim - 1 := by
    intro word hword word' hword' hne
    rw [Finset.mem_map] at hword hword'
    obtain ⟨p, hp, rfl⟩ := hword
    obtain ⟨p', hp', rfl⟩ := hword'
    have hpCode : ReedSolomon.evalOnPoints domain p ∈ ReedSolomon.code domain messageDim :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p.2)
    have hpCode' : ReedSolomon.evalOnPoints domain p' ∈ ReedSolomon.code domain messageDim :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p'.2)
    have hAgreeLt := ReedSolomon.agree_lt_of_mem_code hpCode hpCode' hne
    have hAgreeLt' : Code.agree (embedding p) (embedding p') < messageDim := by
      change Code.agree (ReedSolomon.evalOnPoints domain p)
        (ReedSolomon.evalOnPoints domain p') < messageDim
      exact hAgreeLt
    omega
  have hBound := Code.card_le_one_of_pairwise_agree_le received words minAgreement
    (messageDim - 1) (by simpa only [Fintype.card_fin] using hThreshold) hClose hPair
  simpa only [words, Finset.card_map] using hBound

private lemma agreementThreshold_quarter_gap
    {delta : ℝ} (hdelta : (1 / 4 : ℝ) ≤ delta)
    (blockLength messageDim : ℕ) :
    (messageDim : ℝ) + (blockLength : ℝ) / 4 ≤
      agreementThreshold delta blockLength messageDim := by
  have hdelta_nonneg : 0 ≤ delta := by positivity
  have hThreshold := (agreementThreshold_le_iff_real hdelta_nonneg blockLength messageDim
    (agreementThreshold delta blockLength messageDim)).mp le_rfl
  have hBlockLengthNonneg : (0 : ℝ) ≤ blockLength := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hdelta hBlockLengthNonneg]

private lemma agreementThreshold_half_gap
    {delta : ℝ} (hdelta : (1 / 2 : ℝ) ≤ delta)
    (blockLength messageDim : ℕ) (hMessageDim : 0 < messageDim) :
    blockLength + (messageDim - 1) <
      2 * agreementThreshold delta blockLength messageDim := by
  have hdelta_nonneg : 0 ≤ delta := by positivity
  have hThreshold := (agreementThreshold_le_iff_real hdelta_nonneg blockLength messageDim
    (agreementThreshold delta blockLength messageDim)).mp le_rfl
  have hBlockLengthNonneg : (0 : ℝ) ≤ blockLength := by positivity
  have hMessageDimSub : ((messageDim - 1 : ℕ) : ℝ) < messageDim := by
    exact_mod_cast Nat.sub_lt hMessageDim (by decide : 0 < 1)
  have hReal :
      (blockLength : ℝ) + (messageDim - 1 : ℕ) <
        2 * agreementThreshold delta blockLength messageDim := by
    nlinarith [mul_le_mul_of_nonneg_right hdelta hBlockLengthNonneg]
  exact_mod_cast hReal

/-- Constant messages have disjoint agreement sets, including over arbitrary finite fields. -/
private theorem exactAgreementDecoder_card_mul_threshold_le_of_dimension_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {blockLength minAgreement : ℕ} (domain : Fin blockLength ↪ F)
    (hn : 0 < blockLength) (received : Fin blockLength → F) :
    (exactAgreementDecoder (messageDim := 1) (minAgreement := minAgreement)
      domain received).card * minAgreement ≤ blockLength := by
  classical
  let embedding := evaluationEmbedding domain (show 1 ≤ blockLength by omega)
  let messages := exactAgreementDecoder (messageDim := 1)
    (minAgreement := minAgreement) domain received
  have h := Code.card_mul_minAgreement_le_of_pairwise_agree_eq_zero received
    (messages.map embedding) minAgreement ?_ ?_
  · simpa only [Finset.card_map, Fintype.card_fin] using h
  · intro word hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hw
    exact (exactAgreementDecoder_isExact domain received p).mp hp
  · intro word hw word' hw' hne
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hw'
    have hlt := ReedSolomon.agree_lt_of_mem_code
      (ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p.2))
      (ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p'.2)) hne
    change Code.agree (embedding p) (embedding p') < 1 at hlt
    omega

private lemma exactAgreementDecoder_card_lt_blockLength
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {delta : ℝ} (hdelta : (1 / 4 : ℝ) ≤ delta)
    {blockLength messageDim : ℕ} (domain : Fin blockLength ↪ F)
    (hBlockLength : 0 < blockLength) (hMessageDim : 0 < messageDim)
    (hMessageDimLe : messageDim ≤ blockLength) (received : Fin blockLength → F) :
    (exactAgreementDecoder (messageDim := messageDim)
      (minAgreement := agreementThreshold delta blockLength messageDim)
      domain received).card < blockLength := by
  by_cases hdim : messageDim = 1
  · subst messageDim
    have h := exactAgreementDecoder_card_mul_threshold_le_of_dimension_one
      (minAgreement := agreementThreshold delta blockLength 1) domain hBlockLength received
    have ht := agreementThreshold_quarter_gap hdelta blockLength 1
    have hn : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
    have htwo : 2 ≤ agreementThreshold delta blockLength 1 := by
      have hreal : (1 : ℝ) < agreementThreshold delta blockLength 1 := by
        push_cast at ht
        linarith
      exact_mod_cast hreal
    have hcard := Nat.mul_le_mul_left
      (exactAgreementDecoder (messageDim := 1)
        (minAgreement := agreementThreshold delta blockLength 1) domain received).card htwo
    omega
  have hProduct := exactAgreementDecoder_card_mul_gap_le
    (minAgreement := agreementThreshold delta blockLength messageDim)
    domain hMessageDim hMessageDimLe received
  have hThreshold := agreementThreshold_quarter_gap hdelta blockLength messageDim
  have hMessageDimSub : ((messageDim - 1 : ℕ) : ℝ) = messageDim - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ messageDim)]
    norm_num
  have hGap : (blockLength : ℝ) ≤
      (agreementThreshold delta blockLength messageDim : ℝ) ^ 2 -
        blockLength * (messageDim - 1 : ℕ) := by
    rw [hMessageDimSub]
    nlinarith [sq_nonneg ((messageDim : ℝ) - (blockLength : ℝ) / 4)]
  have hBlockLengthReal : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  have hGapNonneg : (0 : ℝ) ≤
      (agreementThreshold delta blockLength messageDim : ℝ) ^ 2 -
        blockLength * (messageDim - 1 : ℕ) :=
    (le_of_lt hBlockLengthReal).trans hGap
  have hDecoderCard :
      ((exactAgreementDecoder (messageDim := messageDim)
        (minAgreement := agreementThreshold delta blockLength messageDim)
        domain received).card : ℝ) < blockLength := by
    have hMessageSubPos : (0 : ℝ) < (messageDim - 1 : ℕ) := by
      exact_mod_cast (show 0 < messageDim - 1 by omega)
    have hstrict := mul_pos hBlockLengthReal hMessageSubPos
    nlinarith [mul_nonneg (show (0 : ℝ) ≤
      (exactAgreementDecoder (messageDim := messageDim)
        (minAgreement := agreementThreshold delta blockLength messageDim)
        domain received).card by positivity) hGapNonneg]
  exact_mod_cast hDecoderCard

private lemma exactAgreementDecoder_encard_eq
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {blockLength messageDim minAgreement : ℕ} (domain : Fin blockLength ↪ F)
    (received : Fin blockLength → F) :
    (agreeingPolynomials domain messageDim minAgreement received).encard =
      ((exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
        domain received).card : ℕ∞) := by
  have hSet : agreeingPolynomials domain messageDim minAgreement received =
      (exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
        domain received : Set (MessagePolynomial F messageDim)) := by
    ext p
    simp [agreeingPolynomials, exactAgreementDecoder]
  rw [hSet, Set.encard_coe_eq_coe_finsetCard]

/-- At a capacity gap of at least one quarter, every received word has fewer than `blockLength`
agreeing degree-bounded polynomials. -/
theorem agreeingPolynomials_encard_lt_blockLength_of_quarter
    {F : Type*} [Field F] [Finite F] [DecidableEq F]
    {delta : ℝ} (hdelta : (1 / 4 : ℝ) ≤ delta)
    {blockLength messageDim : ℕ} (domain : Fin blockLength ↪ F)
    (hBlockLength : 0 < blockLength) (hMessageDim : 0 < messageDim)
    (hMessageDimLe : messageDim ≤ blockLength) (received : Fin blockLength → F) :
    (agreeingPolynomials domain messageDim
      (agreementThreshold delta blockLength messageDim) received).encard <
        (blockLength : ℕ∞) := by
  let := Fintype.ofFinite F
  rw [exactAgreementDecoder_encard_eq domain received]
  exact_mod_cast exactAgreementDecoder_card_lt_blockLength hdelta domain hBlockLength
    hMessageDim hMessageDimLe received

/-- At a capacity gap of at least one half, every received word has at most one agreeing
degree-bounded polynomial. -/
theorem agreeingPolynomials_encard_le_one_of_half
    {F : Type*} [Field F] [Finite F] [DecidableEq F]
    {delta : ℝ} (hdelta : (1 / 2 : ℝ) ≤ delta)
    {blockLength messageDim : ℕ} (domain : Fin blockLength ↪ F)
    (hMessageDim : 0 < messageDim) (hMessageDimLe : messageDim ≤ blockLength)
    (received : Fin blockLength → F) :
    (agreeingPolynomials domain messageDim
      (agreementThreshold delta blockLength messageDim) received).encard ≤ 1 := by
  let := Fintype.ofFinite F
  rw [exactAgreementDecoder_encard_eq domain received]
  exact_mod_cast exactAgreementDecoder_card_le_one domain hMessageDim hMessageDimLe
    (agreementThreshold_half_gap hdelta blockLength messageDim hMessageDim) received

/-- Unique decoding from a half-gap and a strict `< 4q` list bound from a quarter-gap. -/
theorem quarter_gap_list_bound : QuarterGapListBound := by
  intro delta hdelta hdelta_lt_one
  refine ⟨0, ?_⟩
  intro blockLength messageDim fieldSize _ hMessageDim hMessageDimLe hFieldPrime
    hBlockLengthLe domain
  let _ : Fact fieldSize.Prime := ⟨hFieldPrime⟩
  have hBlockLength : 0 < blockLength := lt_of_lt_of_le hMessageDim hMessageDimLe
  have hdelta_nonneg : 0 ≤ delta := by positivity
  let minAgreement := agreementThreshold delta blockLength messageDim
  let listBound := if (1 / 2 : ℝ) ≤ delta then 1 else 4 * fieldSize
  have hDecoderExact : IsExactDecoder domain messageDim minAgreement
      (exactAgreementDecoder (minAgreement := minAgreement) domain) :=
    exactAgreementDecoder_isExact domain
  have hCardLeBlockLength : ∀ received : Fin blockLength → ZMod fieldSize,
      (exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
        domain received).card ≤ blockLength :=
    fun received => (exactAgreementDecoder_card_lt_blockLength hdelta domain hBlockLength
      hMessageDim hMessageDimLe received).le
  have hFieldSizePos : 0 < fieldSize := hFieldPrime.pos
  have hCardLeListBound : ∀ received : Fin blockLength → ZMod fieldSize,
      (exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
        domain received).card ≤ listBound := by
    intro received
    by_cases hhalf : (1 / 2 : ℝ) ≤ delta
    · simp only [listBound, if_pos hhalf]
      exact exactAgreementDecoder_card_le_one domain hMessageDim hMessageDimLe
        (by simpa only [minAgreement] using
          agreementThreshold_half_gap hhalf blockLength messageDim hMessageDim) received
    · simp only [listBound, if_neg hhalf]
      exact (hCardLeBlockLength received).trans <| by omega
  let decoderCertificate : DecoderCertificate domain messageDim minAgreement listBound := {
    decoder := exactAgreementDecoder (minAgreement := minAgreement) domain
    isExact := hDecoderExact
    card_le := hCardLeListBound }
  have hPointwise : ∀ received : Fin blockLength → ZMod fieldSize,
      (agreeingPolynomials domain messageDim minAgreement received).encard ≤
        (listBound : ℕ∞) := by
    intro received
    rw [exactAgreementDecoder_encard_eq domain received]
    exact_mod_cast hCardLeListBound received
  have hCertificate : CapacityGapCertificate delta domain messageDim listBound :=
    CapacityGapCertificate.ofDecoderCertificateAndPointwiseBound hdelta_nonneg hBlockLength
      domain decoderCertificate (by simpa only [minAgreement] using hPointwise)
  refine ⟨⟨hCertificate⟩, ?_⟩
  intro hdelta_lt_half received
  rw [exactAgreementDecoder_encard_eq domain received]
  exact_mod_cast lt_of_le_of_lt (hCardLeBlockLength received)
    (by omega : blockLength < 4 * fieldSize)

end
end ReedSolomon
