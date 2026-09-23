/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.PairAgreementBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Reed–Solomon list bounds at gaps of at least one quarter

Pairwise agreement bounds give list-size guarantees for Reed–Solomon codes at large capacity
gaps. At gaps of at least one half, each list has size at most one. At gaps from one quarter to
one half, each list has fewer than `blockLength` polynomials. These bounds specify list sizes and
do not assert an interpolation algorithm or running-time bound.

## Main statements

* `agreeingPolynomials_encard_le_one_of_half`: a half-gap agreement list has size at most one.
* `agreeingPolynomials_encard_lt_blockLength_of_quarter`: a quarter-gap agreement list has fewer
  elements than the block length.
* `quarter_gap_list_bound`: prime-field certificates for all gaps of at least one quarter.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open ListDecoding

noncomputable section

/-- Evaluation on at least `messageDim` distinct points embeds bounded-degree messages into the
Reed–Solomon word space. -/
private def evaluationEmbedding {ι F : Type*} [Field F] [Fintype ι] {messageDim : ℕ}
    (domain : ι ↪ F) (hMessageDim : messageDim ≤ Fintype.card ι) :
    MessagePolynomial F messageDim ↪ (ι → F) where
  toFun p := ReedSolomon.evalOnPoints domain p
  inj' p p' hEvaluation := by
    apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ domain.injective.injOn
    · simpa only [Finset.card_univ] using
        (Polynomial.mem_degreeLT.mp p.2).trans_le (Nat.cast_le.mpr hMessageDim)
    · simpa only [Finset.card_univ] using
        (Polynomial.mem_degreeLT.mp p'.2).trans_le (Nat.cast_le.mpr hMessageDim)
    · intro i _
      exact congrFun hEvaluation i

/-- The finite message-polynomial enumeration induced by its coefficient vectors. -/
@[instance_reducible]
private def messagePolynomialFintype (F : Type*) [Semiring F] [Fintype F]
    (messageDim : ℕ) : Fintype (MessagePolynomial F messageDim) :=
  Fintype.ofEquiv (Fin messageDim → F)
    (Polynomial.degreeLTEquiv F messageDim).toEquiv.symm

/-- The exact decoder retaining precisely the polynomials meeting an agreement threshold. -/
private def exactAgreementDecoder {ι F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] {messageDim minAgreement : ℕ} (domain : ι ↪ F) :
    Decoder F ι messageDim := fun received =>
  letI := messagePolynomialFintype F messageDim
  Finset.univ.filter fun p =>
    minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received

/-- The declarative decoder returns exactly the polynomials with enough agreements. -/
private lemma exactAgreementDecoder_isExact {ι F : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] {messageDim minAgreement : ℕ} (domain : ι ↪ F) :
    IsExactDecoder domain messageDim minAgreement
      (exactAgreementDecoder (minAgreement := minAgreement) domain) := by
  intro received p
  simp [exactAgreementDecoder, Accepts]

/-- The exact decoder inherits the pairwise-agreement product estimate. -/
private theorem exactAgreementDecoder_card_mul_gap_le {ι F : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] {messageDim minAgreement : ℕ} (domain : ι ↪ F)
    (hMessageDim : 0 < messageDim) (hMessageDimLe : messageDim ≤ Fintype.card ι)
    (received : ι → F) :
    ((exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
      domain received).card : ℝ) *
        ((minAgreement : ℝ) ^ 2 -
          (Fintype.card ι : ℝ) * ((messageDim - 1 : ℕ) : ℝ)) ≤
      (Fintype.card ι : ℝ) *
        ((Fintype.card ι : ℝ) - ((messageDim - 1 : ℕ) : ℝ)) := by
  classical
  let embedding := evaluationEmbedding domain hMessageDimLe
  let words := (exactAgreementDecoder (messageDim := messageDim)
    (minAgreement := minAgreement) domain received).map embedding
  have hPairAgreement : messageDim - 1 ≤ Fintype.card ι := by omega
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
    have hpCode : ReedSolomon.evalOnPoints domain p ∈
        ReedSolomon.code domain messageDim :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p.2)
    have hpCode' : ReedSolomon.evalOnPoints domain p' ∈
        ReedSolomon.code domain messageDim :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p'.2)
    have hAgreeLt := ReedSolomon.agree_lt_of_mem_code hpCode hpCode' hne
    have hAgreeLt' : Code.agree (embedding p) (embedding p') < messageDim := by
      change Code.agree (ReedSolomon.evalOnPoints domain p)
        (ReedSolomon.evalOnPoints domain p') < messageDim
      exact hAgreeLt
    omega
  have hBound := Code.card_mul_sq_minAgreement_sub_pairAgreement_le
    received words minAgreement (messageDim - 1) hPairAgreement hClose hPair
  simpa only [words, Finset.card_map] using hBound

/-- Above the half-gap threshold the exact agreement decoder contains at most one polynomial. -/
private theorem exactAgreementDecoder_card_le_one {ι F : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] {messageDim minAgreement : ℕ} (domain : ι ↪ F)
    (hMessageDim : 0 < messageDim) (hMessageDimLe : messageDim ≤ Fintype.card ι)
    (hThreshold : Fintype.card ι + (messageDim - 1) < 2 * minAgreement)
    (received : ι → F) :
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
    have hpCode : ReedSolomon.evalOnPoints domain p ∈
        ReedSolomon.code domain messageDim :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p.2)
    have hpCode' : ReedSolomon.evalOnPoints domain p' ∈
        ReedSolomon.code domain messageDim :=
      ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p'.2)
    have hAgreeLt := ReedSolomon.agree_lt_of_mem_code hpCode hpCode' hne
    have hAgreeLt' : Code.agree (embedding p) (embedding p') < messageDim := by
      change Code.agree (ReedSolomon.evalOnPoints domain p)
        (ReedSolomon.evalOnPoints domain p') < messageDim
      exact hAgreeLt
    omega
  have hBound := Code.card_le_one_of_pairwise_agree_le received words minAgreement
    (messageDim - 1) (by simpa using hThreshold) hClose hPair
  simpa only [words, Finset.card_map] using hBound

/-- The agreement threshold at a quarter gap is at least `k + n / 4`. -/
private lemma agreementThreshold_quarter_gap {delta : ℝ}
    (hdelta : (1 / 4 : ℝ) ≤ delta) (blockLength messageDim : ℕ) :
    (messageDim : ℝ) + (blockLength : ℝ) / 4 ≤
      agreementThreshold delta blockLength messageDim := by
  have hdelta_nonneg : 0 ≤ delta := by positivity
  have hThreshold := (agreementThreshold_le_iff_real hdelta_nonneg blockLength messageDim
    (agreementThreshold delta blockLength messageDim)).mp le_rfl
  have hBlockLengthNonneg : (0 : ℝ) ≤ blockLength := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hdelta hBlockLengthNonneg]

/-- The half-gap threshold makes two degree-bounded candidates agree too often to be distinct. -/
private lemma agreementThreshold_half_gap {delta : ℝ}
    (hdelta : (1 / 2 : ℝ) ≤ delta) (blockLength messageDim : ℕ)
    (hMessageDim : 0 < messageDim) :
    blockLength + (messageDim - 1) <
      2 * agreementThreshold delta blockLength messageDim := by
  have hdelta_nonneg : 0 ≤ delta := by positivity
  have hThreshold := (agreementThreshold_le_iff_real hdelta_nonneg blockLength messageDim
    (agreementThreshold delta blockLength messageDim)).mp le_rfl
  have hBlockLengthNonneg : (0 : ℝ) ≤ blockLength := by positivity
  have hMessageDimSub : ((messageDim - 1 : ℕ) : ℝ) < messageDim := by
    exact_mod_cast Nat.sub_lt hMessageDim (by decide : 0 < 1)
  have hReal : (blockLength : ℝ) + (messageDim - 1 : ℕ) <
      2 * agreementThreshold delta blockLength messageDim := by
    nlinarith [mul_le_mul_of_nonneg_right hdelta hBlockLengthNonneg]
  exact_mod_cast hReal

/-- Constant messages have disjoint agreement sets. -/
private theorem exactAgreementDecoder_card_mul_threshold_le_of_dimension_one
    {ι F : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    {minAgreement : ℕ} (domain : ι ↪ F) (hn : 0 < Fintype.card ι)
    (received : ι → F) :
    (exactAgreementDecoder (messageDim := 1) (minAgreement := minAgreement)
      domain received).card * minAgreement ≤ Fintype.card ι := by
  classical
  let embedding := evaluationEmbedding domain (show 1 ≤ Fintype.card ι by omega)
  let messages := exactAgreementDecoder (messageDim := 1)
    (minAgreement := minAgreement) domain received
  have h := Code.card_mul_minAgreement_le_of_pairwise_agree_eq_zero received
    (messages.map embedding) minAgreement ?_ ?_
  · simpa only [Finset.card_map] using h
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

/-- A quarter-gap decoder list is strictly smaller than the block length. -/
private lemma exactAgreementDecoder_card_lt_blockLength {ι F : Type*} [Field F]
    [Fintype F] [DecidableEq F] [Fintype ι] {delta : ℝ} {messageDim : ℕ}
    (hdelta : (1 / 4 : ℝ) ≤ delta) (domain : ι ↪ F)
    (hBlockLength : 0 < Fintype.card ι) (hMessageDim : 0 < messageDim)
    (hMessageDimLe : messageDim ≤ Fintype.card ι) (received : ι → F) :
    (exactAgreementDecoder (messageDim := messageDim)
      (minAgreement := agreementThreshold delta (Fintype.card ι) messageDim)
      domain received).card < Fintype.card ι := by
  by_cases hdim : messageDim = 1
  · subst messageDim
    have h := exactAgreementDecoder_card_mul_threshold_le_of_dimension_one
      (minAgreement := agreementThreshold delta (Fintype.card ι) 1) domain hBlockLength received
    have ht := agreementThreshold_quarter_gap hdelta (Fintype.card ι) 1
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hBlockLength
    have htwo : 2 ≤ agreementThreshold delta (Fintype.card ι) 1 := by
      have hreal : (1 : ℝ) < agreementThreshold delta (Fintype.card ι) 1 := by
        push_cast at ht
        linarith
      exact_mod_cast hreal
    have hcard := Nat.mul_le_mul_left
      (exactAgreementDecoder (messageDim := 1)
        (minAgreement := agreementThreshold delta (Fintype.card ι) 1)
        domain received).card htwo
    omega
  have hProduct := exactAgreementDecoder_card_mul_gap_le
    (minAgreement := agreementThreshold delta (Fintype.card ι) messageDim)
    domain hMessageDim hMessageDimLe received
  have hThreshold := agreementThreshold_quarter_gap hdelta (Fintype.card ι) messageDim
  have hMessageDimSub : ((messageDim - 1 : ℕ) : ℝ) = messageDim - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ messageDim)]
    norm_num
  have hGap : (Fintype.card ι : ℝ) ≤
      (agreementThreshold delta (Fintype.card ι) messageDim : ℝ) ^ 2 -
        Fintype.card ι * (messageDim - 1 : ℕ) := by
    rw [hMessageDimSub]
    nlinarith [sq_nonneg ((messageDim : ℝ) - (Fintype.card ι : ℝ) / 4)]
  have hBlockLengthReal : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast hBlockLength
  have hGapNonneg : (0 : ℝ) ≤
      (agreementThreshold delta (Fintype.card ι) messageDim : ℝ) ^ 2 -
        Fintype.card ι * (messageDim - 1 : ℕ) :=
    (le_of_lt hBlockLengthReal).trans hGap
  have hDecoderCard :
      ((exactAgreementDecoder (messageDim := messageDim)
        (minAgreement := agreementThreshold delta (Fintype.card ι) messageDim)
        domain received).card : ℝ) < Fintype.card ι := by
    have hMessageSubPos : (0 : ℝ) < (messageDim - 1 : ℕ) := by
      exact_mod_cast (show 0 < messageDim - 1 by omega)
    have hstrict := mul_pos hBlockLengthReal hMessageSubPos
    nlinarith [mul_nonneg (show (0 : ℝ) ≤
      (exactAgreementDecoder (messageDim := messageDim)
        (minAgreement := agreementThreshold delta (Fintype.card ι) messageDim)
        domain received).card by positivity) hGapNonneg]
  exact_mod_cast hDecoderCard

/-- The polynomial agreement set has the cardinality of its exact finite decoder. -/
private lemma exactAgreementDecoder_encard_eq {ι F : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] {messageDim minAgreement : ℕ} (domain : ι ↪ F)
    (received : ι → F) :
    (agreeingPolynomials domain messageDim minAgreement received).encard =
      ((exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
        domain received).card : ℕ∞) := by
  have hSet : agreeingPolynomials domain messageDim minAgreement received =
      (exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
        domain received : Set (MessagePolynomial F messageDim)) := by
    ext p
    simp [agreeingPolynomials, exactAgreementDecoder]
  rw [hSet, Set.encard_coe_eq_coe_finsetCard]

/-- A quarter-gap agreement list has fewer elements than the number of coordinates. -/
theorem agreeingPolynomials_encard_lt_blockLength_of_quarter
    {ι F : Type*} [Field F] [Finite F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} (hdelta : (1 / 4 : ℝ) ≤ delta) {messageDim : ℕ}
    (domain : ι ↪ F) (hBlockLength : 0 < Fintype.card ι) (hMessageDim : 0 < messageDim)
    (hMessageDimLe : messageDim ≤ Fintype.card ι) (received : ι → F) :
    (agreeingPolynomials domain messageDim
      (agreementThreshold delta (Fintype.card ι) messageDim) received).encard <
        (Fintype.card ι : ℕ∞) := by
  let := Fintype.ofFinite F
  rw [exactAgreementDecoder_encard_eq domain received]
  exact_mod_cast exactAgreementDecoder_card_lt_blockLength hdelta domain hBlockLength
    hMessageDim hMessageDimLe received

/-- At a capacity gap of at least one half, every received word has at most one agreeing
degree-bounded polynomial. -/
theorem agreeingPolynomials_encard_le_one_of_half
    {ι F : Type*} [Field F] [Finite F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} (hdelta : (1 / 2 : ℝ) ≤ delta) {messageDim : ℕ}
    (domain : ι ↪ F) (hMessageDim : 0 < messageDim)
    (hMessageDimLe : messageDim ≤ Fintype.card ι) (received : ι → F) :
    (agreeingPolynomials domain messageDim
      (agreementThreshold delta (Fintype.card ι) messageDim) received).encard ≤ 1 := by
  let := Fintype.ofFinite F
  rw [exactAgreementDecoder_encard_eq domain received]
  exact_mod_cast exactAgreementDecoder_card_le_one domain hMessageDim hMessageDimLe
    (agreementThreshold_half_gap hdelta (Fintype.card ι) messageDim hMessageDim) received

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
        domain received).card ≤ blockLength := by
    intro received
    have h := exactAgreementDecoder_card_lt_blockLength hdelta domain
      (by simpa only [Fintype.card_fin] using hBlockLength) hMessageDim
      (by simpa only [Fintype.card_fin] using hMessageDimLe) received
    simpa only [minAgreement, Fintype.card_fin] using h.le
  have hFieldSizePos : 0 < fieldSize := hFieldPrime.pos
  have hCardLeListBound : ∀ received : Fin blockLength → ZMod fieldSize,
      (exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
        domain received).card ≤ listBound := by
    intro received
    by_cases hhalf : (1 / 2 : ℝ) ≤ delta
    · simp only [listBound, ite_eq_left hhalf]
      exact exactAgreementDecoder_card_le_one domain hMessageDim
        (by simpa only [Fintype.card_fin] using hMessageDimLe)
        (by simpa only [minAgreement, Fintype.card_fin] using
          agreementThreshold_half_gap hhalf blockLength messageDim hMessageDim) received
    · simp only [listBound, ite_eq_right hhalf]
      exact (hCardLeBlockLength received).trans <| by omega
  let decoderCertificate : DecoderCertificate domain messageDim minAgreement listBound := {
    enumerate := exactAgreementDecoder (minAgreement := minAgreement) domain
    isExact := hDecoderExact
    card_le := hCardLeListBound }
  have hPointwise : ∀ received : Fin blockLength → ZMod fieldSize,
      (agreeingPolynomials domain messageDim minAgreement received).encard ≤
        (listBound : ℕ∞) := by
    intro received
    rw [exactAgreementDecoder_encard_eq domain received]
    exact_mod_cast hCardLeListBound received
  have hCertificate : CapacityGapCertificate delta domain messageDim listBound :=
    CapacityGapCertificate.ofDecoderCertificateAndPointwiseBound hdelta_nonneg
      (by simpa only [Fintype.card_fin] using hBlockLength)
      (by simpa only [minAgreement, Fintype.card_fin] using decoderCertificate)
      (by simpa only [minAgreement, Fintype.card_fin] using hPointwise)
  refine ⟨⟨hCertificate⟩, ?_⟩
  intro hdelta_lt_half received
  rw [exactAgreementDecoder_encard_eq domain received]
  exact_mod_cast lt_of_le_of_lt (hCardLeBlockLength received)
    (by omega : blockLength < 4 * fieldSize)

end
end ReedSolomon
