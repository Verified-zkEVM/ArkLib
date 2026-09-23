/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.PairAgreementBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
import ArkLib.Data.CodingTheory.JohnsonBound.Pairwise
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

private lemma agreeingPolynomials_encard_le_Lambda {ι F : Type*} [Field F]
    [DecidableEq F] [Fintype ι] {messageDim minAgreement : ℕ}
    (domain : ι ↪ F) (hMessageDimLe : messageDim ≤ Fintype.card ι)
    (received : ι → F) :
    (agreeingPolynomials domain messageDim minAgreement received).encard ≤
      Code.Lambda (ReedSolomon.code domain messageDim : Set (ι → F))
        (1 - (minAgreement : ℝ) / Fintype.card ι) := by
  let embedding := evaluationEmbedding domain hMessageDimLe
  have h := Code.encard_setOf_le_agree_encode_le_Lambda
    (ReedSolomon.code domain messageDim : Set (ι → F)) received minAgreement
    (encode := fun p : MessagePolynomial F messageDim =>
      ReedSolomon.evalOnPoints domain p) (S := Set.univ) (by
      intro p _ q _ heval
      exact embedding.injective heval) (by
      intro p _
      exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt (Polynomial.mem_degreeLT.mp p.2))
  simpa [agreeingPolynomials] using h

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

/-- The agreement threshold at a quarter gap is at least `k + n / 4`. -/
private lemma agreementThreshold_quarter_gap {delta : ℝ}
    (hdelta : (1 / 4 : ℝ) ≤ delta) (blockLength messageDim : ℕ) :
    (messageDim : ℝ) + (blockLength : ℝ) / 4 ≤
      agreementThreshold delta blockLength messageDim := by
  have hThreshold := (agreementThreshold_le_iff_real (by positivity) blockLength messageDim
    (agreementThreshold delta blockLength messageDim)).mp le_rfl
  nlinarith [mul_le_mul_of_nonneg_right hdelta
    (by positivity : (0 : ℝ) ≤ blockLength)]

private lemma pairwiseJohnsonListBound_quarter_gap_arithmetic {n messageDim A : ℕ}
    (hn : 0 < n) (hMessageDim : 0 < messageDim) (hMessageDimLe : messageDim ≤ n)
    (hMessageDimLeA : messageDim ≤ A)
    (hA : (messageDim : ℝ) + (n : ℝ) / 4 ≤ A) :
    n * (messageDim - 1) < A * A ∧
      0 < A * A - n * (messageDim - 1) ∧
      Code.pairwiseJohnsonListBound n (messageDim - 1) A < n := by
  let D := messageDim - 1
  have hDcast : (D : ℝ) = (messageDim : ℝ) - 1 := by
    norm_num [D, Nat.cast_sub (by omega : 1 ≤ messageDim)]
  have hGapReal : (n : ℝ) + (n : ℝ) * D ≤ (A : ℝ) * A := by
    rw [hDcast]; nlinarith [sq_nonneg ((messageDim : ℝ) - (n : ℝ) / 4)]
  have hGap : n + n * D ≤ A * A := by exact_mod_cast hGapReal
  have hpositive : n * D < A * A := by omega
  have hDenPos : 0 < A * A - n * D := Nat.sub_pos_of_lt hpositive
  have hNumLt : A - D < A * A - n * D := by
    by_cases hDZero : D = 0
    · have hAReal : 2 ≤ (A : ℝ) := by
        have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hkReal : (1 : ℝ) ≤ messageDim := by exact_mod_cast hMessageDim
        have hAgtReal : (1 : ℝ) < A := by nlinarith [hA]
        have hAgtNat : 1 < A := by exact_mod_cast hAgtReal
        have hANat : 2 ≤ A := by omega
        exact_mod_cast hANat
      have hANat : 2 ≤ A := by exact_mod_cast hAReal
      have hARealStrict : (A : ℝ) < (A : ℝ) * A := by nlinarith
      have hANatStrict : A < A * A := by exact_mod_cast hARealStrict
      simpa [hDZero] using hANatStrict
    · have hDPos : 0 < D := Nat.pos_of_ne_zero hDZero
      by_cases hAle : A ≤ n
      · have hADLt : A - D < n := by omega
        exact hADLt.trans_le (by omega)
      · have hAn : n + 1 ≤ A := by omega
        have hDn : D ≤ n - 1 := by omega
        have hMon : 0 ≤ ((A : ℝ) - (n + 1)) * ((A : ℝ) + n) :=
          mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hAn)) (by positivity)
        have hDproduct : (D : ℝ) * ((n : ℝ) - 1) ≤ ((n : ℝ) - 1) ^ 2 := by
          have hDnReal : (D : ℝ) ≤ (n : ℝ) - 1 := by
            have hDplus : D + 1 ≤ n := by omega
            have hDplusReal : (D : ℝ) + 1 ≤ n := by exact_mod_cast hDplus
            linarith
          have hnOneReal : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
          calc
            (D : ℝ) * ((n : ℝ) - 1) ≤ ((n : ℝ) - 1) * ((n : ℝ) - 1) :=
              mul_le_mul_of_nonneg_right hDnReal (sub_nonneg.mpr hnOneReal)
            _ = ((n : ℝ) - 1) ^ 2 := by ring
        have hStrictReal : (A : ℝ) - D < (A : ℝ) ^ 2 - (n : ℝ) * D := by
          have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
          nlinarith [hMon, hDproduct]
        have hDA : D ≤ A := (Nat.sub_le _ _).trans hMessageDimLeA
        have hStrictCast : ((A - D : ℕ) : ℝ) < (A * A - n * D : ℕ) := by
          rw [Nat.cast_sub hDA, Nat.cast_sub (Nat.le_of_lt hpositive)]
          push_cast
          nlinarith [hStrictReal]
        exact_mod_cast hStrictCast
  refine ⟨hpositive, hDenPos, ?_⟩
  rw [Code.pairwiseJohnsonListBound, Nat.div_lt_iff_lt_mul hDenPos]
  exact Nat.mul_lt_mul_of_pos_left hNumLt hn

private lemma agreeingPolynomials_encard_le_pairwiseJohnson_of_quarter
    {ι F : Type*} [Field F] [DecidableEq F] [Fintype ι] {delta : ℝ}
    (hdelta : (1 / 4 : ℝ) ≤ delta) {messageDim : ℕ}
    (domain : ι ↪ F) (hMessageDim : 0 < messageDim)
    (hMessageDimLe : messageDim ≤ Fintype.card ι) (received : ι → F) :
    (agreeingPolynomials domain messageDim
      (agreementThreshold delta (Fintype.card ι) messageDim) received).encard ≤
        (Code.pairwiseJohnsonListBound (Fintype.card ι) (messageDim - 1)
          (agreementThreshold delta (Fintype.card ι) messageDim) : ℕ∞) := by
  let n := Fintype.card ι
  let D := messageDim - 1
  let A := agreementThreshold delta n messageDim
  let C : Set (ι → F) := ReedSolomon.code domain messageDim
  have hn : 0 < n := lt_of_lt_of_le hMessageDim hMessageDimLe
  have hNonempty : Nonempty ι := Fintype.card_pos_iff.mp hn
  have hA : messageDim ≤ A := by simp [A, agreementThreshold]
  have hDA : D ≤ A := (Nat.sub_le _ _).trans hA
  have hThreshold := agreementThreshold_quarter_gap hdelta n messageDim
  have hArithmetic := pairwiseJohnsonListBound_quarter_gap_arithmetic hn hMessageDim
    hMessageDimLe hA hThreshold
  have hpositive := hArithmetic.1
  have hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → Code.agree c c' ≤ D := by
    intro c hc c' hc' hne
    have := ReedSolomon.agree_lt_of_mem_code hc hc' hne; omega
  have hList := agreeingPolynomials_encard_le_Lambda (minAgreement := A)
    domain hMessageDimLe received
  have hJohnson := @Code.Lambda_le_pairwiseJohnson ι F inferInstance hNonempty inferInstance
    C D A hDA hpositive hpair
  simpa only [n, D, A, C] using hList.trans hJohnson

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
    {ι F : Type*} [Field F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} (hdelta : (1 / 4 : ℝ) ≤ delta) {messageDim : ℕ}
    (domain : ι ↪ F) (hMessageDim : 0 < messageDim)
    (hMessageDimLe : messageDim ≤ Fintype.card ι) (received : ι → F) :
    (agreeingPolynomials domain messageDim
      (agreementThreshold delta (Fintype.card ι) messageDim) received).encard <
        (Fintype.card ι : ℕ∞) := by
  have hA := agreementThreshold_quarter_gap hdelta (Fintype.card ι) messageDim
  have hList := agreeingPolynomials_encard_le_pairwiseJohnson_of_quarter hdelta domain
    hMessageDim hMessageDimLe received
  have hArithmetic := pairwiseJohnsonListBound_quarter_gap_arithmetic
    (lt_of_lt_of_le hMessageDim hMessageDimLe) hMessageDim hMessageDimLe
    (by simp [agreementThreshold]) hA
  have hJohnson := hArithmetic.2.2
  have hJohnsonStrict :
      (Code.pairwiseJohnsonListBound (Fintype.card ι) (messageDim - 1)
        (agreementThreshold delta (Fintype.card ι) messageDim) : ℕ∞) <
        (Fintype.card ι : ℕ∞) := by
    exact_mod_cast hJohnson
  exact hList.trans_lt hJohnsonStrict

/-- At a capacity gap of at least one half, every received word has at most one agreeing
degree-bounded polynomial. -/
theorem agreeingPolynomials_encard_le_one_of_half
    {ι F : Type*} [Field F] [DecidableEq F] [Fintype ι]
    {delta : ℝ} (hdelta : (1 / 2 : ℝ) ≤ delta) {messageDim : ℕ}
    (domain : ι ↪ F) (hMessageDim : 0 < messageDim)
    (hMessageDimLe : messageDim ≤ Fintype.card ι) (received : ι → F) :
    (agreeingPolynomials domain messageDim
      (agreementThreshold delta (Fintype.card ι) messageDim) received).encard ≤ 1 := by
  let C : Set (ι → F) := ReedSolomon.code domain messageDim
  have hNeZero : NeZero messageDim := ⟨Nat.ne_of_gt hMessageDim⟩
  have hn : 0 < Fintype.card ι := lt_of_lt_of_le hMessageDim hMessageDimLe
  have hnReal : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hRateLeNN : ((messageDim : NNReal) / (Fintype.card ι : NNReal)) ≤ 1 := by
    rw [div_le_one₀ (by positivity)]
    exact_mod_cast hMessageDimLe
  have hRadius : capacityRadius delta (Fintype.card ι) messageDim ≤
      (Code.relativeUniqueDecodingRadius (C := C) : ℝ) := by
    rw [@ReedSolomon.relativeUniqueDecodingRadius_RS_eq F ι messageDim inferInstance domain
      inferInstance inferInstance hNeZero hMessageDimLe]
    push_cast
    rw [NNReal.coe_sub hRateLeNN]
    unfold capacityRadius
    have hRateNonneg : (0 : ℝ) ≤ (messageDim : ℝ) / Fintype.card ι := by positivity
    have hTwoDelta : (1 : ℝ) ≤ 2 * delta := by
      calc
        1 = 2 * (1 / 2 : ℝ) := by norm_num
        _ ≤ 2 * delta := mul_le_mul_of_nonneg_left hdelta (by norm_num)
    have hRateDelta : 1 ≤ (messageDim : ℝ) / Fintype.card ι + 2 * delta := by
      linarith [hRateNonneg, hTwoDelta]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc
      (1 - (messageDim : ℝ) / Fintype.card ι - delta) * 2 =
          2 - 2 * ((messageDim : ℝ) / Fintype.card ι) - 2 * delta := by ring
      _ ≤ 1 - (messageDim : ℝ) / Fintype.card ι := by linarith [hRateDelta]
  have hUnique := Code.isUniquelyDecodable_relativeUniqueDecodingRadius C
  have hUniqueLambda : Code.Lambda C (Code.relativeUniqueDecodingRadius C : ℝ) ≤ 1 :=
    Code.isUniquelyDecodable_iff_Lambda_le.mp hUnique
  have hLambda : Code.Lambda C (capacityRadius delta (Fintype.card ι) messageDim) ≤ 1 :=
    (Code.Lambda_mono hRadius).trans hUniqueLambda
  have hdelta_nonneg : 0 ≤ delta := le_trans (by norm_num) hdelta
  have hImage := closeCodewordsRel_eq_eval_image_agreeingPolynomials hdelta_nonneg
    (messageDim := messageDim) hn domain received
  let evaluation : MessagePolynomial F messageDim → ι → F :=
    fun p => ReedSolomon.evalOnPoints domain p
  have hEvaluationInjective : Function.Injective evaluation :=
    (evaluationEmbedding domain hMessageDimLe).injective
  have hList :
      (agreeingPolynomials domain messageDim
        (agreementThreshold delta (Fintype.card ι) messageDim) received).encard ≤
        Code.Lambda C (capacityRadius delta (Fintype.card ι) messageDim) := by
    rw [← hEvaluationInjective.encard_image
      (agreeingPolynomials domain messageDim
        (agreementThreshold delta (Fintype.card ι) messageDim) received), ← hImage]
    exact Code.encard_closeCodewordsRel_le_Lambda C _ received
  exact hList.trans hLambda

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
  have hFieldSizePos : 0 < fieldSize := hFieldPrime.pos
  have hQuarterEnc : ∀ received : Fin blockLength → ZMod fieldSize,
      (agreeingPolynomials domain messageDim minAgreement received).encard <
        (blockLength : ℕ∞) := by
    intro received
    simpa only [minAgreement, Fintype.card_fin] using
      agreeingPolynomials_encard_lt_blockLength_of_quarter hdelta domain
        hMessageDim (by simpa only [Fintype.card_fin] using hMessageDimLe) received
  have hCardLeListBound : ∀ received : Fin blockLength → ZMod fieldSize,
      (exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
        domain received).card ≤ listBound := by
    intro received
    by_cases hhalf : (1 / 2 : ℝ) ≤ delta
    · simp only [listBound, ite_eq_left hhalf]
      have hEnc := agreeingPolynomials_encard_le_one_of_half hhalf domain hMessageDim
        (by simpa only [Fintype.card_fin] using hMessageDimLe) received
      have hCard : (exactAgreementDecoder (messageDim := messageDim)
          (minAgreement := minAgreement) domain received).card ≤ 1 := by
        have hCardEnc :
            ((exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
              domain received).card : ℕ∞) ≤ 1 := by
          rw [← exactAgreementDecoder_encard_eq domain received]
          simpa only [minAgreement, Fintype.card_fin] using hEnc
        exact_mod_cast hCardEnc
      exact hCard
    · simp only [listBound, ite_eq_right hhalf]
      have hCard :
          (exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
            domain received).card < blockLength := by
        have hCardEnc :
            ((exactAgreementDecoder (messageDim := messageDim) (minAgreement := minAgreement)
              domain received).card : ℕ∞) < blockLength := by
          rw [← exactAgreementDecoder_encard_eq domain received]
          exact hQuarterEnc received
        exact_mod_cast hCardEnc
      exact Nat.le_trans (Nat.le_of_lt hCard) (by omega)
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
  have hEnc' :
      (agreeingPolynomials domain messageDim
        (agreementThreshold delta blockLength messageDim) received).encard <
        (blockLength : ℕ∞) := by
    simpa only [minAgreement] using hQuarterEnc received
  have hBlockLess :
      (blockLength : ℕ∞) < ((4 * fieldSize : ℕ) : ℕ∞) := by
    exact_mod_cast (show blockLength < 4 * fieldSize by omega)
  exact hEnc'.trans hBlockLess

end
end ReedSolomon
