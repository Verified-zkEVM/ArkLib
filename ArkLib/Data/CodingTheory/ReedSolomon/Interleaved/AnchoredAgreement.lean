/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredReconstruction
public import ArkLib.Data.Probability.TwoPointPolynomialCollision

/-!
# Binding an interleaved Reed--Solomon candidate with two anchors

This file packages the generic argument used by the LambdaVM application.  Once the committed
main-column words are fixed, `CandidateSet` contains every polynomial tuple of degree below
`T + 3` having at least `A` simultaneous agreements with those words.  A finite `Code.Lambda`
bound makes this set finite; no finite candidate list or list-size hypothesis is supplied by the
protocol layer.

Two early evaluations bind that whole candidate set before later challenges.  The bad ordered
anchor pairs are exactly the collision set intersected with the distinct pairs outside the code
domain.  Away from this set, the two evaluation vectors identify at most one candidate,
simultaneously for every claimed pair of vectors chosen after the anchors.

The final theorem is deliberately curried so that the selected candidate precedes an arbitrary
type of later randomness.  Every later successful cubic-quotient reconstruction, including its
choice of OOD point and any auxiliary or lookup randomness encoded by that type, equals the early
candidate.  Reducing coordinatewise modulo `X ^ T - 1` therefore fixes the trace while preserving
all trace-domain evaluations.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.AnchoredAgreement

open Polynomial Code ReedSolomon.ListDecoding
open ArkLib.TwoPointPolynomialCollision

variable {F : Type*} [Field F]

/-- Evaluate every coordinate of a polynomial tuple on a Reed--Solomon domain. -/
def tupleEvaluation {n width : ℕ} (domain : Fin n ↪ F)
    (tuple : Fin width → F[X]) : Matrix (Fin n) (Fin width) F :=
  fun x j ↦ (tuple j).eval (domain x)

/-- Degree-bounded polynomial tuples are determined by their domain evaluations. -/
theorem tuple_eq_of_evaluation_eq {n width k : ℕ} (domain : Fin n ↪ F)
    (hkPos : 0 < k) (hk : k ≤ n) (P Q : Fin width → F[X])
    (hP : ∀ j, (P j).degree < k) (hQ : ∀ j, (Q j).degree < k)
    (hEval : tupleEvaluation domain P = tupleEvaluation domain Q) : P = Q := by
  funext j
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P j) (Q j) domain.injective
  · intro x
    exact congrFun (congrFun hEval x) j
  · simp only [Fintype.card_fin]
    apply max_lt
    · by_cases hzero : P j = 0
      · simp [hzero, hkPos.trans_le hk]
      · exact ((Polynomial.natDegree_lt_iff_degree_lt hzero).mpr (hP j)).trans_le hk
    · by_cases hzero : Q j = 0
      · simp [hzero, hkPos.trans_le hk]
      · exact ((Polynomial.natDegree_lt_iff_degree_lt hzero).mpr (hQ j)).trans_le hk

/-- All main-column polynomial tuples compatible with the fixed committed words at the target
degree and simultaneous-agreement threshold. -/
def CandidateSet [DecidableEq F] {n width : ℕ} (domain : Fin n ↪ F)
    (received : Matrix (Fin n) (Fin width) F) (T A : ℕ) : Set (Fin width → F[X]) :=
  {tuple | (∀ j, (tuple j).degree < T + 3) ∧
    A ≤ Code.agree (tupleEvaluation domain tuple) received}

theorem candidateSet_injective [DecidableEq F] {n width T A : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (hDimension : T + 3 ≤ n) :
    Set.InjOn (tupleEvaluation domain) (CandidateSet domain received T A) := by
  intro P hP Q hQ hEval
  exact tuple_eq_of_evaluation_eq domain (by omega) hDimension P Q hP.1 hQ.1 hEval

/-- A capacity-radius list bound makes the complete anchored candidate set finite. -/
theorem candidateSet_finite [DecidableEq F] {n width T A listBound : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (delta : ℝ) (hDelta : 0 ≤ delta) (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : agreementThreshold delta n (T + 3) ≤ A)
    (hLambda : Code.Lambda
      (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
      (capacityRadius delta n (T + 3)) ≤ (listBound : ℕ∞)) :
    (CandidateSet domain received T A).Finite := by
  have hPointList := (Code.Lambda_le_iff_forall_ncard_le.mp hLambda) received
  apply Set.Finite.of_finite_image
  · refine hPointList.1.subset ?_
    rintro codeword ⟨tuple, hTuple, rfl⟩
    apply (Code.mem_closeCodewordsRel_iff
      (C := Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))).mpr
    constructor
    · intro j
      exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt (hTuple.1 j)
    · apply (relHammingDist_le_capacityRadius_iff_agreementThreshold_le
        hDelta hLength _ _).mpr
      exact hThreshold.trans hTuple.2
  · exact candidateSet_injective domain received hDimension

/-- The complete finite family of anchored candidates.  Its proof argument only witnesses the
finiteness already implied by the `Code.Lambda` bound. -/
def candidateFamily [DecidableEq F] {n width T A listBound : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (delta : ℝ) (hDelta : 0 ≤ delta) (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : agreementThreshold delta n (T + 3) ≤ A)
    (hLambda : Code.Lambda
      (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
      (capacityRadius delta n (T + 3)) ≤ (listBound : ℕ∞)) :
    Finset (Fin width → F[X]) :=
  (candidateSet_finite domain received delta hDelta hLength hDimension hThreshold hLambda).toFinset

@[simp]
theorem mem_candidateFamily [DecidableEq F] {n width T A listBound : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (delta : ℝ) (hDelta : 0 ≤ delta) (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : agreementThreshold delta n (T + 3) ≤ A)
    (hLambda : Code.Lambda
      (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
      (capacityRadius delta n (T + 3)) ≤ (listBound : ℕ∞))
    (tuple : Fin width → F[X]) :
    tuple ∈ candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda ↔
      (∀ j, (tuple j).degree < T + 3) ∧
        A ≤ Code.agree (tupleEvaluation domain tuple) received := by
  simp [candidateFamily, CandidateSet]

/-- The complete family inherits the supplied `Code.Lambda` list-size bound. -/
theorem candidateFamily_card_le [DecidableEq F] {n width T A listBound : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (delta : ℝ) (hDelta : 0 ≤ delta) (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : agreementThreshold delta n (T + 3) ≤ A)
    (hLambda : Code.Lambda
      (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
      (capacityRadius delta n (T + 3)) ≤ (listBound : ℕ∞)) :
    (candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda).card ≤
      listBound := by
  let candidates :=
    candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda
  let evaluated := candidates.image (tupleEvaluation domain)
  have hCard : evaluated.card = candidates.card := by
    rw [Finset.card_image_iff]
    intro P hP Q hQ hEval
    exact tuple_eq_of_evaluation_eq domain (by omega) hDimension P Q
      (mem_candidateFamily domain received delta hDelta hLength hDimension
        hThreshold hLambda P |>.mp hP).1
      (mem_candidateFamily domain received delta hDelta hLength hDimension
        hThreshold hLambda Q |>.mp hQ).1
      hEval
  have hPointList := (Code.Lambda_le_iff_forall_ncard_le.mp hLambda) received
  have hSubset :
      (↑evaluated : Set (Matrix (Fin n) (Fin width) F)) ⊆
        Code.closeCodewordsRel
          (Code.interleavedCodeSet (κ := Fin width)
            (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
          received (capacityRadius delta n (T + 3)) := by
    intro codeword hCodeword
    change codeword ∈ evaluated at hCodeword
    obtain ⟨tuple, hTuple, rfl⟩ := Finset.mem_image.mp hCodeword
    have hCandidate := (mem_candidateFamily domain received delta hDelta hLength hDimension
      hThreshold hLambda tuple).mp hTuple
    apply (Code.mem_closeCodewordsRel_iff
      (C := Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))).mpr
    constructor
    · intro j
      exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt (hCandidate.1 j)
    · apply (relHammingDist_le_capacityRadius_iff_agreementThreshold_le
        hDelta hLength _ _).mpr
      exact hThreshold.trans hCandidate.2
  have hNcard :
      (↑evaluated : Set (Matrix (Fin n) (Fin width) F)).ncard ≤
        (Code.closeCodewordsRel
          (Code.interleavedCodeSet (κ := Fin width)
            (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
          received (capacityRadius delta n (T + 3))).ncard :=
    Set.ncard_le_ncard hSubset hPointList.1
  calc
    candidates.card = evaluated.card := hCard.symm
    _ = (↑evaluated : Set (Matrix (Fin n) (Fin width) F)).ncard := by simp
    _ ≤ _ := hNcard
    _ ≤ listBound := hPointList.2

/-! ## Exact bad-pair space and two-anchor binding -/

/-- Bad ordered anchor pairs among the pairs sampled distinctly outside the evaluation domain. -/
def badAnchorPairs [Fintype F] [DecidableEq F] {n width : ℕ} (domain : Fin n ↪ F)
    (candidates : Finset (Fin width → F[X])) : Finset (F × F) := by
  classical
  exact collisionSet candidates ∩ orderedDistinctPairs (outsideDomain domain)

/-- Exact collision probability for uniform sampling from the ordered, distinct, outside-domain
anchor pairs. -/
def badAnchorRate [Fintype F] [DecidableEq F] {n width : ℕ} (domain : Fin n ↪ F)
    (candidates : Finset (Fin width → F[X])) : ℚ :=
  (badAnchorPairs domain candidates).card /
    (orderedDistinctPairs (outsideDomain domain)).card

/-- The denominator in `badAnchorRate` is the exact ordered sample-space size. -/
theorem badAnchorRate_eq [Fintype F] [DecidableEq F] {n width : ℕ}
    (domain : Fin n ↪ F) (candidates : Finset (Fin width → F[X])) :
    badAnchorRate domain candidates =
      ((badAnchorPairs domain candidates).card : ℚ) /
        (((Fintype.card F - n) * (Fintype.card F - n - 1) : ℕ) : ℚ) := by
  rw [badAnchorRate, card_orderedDistinctPairs_outsideDomain]

/-- For a pair in the sampler's support, avoiding `badAnchorPairs` means avoiding the underlying
collision set. -/
theorem not_mem_collisionSet_of_sampled_of_not_mem_badAnchorPairs
    [Fintype F] [DecidableEq F] {n width : ℕ} (domain : Fin n ↪ F)
    (candidates : Finset (Fin width → F[X])) {s₁ s₂ : F}
    (hSampled : (s₁, s₂) ∈ orderedDistinctPairs (outsideDomain domain))
    (hGood : (s₁, s₂) ∉ badAnchorPairs domain candidates) :
    (s₁, s₂) ∉ collisionSet candidates := by
  intro hCollision
  exact hGood (Finset.mem_inter.mpr ⟨hCollision, hSampled⟩)

/-- Degree below `T + 3` gives the `T + 2` natural-degree cap used by the collision bound. -/
theorem natDegree_le_add_two_of_degree_lt_add_three {T : ℕ} (p : F[X])
    (hDegree : p.degree < T + 3) : p.natDegree ≤ T + 2 := by
  by_cases hzero : p = 0
  · simp [hzero]
  · have hNat : p.natDegree < T + 3 :=
      (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hDegree
    omega

/-- The two-anchor collision probability of any bounded family obeys the standard union bound. -/
theorem badAnchorRate_le [Fintype F] [DecidableEq F]
    {n width T listBound : ℕ} (domain : Fin n ↪ F)
    (candidates : Finset (Fin width → F[X]))
    (hDegree : ∀ tuple ∈ candidates, ∀ j, (tuple j).degree < T + 3)
    (hList : candidates.card ≤ listBound) (hSpace : n + 1 < Fintype.card F) :
    badAnchorRate domain candidates ≤
      (listBound.choose 2 : ℚ) *
        (((T + 2 : ℕ) : ℚ) / (Fintype.card F - n - 1 : ℕ)) ^ 2 := by
  classical
  have hDegreeNat : ∀ tuple ∈ candidates, ∀ j, (tuple j).natDegree ≤ T + 2 := by
    intro tuple hTuple j
    exact natDegree_le_add_two_of_degree_lt_add_three _ (hDegree tuple hTuple j)
  simpa [badAnchorRate, badAnchorPairs, collisionRate] using
    (collisionRate_le domain candidates hDegreeNat hList hSpace)

/-- The complete candidate family gets its collision bound directly from `Code.Lambda`. -/
theorem candidateFamily_badAnchorRate_le [Fintype F] [DecidableEq F]
    {n width T A listBound : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (delta : ℝ) (hDelta : 0 ≤ delta) (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : agreementThreshold delta n (T + 3) ≤ A)
    (hLambda : Code.Lambda
      (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
      (capacityRadius delta n (T + 3)) ≤ (listBound : ℕ∞))
    (hSpace : n + 1 < Fintype.card F) :
    badAnchorRate domain
        (candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda) ≤
      (listBound.choose 2 : ℚ) *
        (((T + 2 : ℕ) : ℚ) / (Fintype.card F - n - 1 : ℕ)) ^ 2 := by
  apply badAnchorRate_le domain _
  · intro tuple hTuple
    exact (mem_candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda
      tuple).mp hTuple |>.1
  · exact candidateFamily_card_le domain received delta hDelta hLength hDimension
      hThreshold hLambda
  · exact hSpace

/-- The pair of main-column evaluation vectors revealed at the two early anchors. -/
def twoAnchorValues {width : ℕ} (s₁ s₂ : F) (tuple : Fin width → F[X]) :
    (Fin width → F) × (Fin width → F) :=
  (⟨fun j ↦ (tuple j).eval s₁, fun j ↦ (tuple j).eval s₂⟩)

/-- Outside the bad set, two-anchor evaluation is injective on the whole candidate family. -/
theorem twoAnchorValues_injOn_of_good [DecidableEq F] {width : ℕ}
    (candidates : Finset (Fin width → F[X])) {s₁ s₂ : F}
    (hGood : (s₁, s₂) ∉ collisionSet candidates) :
    Set.InjOn (twoAnchorValues s₁ s₂) (↑candidates : Set (Fin width → F[X])) := by
  intro left hLeft right hRight hValues
  apply eq_of_agree_of_not_mem_collisionSet hLeft hRight hGood
  · intro j
    exact congrFun (congrArg Prod.fst hValues) j
  · intro j
    exact congrFun (congrArg Prod.snd hValues) j

/-- A good anchor pair binds every possible pair of claimed evaluation vectors at once.  The
claimed vectors occur after `s₁`, `s₂`, and `hGood`, so they may be chosen after seeing the
anchors. -/
theorem eq_of_claimed_twoAnchorValues_of_good [DecidableEq F] {width : ℕ}
    (candidates : Finset (Fin width → F[X])) (s₁ s₂ : F)
    (hGood : (s₁, s₂) ∉ collisionSet candidates)
    (claimed₁ claimed₂ : Fin width → F)
    {left right : Fin width → F[X]} (hLeft : left ∈ candidates)
    (hRight : right ∈ candidates)
    (hLeftValues : twoAnchorValues s₁ s₂ left = ⟨claimed₁, claimed₂⟩)
    (hRightValues : twoAnchorValues s₁ s₂ right = ⟨claimed₁, claimed₂⟩) :
    left = right := by
  apply twoAnchorValues_injOn_of_good candidates hGood hLeft hRight
  exact hLeftValues.trans hRightValues.symm

/-! ## Later cubic quotient reconstruction -/

/-- The word obtained by evaluating the left-hand side of each cubic quotient equation. -/
def cubicQuotientWord {n width : ℕ} (domain : Fin n ↪ F) (s₁ s₂ z : F)
    (quotient : Fin width → F[X]) : Matrix (Fin n) (Fin width) F :=
  fun x j ↦ (cubicAnchorDivisor s₁ s₂ z).eval (domain x) *
    (quotient j).eval (domain x)

/-- The received residual word on the right-hand side of each cubic quotient equation. -/
def cubicResidualWord {n width : ℕ} (domain : Fin n ↪ F)
    (received : Matrix (Fin n) (Fin width) F) (interpolant : Fin width → F[X]) :
    Matrix (Fin n) (Fin width) F :=
  fun x j ↦ received x j - (interpolant j).eval (domain x)

/-- Reconstruct every main-column polynomial from a later cubic quotient. -/
def cubicReconstructedTuple {width : ℕ} (s₁ s₂ z : F)
    (quotient interpolant : Fin width → F[X]) : Fin width → F[X] :=
  fun j ↦ cubicAnchorReconstruct s₁ s₂ z (quotient j) (interpolant j)

/-- Agreement of the evaluated quotient equations implies simultaneous agreement of the
reconstructed main-column tuple with the committed received words. -/
theorem cubicReconstructedTuple_agreement [DecidableEq F] {n width A : ℕ} (domain : Fin n ↪ F)
    (received : Matrix (Fin n) (Fin width) F) (s₁ s₂ z : F)
    (quotient interpolant : Fin width → F[X])
    (hAgreement : A ≤ Code.agree (cubicQuotientWord domain s₁ s₂ z quotient)
      (cubicResidualWord domain received interpolant)) :
    A ≤ Code.agree (tupleEvaluation domain
      (cubicReconstructedTuple s₁ s₂ z quotient interpolant)) received := by
  apply hAgreement.trans
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  funext j
  apply cubicAnchorReconstruct_eval_of_quotient
  exact congrFun hx j

/-- Data revealed or extracted after the early candidate has already been selected. -/
structure LaterCubicReconstruction (width : ℕ) where
  /-- The later out-of-domain evaluation point. -/
  z : F
  /-- The claimed main-column values at `z`. -/
  claimedZ : Fin width → F
  /-- Extracted degree-`< T` quotient polynomials. -/
  quotient : Fin width → F[X]
  /-- Interpolants through the two early claims and the later OOD claim. -/
  interpolant : Fin width → F[X]

/-- Conditions supplied by a successful later cubic quotient reconstruction.  Agreement is
stated on the actual quotient equation words and transferred to the reconstructed tuple by
`cubicReconstructedTuple_agreement`. -/
def SuccessfulCubicReconstruction [DecidableEq F] {n width T A : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (s₁ s₂ : F) (claimed₁ claimed₂ : Fin width → F)
    (later : LaterCubicReconstruction (F := F) width) : Prop :=
  s₁ ≠ s₂ ∧ later.z ≠ s₁ ∧ later.z ≠ s₂ ∧
    (∀ j, (later.quotient j).degree < T) ∧
    (∀ j, (later.interpolant j).degree < 3) ∧
    (∀ j, (later.interpolant j).eval s₁ = claimed₁ j) ∧
    (∀ j, (later.interpolant j).eval s₂ = claimed₂ j) ∧
    (∀ j, (later.interpolant j).eval later.z = later.claimedZ j) ∧
    A ≤ Code.agree (cubicQuotientWord domain s₁ s₂ later.z later.quotient)
      (cubicResidualWord domain received later.interpolant)

/-- A successful later reconstruction belongs to the complete early candidate family and has
the two claimed early evaluation vectors. -/
theorem successfulCubicReconstruction_mem_and_values [DecidableEq F]
    {n width T A listBound : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (delta : ℝ) (hDelta : 0 ≤ delta) (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : agreementThreshold delta n (T + 3) ≤ A)
    (hLambda : Code.Lambda
      (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
      (capacityRadius delta n (T + 3)) ≤ (listBound : ℕ∞))
    (hTraceLength : 0 < T)
    (s₁ s₂ : F) (claimed₁ claimed₂ : Fin width → F)
    (later : LaterCubicReconstruction (F := F) width)
    (hSuccess : SuccessfulCubicReconstruction domain received s₁ s₂ claimed₁ claimed₂
      (T := T) (A := A) later) :
    cubicReconstructedTuple s₁ s₂ later.z later.quotient later.interpolant ∈
        candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda ∧
      twoAnchorValues s₁ s₂
          (cubicReconstructedTuple s₁ s₂ later.z later.quotient later.interpolant) =
        ⟨claimed₁, claimed₂⟩ := by
  rcases hSuccess with ⟨_, _, _, hQuotient, hInterpolant, hFirst, hSecond, _, hAgreement⟩
  constructor
  · apply (mem_candidateFamily domain received delta hDelta hLength hDimension hThreshold
      hLambda _).mpr
    constructor
    · intro j
      exact cubicAnchorReconstruct_degree_lt hTraceLength s₁ s₂ later.z
        (later.quotient j) (later.interpolant j) (hQuotient j) (hInterpolant j)
    · exact cubicReconstructedTuple_agreement domain received s₁ s₂ later.z
        later.quotient later.interpolant hAgreement
  · apply Prod.ext
    · funext j
      exact (cubicAnchorReconstruct_eval_anchors s₁ s₂ later.z
        (later.quotient j) (later.interpolant j)).1.trans (hFirst j)
    · funext j
      exact (cubicAnchorReconstruct_eval_anchors s₁ s₂ later.z
        (later.quotient j) (later.interpolant j)).2.1.trans (hSecond j)

/-- For every good sampled anchor pair and every pair of claimed vectors, choose either the
unique consistent early candidate or `none`.  The option is chosen before any later
reconstruction data is quantified.  A successful later reconstruction proves that the option
was `some` and identifies its value; no successful reconstruction or nonempty candidate fiber is
assumed in advance. -/
theorem exists_selectedCandidate_before_later [Fintype F] [DecidableEq F]
    {n width T A listBound : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (delta : ℝ) (hDelta : 0 ≤ delta) (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : agreementThreshold delta n (T + 3) ≤ A)
    (hLambda : Code.Lambda
      (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
      (capacityRadius delta n (T + 3)) ≤ (listBound : ℕ∞))
    (hTraceLength : 0 < T) (s₁ s₂ : F)
    (hSampled : (s₁, s₂) ∈ orderedDistinctPairs (outsideDomain domain))
    (hGood : (s₁, s₂) ∉ badAnchorPairs domain
      (candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda))
    (claimed₁ claimed₂ : Fin width → F) :
    ∃ selected : Option (Fin width → F[X]),
      (∀ tuple, selected = some tuple →
        tuple ∈ candidateFamily domain received delta hDelta hLength hDimension
          hThreshold hLambda ∧
        twoAnchorValues s₁ s₂ tuple = ⟨claimed₁, claimed₂⟩) ∧
      ∀ later : LaterCubicReconstruction (F := F) width,
        SuccessfulCubicReconstruction domain received s₁ s₂ claimed₁ claimed₂
            (T := T) (A := A) later →
          selected = some
            (cubicReconstructedTuple s₁ s₂ later.z later.quotient later.interpolant) := by
  classical
  let candidates :=
    candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda
  by_cases hExists : ∃ tuple ∈ candidates,
      twoAnchorValues s₁ s₂ tuple = ⟨claimed₁, claimed₂⟩
  · let selected := Classical.choose hExists
    have hSelected := Classical.choose_spec hExists
    refine ⟨some selected, ?_, ?_⟩
    · intro tuple hSome
      have hEq : selected = tuple := Option.some.inj hSome
      subst tuple
      change selected ∈ candidates ∧
        twoAnchorValues s₁ s₂ selected = ⟨claimed₁, claimed₂⟩
      exact hSelected
    · intro later hSuccess
      have hLater := successfulCubicReconstruction_mem_and_values domain received delta hDelta
        hLength hDimension hThreshold hLambda hTraceLength s₁ s₂ claimed₁ claimed₂
        later hSuccess
      have hNoCollision := not_mem_collisionSet_of_sampled_of_not_mem_badAnchorPairs domain
        candidates hSampled hGood
      have hEq := eq_of_claimed_twoAnchorValues_of_good candidates s₁ s₂ hNoCollision
        claimed₁ claimed₂ hSelected.1 hLater.1 hSelected.2 hLater.2
      exact congrArg some hEq
  · refine ⟨none, ?_, ?_⟩
    · intro tuple hSome
      simp at hSome
    · intro later hSuccess
      have hLater := successfulCubicReconstruction_mem_and_values domain received delta hDelta
        hLength hDimension hThreshold hLambda hTraceLength s₁ s₂ claimed₁ claimed₂
        later hSuccess
      exact (hExists ⟨_, hLater.1, hLater.2⟩).elim

/-! ## The fixed trace remainder -/

/-- Reduce every selected main-column polynomial modulo the trace zerofier. -/
def traceRemainderTuple {width : ℕ} (T : ℕ) (tuple : Fin width → F[X]) :
    Fin width → F[X] :=
  fun j ↦ tuple j %ₘ (X ^ T - C (1 : F))

/-- Every coordinate of the trace remainder has degree below `T`. -/
theorem traceRemainderTuple_degree_lt {width : ℕ} (T : ℕ) (hT : 0 < T)
    (tuple : Fin width → F[X]) (j : Fin width) :
    (traceRemainderTuple T tuple j).degree < T :=
  traceRemainder_degree_lt T hT (tuple j)

/-- Coordinatewise trace reduction preserves all values on the trace domain. -/
theorem traceRemainderTuple_eval_eq {width : ℕ} (T : ℕ)
    (tuple : Fin width → F[X]) (x : F) (hx : x ^ T = 1) (j : Fin width) :
    (traceRemainderTuple T tuple j).eval x = (tuple j).eval x :=
  traceRemainder_eval_eq T (tuple j) x hx

/-- The pre-later optional selection also fixes the coordinatewise trace remainder.  If a later
reconstruction succeeds, mapping trace reduction over the already chosen option gives exactly
the reconstructed trace. -/
theorem exists_selectedTrace_before_later [Fintype F] [DecidableEq F]
    {n width T A listBound : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (delta : ℝ) (hDelta : 0 ≤ delta) (hLength : 0 < n) (hDimension : T + 3 ≤ n)
    (hThreshold : agreementThreshold delta n (T + 3) ≤ A)
    (hLambda : Code.Lambda
      (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (T + 3) : Set (Fin n → F)))
      (capacityRadius delta n (T + 3)) ≤ (listBound : ℕ∞))
    (hTraceLength : 0 < T) (s₁ s₂ : F)
    (hSampled : (s₁, s₂) ∈ orderedDistinctPairs (outsideDomain domain))
    (hGood : (s₁, s₂) ∉ badAnchorPairs domain
      (candidateFamily domain received delta hDelta hLength hDimension hThreshold hLambda))
    (claimed₁ claimed₂ : Fin width → F) :
    ∃ selected : Option (Fin width → F[X]),
      (∀ tuple, selected = some tuple →
        tuple ∈ candidateFamily domain received delta hDelta hLength hDimension
          hThreshold hLambda ∧
        twoAnchorValues s₁ s₂ tuple = ⟨claimed₁, claimed₂⟩) ∧
      ∀ later : LaterCubicReconstruction (F := F) width,
        SuccessfulCubicReconstruction domain received s₁ s₂ claimed₁ claimed₂
            (T := T) (A := A) later →
          selected.map (traceRemainderTuple T) = some
            (traceRemainderTuple T
              (cubicReconstructedTuple s₁ s₂ later.z later.quotient later.interpolant)) := by
  obtain ⟨selected, hSelected, hLater⟩ := exists_selectedCandidate_before_later domain received
    delta hDelta hLength hDimension hThreshold hLambda hTraceLength s₁ s₂ hSampled hGood
    claimed₁ claimed₂
  refine ⟨selected, hSelected, ?_⟩
  intro later hSuccess
  rw [hLater later hSuccess]
  rfl


end ReedSolomon.AnchoredAgreement
