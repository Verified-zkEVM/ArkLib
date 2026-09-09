/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.DerivativeImage
import
  ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.PowerToLine
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HybridDescent
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.HybridConstants

/-!
# Hybrid first-order correlated-agreement transfer

This file combines the regular `Y₁` stages of the actual-degree first-order descent with a
separately supplied order-zero tail theorem.  The tail interface states only the ordinary
conclusion and its ordinary numerical charge.  In particular, it does not assume the hybrid
conclusion or its final exceptional-set bound.

The resulting bound is first proved against the exact real-valued stage sum.  Both the ceiling
bound and the printed closed real bound are then derived from that same raw comparison.
-/

open PolynomialDifferential Polynomial

namespace ReedSolomon

open HiddenDerivative MvPolynomial HiddenDerivative.SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

/-- Exact correlated-pair agreement is exactly degree-one power agreement for the tuple
`![f,g]`.  This is the converse of `exactCorrelatedPair_of_powerAgreement_one`; both directions
preserve equality of the entire agreement set. -/
theorem powerAgreement_one_of_exactCorrelatedPair
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n k : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E) (z : E) (Q : E[X])
    (h : HasExactCorrelatedPair domain f g iota k z Q) :
    HasExactPowerAgreement domain ![f, g] iota k z Q := by
  obtain ⟨pair, hdeg0, hdeg1, hQ, hagree⟩ := h
  let P : Fin 2 → F[X] := ![pair.1, pair.2]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro t
    fin_cases t <;> assumption
  · simpa [P, powerBatchedPolynomial, correlatedPairSpecialization,
      Fin.sum_univ_two, Polynomial.smul_eq_C_mul] using hQ
  · have hw : powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z =
        (fun i ↦ iota (f i) + z * iota (g i)) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    rw [hw]
    simpa [P, commonCurveAgreementSet, commonPolynomialAgreementSet,
      Fin.forall_fin_two] using hagree

/-- The sharp regular-curve bound at a first-order descent stage is exactly the corresponding
summand in the raw hybrid arithmetic. -/
theorem regularSymbolicCurveMCADerivativeBoundTwo_eq_hybrid_stage
    {n D A L h mu e j : ℕ} (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n) :
    (regularSymbolicCurveMCADerivativeBoundTwo n 1 (D + 1) (D + 1) L A
        (mu - j) (e - j) h (HiddenDerivative.hybridTau D) : ℝ) =
      HiddenDerivative.hybridLambdaOne n A L * HiddenDerivative.hybridTheta n D A *
          HiddenDerivative.firstOrderCurveJointStageOne
            (D + 1) 1 h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
        (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
          HiddenDerivative.firstOrderCurveFiberStageOne
            (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D) := by
  have hDn : D ≤ n := by omega
  have hDA : D < A := hDL.trans_le hLA
  have hnumA : n - (D + 1) + 1 = n - D := by omega
  have hdenA : A - (D + 1) + 1 = A - D := by omega
  have hdenL : L - (D + 1) + 1 = L - D := by omega
  simp [regularSymbolicCurveMCADerivativeBoundTwo,
    HiddenDerivative.firstOrderCurveJointStageOne,
    HiddenDerivative.firstOrderCurveFiberStageOne,
    sourceCurveCutChallengeDegree, sourceCurveCutJetDegree,
    sourceCurveCutDerivativeDegree, HiddenDerivative.firstOrderTaylorTotalCap,
    HiddenDerivative.firstOrderTaylorDerivativeCap,
    AffineHilbert.mixedDerivativeImageDegree,
    hnumA, hdenA, hdenL, HiddenDerivative.hybridLambdaOne,
    HiddenDerivative.hybridLambdaTwo, HiddenDerivative.hybridTheta]
  ring

/-- The exact ordinary-tail interface needed by the hybrid transfer.  It asks only for an
order-zero theorem with the order-zero charge, and concludes exact correlated-pair agreement.
The hybrid exceptional set and hybrid numerical bound do not occur in this hypothesis. -/
def HasOrdinaryTailTransfer
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    {n D A h mu e : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q0 : DifferentialPolynomial E[X] 0) : Prop :=
  ∃ exceptional : Finset E,
    (exceptional.card : ℝ) ≤
      HiddenDerivative.hybridOrdinaryRaw
        (HiddenDerivative.hybridTheta n D A) n D h (mu - e) ∧
    ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P).card →
      differentialSpecialization (challengeSpecialization Q0 z) P = 0 →
      HasExactCorrelatedPair domain f g iota (D + 1) z P

/-- An injective field homomorphism preserves the ring characteristic. -/
theorem ringChar_eq_of_injective_fieldHom
    {F E : Type*} [Field F] [Field E] (iota : F →+* E) : ringChar E = ringChar F := by
  let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
  exact ringChar.eq E (ringChar F)

private theorem natCast_ne_zero_of_max_char_guard
    {E : Type*} [Field E] {D M i : ℕ}
    (hchar : ringChar E = 0 ∨ max D M < ringChar E) (hi : 0 < i) (hiD : i ≤ D) :
    (i : E) ≠ 0 := by
  intro hz
  have hdiv := (ringChar.spec E i).mp hz
  rcases hchar with hzero | hpos
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hi
      ((hiD.trans (Nat.le_max_left D M)).trans_lt hpos) hdiv

/-- The exact regular-stage exceptional sets for an actual-degree descent, unioned into one
set.  This is the regular half of the hybrid transfer and carries the exact raw stage sum. -/
theorem exists_exceptional_firstOrder_regularStages
    {F E : Type*} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {n D A L h mu M : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (Q : DifferentialPolynomial E[X] 1)
    (descent : HiddenDerivative.FirstOrderHybridDescent Q mu M h)
    (hD : 1 ≤ D) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.hybridLambdaOne n A L *
            HiddenDerivative.hybridTheta n D A *
              HiddenDerivative.hybridJ1 D h mu descent.actualDegree +
          (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
            HiddenDerivative.hybridB1 D mu descent.actualDegree ∧
      ∀ z ∉ exceptional, ∀ j < descent.actualDegree, ∀ P : E[X],
        P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization
            (challengeSpecialization (HiddenDerivative.firstOrderDerivativeStage Q j) z) P = 0 →
        differentialSpecialization
            (separant
              (challengeSpecialization (HiddenDerivative.firstOrderDerivativeStage Q j) z)
              (1 : Fin 2)) P ≠ 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
  classical
  let e := descent.actualDegree
  have heμ : e ≤ mu := by
    have hdegree := descent.stage_degree 0 (Nat.zero_le e)
    have hweight := descent.stage_jetWeight_le 0 (Nat.zero_le e)
    have hle := jetDegree_le_jetWeight Q (1 : Fin 2)
    have hjet : jetDegree Q (1 : Fin 2) ≤ mu := by
      simpa only [HiddenDerivative.firstOrderDerivativeStage_zero, Nat.sub_zero] using
        hle.trans hweight
    exact descent.actualDegree_eq.trans_le hjet
  have hcharE : ringChar E = 0 ∨ max D M < ringChar E := by
    rwa [ringChar_eq_of_injective_fieldHom iota]
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiK
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_max_char_guard hcharE (by omega) (by omega)
  have hτ : TaylorExponentSufficient 1 (D + 1) (HiddenDerivative.hybridTau D) := by
    convert taylorExponentSufficient_two_mul_sub_three 1 (K := D + 1) (by omega) using 1
    unfold HiddenDerivative.hybridTau
    omega
  have hstage (j : Fin e) : ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.hybridLambdaOne n A L *
            HiddenDerivative.hybridTheta n D A *
              HiddenDerivative.firstOrderCurveJointStageOne
                (D + 1) 1 h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
          (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
            HiddenDerivative.firstOrderCurveFiberStageOne
              (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization
            (challengeSpecialization (HiddenDerivative.firstOrderDerivativeStage Q j) z) P = 0 →
        differentialSpecialization
            (separant
              (challengeSpecialization (HiddenDerivative.firstOrderDerivativeStage Q j) z)
              (1 : Fin 2)) P ≠ 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
    have hj : j.val < e := j.isLt
    have hv : 0 < mu - j := by omega
    have hu : 0 < e - j := by omega
    have huv : e - j ≤ mu - j := Nat.sub_le_sub_right heμ j
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_regularSymbolicCurveMCA_derivativeCapped_of_exponent
        domain ![f, g] iota
        (HiddenDerivative.firstOrderDerivativeStage Q j) (D + 1) (D + 1) L A
        (mu - j) (e - j) h (HiddenDerivative.hybridTau D) hτ (by
          unfold HiddenDerivative.hybridTau
          omega) (by omega) le_rfl (by omega) (by omega) hLA hAn (by omega) hv hu huv
        (descent.stage_jetWeight_le j (Nat.le_of_lt hj))
        (descent.stage_challengeHeight_le j)
        ((descent.stage_degree j (Nat.le_of_lt hj)).le)
        hbin
    refine ⟨exceptional, ?_, ?_⟩
    · rw [← regularSymbolicCurveMCADerivativeBoundTwo_eq_hybrid_stage hDL hLA hAn]
      exact_mod_cast hcard
    · intro z hz P hdegree hagree hroot hsep
      apply hgood z hz P hdegree hagree hroot
      simpa only [show (Fin.last 1 : Fin 2) = 1 by decide] using hsep
  let stageExceptional : Fin e → Finset E := fun j ↦ Classical.choose (hstage j)
  let exceptional := Finset.univ.biUnion stageExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardNat : exceptional.card ≤ ∑ j, (stageExceptional j).card := by
      exact Finset.card_biUnion_le
    have hcardReal : (exceptional.card : ℝ) ≤
        ∑ j, ((stageExceptional j).card : ℝ) := by exact_mod_cast hcardNat
    have hsum : (∑ j, ((stageExceptional j).card : ℝ)) ≤
        ∑ j : Fin e,
          (HiddenDerivative.hybridLambdaOne n A L *
              HiddenDerivative.hybridTheta n D A *
                HiddenDerivative.firstOrderCurveJointStageOne
                  (D + 1) 1 h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
            (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
              HiddenDerivative.firstOrderCurveFiberStageOne
                (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D)) := by
      apply Finset.sum_le_sum
      intro j _
      exact (Classical.choose_spec (hstage j)).1
    apply hcardReal.trans (hsum.trans_eq ?_)
    have hfin : (∑ j : Fin e,
          (HiddenDerivative.hybridLambdaOne n A L *
              HiddenDerivative.hybridTheta n D A *
                HiddenDerivative.firstOrderCurveJointStageOne
                  (D + 1) 1 h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
            (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
              HiddenDerivative.firstOrderCurveFiberStageOne
                (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D))) =
        ∑ j ∈ Finset.range e,
          (HiddenDerivative.hybridLambdaOne n A L *
              HiddenDerivative.hybridTheta n D A *
                HiddenDerivative.firstOrderCurveJointStageOne
                  (D + 1) 1 h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
            (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
              HiddenDerivative.firstOrderCurveFiberStageOne
                (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D)) := by
      exact Fin.sum_univ_eq_sum_range (α := ℝ) (fun j : ℕ ↦
        (HiddenDerivative.hybridLambdaOne n A L *
            HiddenDerivative.hybridTheta n D A *
              HiddenDerivative.firstOrderCurveJointStageOne
                (D + 1) 1 h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
          (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
            HiddenDerivative.firstOrderCurveFiberStageOne
              (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D))) e
    rw [hfin]
    simp only [HiddenDerivative.hybridJ1, HiddenDerivative.hybridB1, e,
      Nat.cast_sum]
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
  · intro z hz j hj P hdegree hagree hroot hsep
    have hzj : z ∉ stageExceptional ⟨j, hj⟩ := by
      intro hmem
      apply hz
      exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, hmem⟩
    exact (Classical.choose_spec (hstage ⟨j, hj⟩)).2 z hzj P hdegree hagree hroot hsep

/-- Degree-one power batching of `![f,g]` is the correlated line word, after scalar
extension. -/
theorem powerBatchedWord_pair_eq
    {F E : Type*} [Field F] [Field E] {n : ℕ} (f g : Fin n → F)
    (iota : F →+* E) (z : E) :
    powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z =
      (fun i ↦ iota (f i) + z * iota (g i)) := by
  funext i
  simp [powerBatchedWord, Fin.sum_univ_two]

/-- The ordinary tail set and all actual regular `Y₁` stage sets combine into one exceptional
set with the exact raw hybrid charge at the chosen retention split `L`. -/
theorem exists_exceptional_firstOrder_hybrid_raw_of_tail
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n D A L h mu M : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (Q : DifferentialPolynomial E[X] 1)
    (descent : HiddenDerivative.FirstOrderHybridDescent Q mu M h)
    (hD : 1 ≤ D) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasOrdinaryTailTransfer (D := D) (A := A) (h := h) (mu := mu)
      (e := descent.actualDegree) domain f g iota descent.tail.equation) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.hybridERaw (HiddenDerivative.hybridTheta n D A)
          n D A h mu descent.actualDegree L ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
  classical
  obtain ⟨tailExceptional, htailCard, htailGood⟩ := htail
  obtain ⟨regularExceptional, hregularCard, hregularGood⟩ :=
    exists_exceptional_firstOrder_regularStages domain f g iota Q descent
      hD hDL hLA hAn hchar
  let exceptional := tailExceptional ∪ regularExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardNat : exceptional.card ≤ tailExceptional.card + regularExceptional.card := by
      exact Finset.card_union_le _ _
    have hcardReal : (exceptional.card : ℝ) ≤
        (tailExceptional.card : ℝ) + (regularExceptional.card : ℝ) := by
      exact_mod_cast hcardNat
    apply hcardReal.trans
    unfold HiddenDerivative.hybridERaw
    linarith
  · intro z hz P hdegree hagree hroot
    have hzTail : z ∉ tailExceptional := by
      intro hmem
      exact hz (Finset.mem_union_left regularExceptional hmem)
    have hzRegular : z ∉ regularExceptional := by
      intro hmem
      exact hz (Finset.mem_union_right tailExceptional hmem)
    have heval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
      apply Polynomial.ringHom_ext
      · intro x
        simp
      · simp
    rw [challengeSpecialization, heval] at hroot
    have hcoverage := descent.root_coverage (Polynomial.evalRingHom z) P hroot
    rcases hcoverage with htailRoot | ⟨j, hj, hstageRoot, hstageSeparant⟩
    · apply powerAgreement_one_of_exactCorrelatedPair domain f g iota z P
      apply htailGood z hzTail P hdegree
      · rw [← powerBatchedWord_pair_eq f g iota z]
        exact hagree
      · rw [challengeSpecialization, heval]
        exact htailRoot
    · apply hregularGood z hzRegular j hj P hdegree hagree
      · rw [challengeSpecialization, heval]
        exact hstageRoot
      · rw [challengeSpecialization, heval]
        exact hstageSeparant

/-- In the nonempty geometric range, the fixed-degree minimum is attained by an admissible
integer split. -/
theorem exists_hybridERaw_eq_hybridERawAtDegree
    {theta : ℝ} {n D A h mu e : ℕ} (hDA : D < A) :
    ∃ L, D < L ∧ L ≤ A ∧
      HiddenDerivative.hybridERaw theta n D A h mu e L =
        HiddenDerivative.hybridERawAtDegree theta n D A h mu e := by
  classical
  let splits := Finset.Icc (D + 1) A
  have hsplits : splits.Nonempty := by
    refine ⟨D + 1, ?_⟩
    simp only [splits, Finset.mem_Icc]
    omega
  let charges := splits.image (HiddenDerivative.hybridERaw theta n D A h mu e)
  have hcharges : charges.Nonempty := Finset.image_nonempty.mpr hsplits
  have hmem := Finset.min'_mem charges hcharges
  obtain ⟨L, hL, hvalue⟩ := Finset.mem_image.mp hmem
  refine ⟨L, ?_, ?_, ?_⟩
  · exact (Finset.mem_Icc.mp hL).1
  · exact (Finset.mem_Icc.mp hL).2
  · rw [HiddenDerivative.hybridERawAtDegree]
    simp only [hDA, ↓reduceDIte]
    exact hvalue

/-- The fixed-degree optimized charge is one of the entries in the outer finite maximum. -/
theorem hybridERawAtDegree_le_hybridEOptimizedRaw
    {theta : ℝ} {n D A h mu M e : ℕ} (heM : e ≤ M) :
    HiddenDerivative.hybridERawAtDegree theta n D A h mu e ≤
      HiddenDerivative.hybridEOptimizedRaw theta n D A h mu M := by
  classical
  unfold HiddenDerivative.hybridEOptimizedRaw
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨e, ?_, rfl⟩
  simpa only [Finset.mem_range, Nat.lt_add_one_iff] using heM

/-- Optimizing the actual-degree hybrid transfer over `L` and then over every `e ≤ M` gives
one exceptional set with all three numerical interfaces.  The natural ceiling and printed
closed real bound are both derived from the same raw real cardinality comparison. -/
theorem exists_exceptional_firstOrder_hybrid_optimized_of_tail
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n D A h mu M : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (Q : DifferentialPolynomial E[X] 1)
    (descent : HiddenDerivative.FirstOrderHybridDescent Q mu M h)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hmu : 1 ≤ mu) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasOrdinaryTailTransfer (D := D) (A := A) (h := h) (mu := mu)
      (e := descent.actualDegree) domain f g iota descent.tail.equation) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
          HiddenDerivative.hybridEOptimizedRaw
            (HiddenDerivative.hybridTheta n D A) n D A h mu M ∧
      exceptional.card ≤
          HiddenDerivative.hybridEOptimizedCeil
            (HiddenDerivative.hybridTheta n D A) n D A h mu M ∧
      (exceptional.card : ℝ) ≤
          HiddenDerivative.hybridEClosed
            (HiddenDerivative.hybridTheta n D A) n D h mu M ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
  obtain ⟨L, hDL, hLA, hL⟩ := exists_hybridERaw_eq_hybridERawAtDegree
    (theta := HiddenDerivative.hybridTheta n D A) (n := n) (h := h)
    (mu := mu) (e := descent.actualDegree) hDA
  obtain ⟨exceptional, hcardL, hgood⟩ :=
    exists_exceptional_firstOrder_hybrid_raw_of_tail domain f g iota Q descent
      hD hDL hLA hAn hchar htail
  have hdegreeOpt := hybridERawAtDegree_le_hybridEOptimizedRaw
    (theta := HiddenDerivative.hybridTheta n D A) (n := n) (D := D) (A := A)
    (h := h) (mu := mu) (e := descent.actualDegree) descent.actualDegree_le
  have hcardRaw : (exceptional.card : ℝ) ≤
      HiddenDerivative.hybridEOptimizedRaw
        (HiddenDerivative.hybridTheta n D A) n D A h mu M := by
    rw [hL] at hcardL
    exact hcardL.trans hdegreeOpt
  have hcardCeil : exceptional.card ≤
      HiddenDerivative.hybridEOptimizedCeil
        (HiddenDerivative.hybridTheta n D A) n D A h mu M := by
    unfold HiddenDerivative.hybridEOptimizedCeil
    exact_mod_cast hcardRaw.trans (Nat.le_ceil _)
  have hclosed := HiddenDerivative.hybridEOptimizedRaw_le_closed
    (h := h) hD hDA hAn hmu hMmu
  exact ⟨exceptional, hcardRaw, hcardCeil, hcardRaw.trans hclosed, hgood⟩

end

end ReedSolomon
