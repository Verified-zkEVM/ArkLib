/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.DerivativeImage
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HybridDescent
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.HybridConstants
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.UnifiedBudget

/-!
# Actual-degree first-order stages on polynomial received curves

The reconstruction degree is the actual message degree. The curve degree enters the joint
degree and accidental-agreement terms before summing the actual derivative stages.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon

open HiddenDerivative MvPolynomial HiddenDerivative.SymbolicSeparantChain

noncomputable section

/-- Joint degree summed over the actual regular stages of a received curve. -/
def hybridCurveJ1 (D ell h mu e : ℕ) : ℕ :=
  ∑ i ∈ Finset.range e,
    firstOrderCurveJointStageOne (D + 1) ell h (mu - i) (e - i) (hybridTau D)

/-- Minimum over precisely the admissible integer retention thresholds. -/
def curveRetentionMinimum (D A : ℕ) (charge : ℕ → ℝ) : ℝ :=
  if h : D < A then
    ((Finset.Icc (D + 1) A).image charge).min'
      (Finset.image_nonempty.mpr ⟨D + 1, by simp; omega⟩)
  else 0

/-- Every admissible threshold bounds the finite minimum from above. -/
theorem curveRetentionMinimum_le {D A L : ℕ} (charge : ℕ → ℝ)
    (hDL : D < L) (hLA : L ≤ A) :
    curveRetentionMinimum D A charge ≤ charge L := by
  classical
  unfold curveRetentionMinimum
  rw [dif_pos (hDL.trans_le hLA)]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨L, Finset.mem_Icc.mpr ⟨by omega, hLA⟩, rfl⟩

/-- The finite minimum is attained before any challenge or candidate is chosen. -/
theorem exists_curveRetentionMinimum {D A : ℕ} (charge : ℕ → ℝ) (hDA : D < A) :
    ∃ L, D < L ∧ L ≤ A ∧ charge L = curveRetentionMinimum D A charge := by
  classical
  have hne : ((Finset.Icc (D + 1) A).image charge).Nonempty :=
    Finset.image_nonempty.mpr ⟨D + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨L, hL, heq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
  refine ⟨L, by have := (Finset.mem_Icc.mp hL).1; omega,
    (Finset.mem_Icc.mp hL).2, ?_⟩
  simpa only [curveRetentionMinimum, dif_pos hDA] using heq

/-- The constant-equation tail has its own height charge. -/
def hybridCurveTail (n D ell B H A L : ℕ) : ℝ :=
  if B = 0 then H else (ordinaryUnifiedPowerFactorAt n D ell B H A L : ℝ)

/-- Regular-stage charge with the actual derivative degree, before retention optimization. -/
def hybridCurveRegular (n D ell A H B e L : ℕ) : ℝ :=
  hybridLambdaOne n A L * hybridTheta n D A * hybridCurveJ1 D ell H B e +
    ell * (n - L : ℕ) * hybridLambdaTwo n D L * hybridB1 D B e

/-- The ordinary tail and regular stages choose their thresholds independently. -/
def hybridCurveAtDegree (n D ell A H B e : ℕ) : ℝ :=
  curveRetentionMinimum D A (fun L ↦
    curveRetentionMinimum D A (hybridCurveTail n D ell (B - e) H A) +
      hybridCurveRegular n D ell A H B e L)

/-- The support-uniform bound maximizes only after optimizing at each actual degree. -/
def hybridCurveOptimized (n D ell A H B M : ℕ) : ℝ :=
  ((Finset.range (M + 1)).image (hybridCurveAtDegree n D ell A H B)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Independent threshold optimization is bounded by every admissible pair of thresholds. -/
theorem hybridCurveAtDegree_le_pair {n D ell A H B e L L₀ : ℕ}
    (hDL : D < L) (hLA : L ≤ A) (hDL₀ : D < L₀) (hL₀A : L₀ ≤ A) :
    hybridCurveAtDegree n D ell A H B e ≤
      hybridCurveTail n D ell (B - e) H A L₀ + hybridCurveRegular n D ell A H B e L := by
  unfold hybridCurveAtDegree
  exact (curveRetentionMinimum_le _ hDL hLA).trans
    (add_le_add (curveRetentionMinimum_le _ hDL₀ hL₀A) le_rfl)

/-- The actual derivative-degree entry lies below the outer finite maximum. -/
theorem hybridCurveAtDegree_le_optimized {n D ell A H B M e : ℕ} (heM : e ≤ M) :
    hybridCurveAtDegree n D ell A H B e ≤ hybridCurveOptimized n D ell A H B M := by
  classical
  unfold hybridCurveOptimized
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨e, Finset.mem_range.mpr (by omega), rfl⟩

/-- The sharp regular-curve bound at a first-order descent stage is exactly the corresponding
summand in the raw hybrid arithmetic. -/
theorem regularSymbolicCurveMCADerivativeBoundTwo_eq_hybrid_curve_stage
    {n D A L h mu e j ell : ℕ} (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n) :
    (regularSymbolicCurveMCADerivativeBoundTwo n ell (D + 1) (D + 1) L A
        (mu - j) (e - j) h (HiddenDerivative.hybridTau D) : ℝ) =
      HiddenDerivative.hybridLambdaOne n A L * HiddenDerivative.hybridTheta n D A *
          HiddenDerivative.firstOrderCurveJointStageOne
            (D + 1) ell h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
        ell * (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
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
theorem exists_exceptional_firstOrder_regularCurveStages
    {F E : Type*} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {n D A L h mu M ell : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E) (Q : DifferentialPolynomial E[X] 1)
    (descent : HiddenDerivative.FirstOrderHybridDescent Q mu M h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ D < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.hybridLambdaOne n A L *
            HiddenDerivative.hybridTheta n D A *
              hybridCurveJ1 D ell h mu descent.actualDegree +
          ell * (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
            HiddenDerivative.hybridB1 D mu descent.actualDegree ∧
      ∀ z ∉ exceptional, ∀ j < descent.actualDegree, ∀ P : E[X],
        P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization
            (challengeSpecialization (HiddenDerivative.firstOrderDerivativeStage Q j) z) P = 0 →
        differentialSpecialization
            (separant
              (challengeSpecialization (HiddenDerivative.firstOrderDerivativeStage Q j) z)
              (1 : Fin 2)) P ≠ 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
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
  have hcharE : ringChar E = 0 ∨ D < ringChar E := by
    have heq : ringChar E = ringChar F := by
      let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
      exact ringChar.eq E (ringChar F)
    rwa [heq]
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiK
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_max_char_guard (M := 0) (by simpa using hcharE) (by omega) (by omega)
  have hτ : TaylorExponentSufficient 1 (D + 1) (HiddenDerivative.hybridTau D) := by
    convert taylorExponentSufficient_two_mul_sub_three 1 (K := D + 1) (by omega) using 1
    unfold HiddenDerivative.hybridTau
    omega
  have hstage (j : Fin e) : ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.hybridLambdaOne n A L *
            HiddenDerivative.hybridTheta n D A *
              HiddenDerivative.firstOrderCurveJointStageOne
                (D + 1) ell h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
          ell * (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
            HiddenDerivative.firstOrderCurveFiberStageOne
              (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization
            (challengeSpecialization (HiddenDerivative.firstOrderDerivativeStage Q j) z) P = 0 →
        differentialSpecialization
            (separant
              (challengeSpecialization (HiddenDerivative.firstOrderDerivativeStage Q j) z)
              (1 : Fin 2)) P ≠ 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
    have hj : j.val < e := j.isLt
    have hv : 0 < mu - j := by omega
    have hu : 0 < e - j := by omega
    have huv : e - j ≤ mu - j := Nat.sub_le_sub_right heμ j
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_regularSymbolicCurveMCA_derivativeCapped_of_exponent
        domain values iota
        (HiddenDerivative.firstOrderDerivativeStage Q j) (D + 1) (D + 1) L A
        (mu - j) (e - j) h (HiddenDerivative.hybridTau D) hτ (by
          unfold HiddenDerivative.hybridTau
          omega) (by omega) le_rfl (by omega) (by omega) hLA hAn (by omega) hv hu huv
        (descent.stage_jetWeight_le j (Nat.le_of_lt hj))
        (descent.stage_challengeHeight_le j)
        ((descent.stage_degree j (Nat.le_of_lt hj)).le)
        hbin
    refine ⟨exceptional, ?_, ?_⟩
    · rw [← regularSymbolicCurveMCADerivativeBoundTwo_eq_hybrid_curve_stage hDL hLA hAn]
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
                  (D + 1) ell h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
            ell * (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
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
                  (D + 1) ell h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
            ell * (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
              HiddenDerivative.firstOrderCurveFiberStageOne
                (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D))) =
        ∑ j ∈ Finset.range e,
          (HiddenDerivative.hybridLambdaOne n A L *
              HiddenDerivative.hybridTheta n D A *
                HiddenDerivative.firstOrderCurveJointStageOne
                  (D + 1) ell h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
            ell * (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
              HiddenDerivative.firstOrderCurveFiberStageOne
                (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D)) := by
      exact Fin.sum_univ_eq_sum_range (α := ℝ) (fun j : ℕ ↦
        (HiddenDerivative.hybridLambdaOne n A L *
            HiddenDerivative.hybridTheta n D A *
              HiddenDerivative.firstOrderCurveJointStageOne
                (D + 1) ell h (mu - j) (e - j) (HiddenDerivative.hybridTau D) +
          ell * (n - L : ℕ) * HiddenDerivative.hybridLambdaTwo n D L *
            HiddenDerivative.firstOrderCurveFiberStageOne
              (D + 1) (mu - j) (e - j) (HiddenDerivative.hybridTau D))) e
    rw [hfin]
    simp only [hybridCurveJ1, HiddenDerivative.hybridB1, e,
      Nat.cast_sum]
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
  · intro z hz j hj P hdegree hagree hroot hsep
    have hzj : z ∉ stageExceptional ⟨j, hj⟩ := by
      intro hmem
      apply hz
      exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, hmem⟩
    exact (Classical.choose_spec (hstage ⟨j, hj⟩)).2 z hzj P hdegree hagree hroot hsep


/-- The ordinary tail set and all actual regular `Y₁` stage sets combine into one exceptional
set with the exact raw hybrid charge at the chosen retention split `L`. -/
theorem exists_exceptional_firstOrder_hybridCurve_of_tail
    {F E : Type*} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {n D A L h mu M ell : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E) (Q : DifferentialPolynomial E[X] 1)
    (descent : HiddenDerivative.FirstOrderHybridDescent Q mu M h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ D < ringChar F)
    (tailBound : ℝ)
    (htail : ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ tailBound ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization descent.tail.equation z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        tailBound + hybridCurveRegular n D ell A h mu descent.actualDegree L ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  classical
  obtain ⟨tailExceptional, htailCard, htailGood⟩ := htail
  obtain ⟨regularExceptional, hregularCard, hregularGood⟩ :=
    exists_exceptional_firstOrder_regularCurveStages domain values iota Q descent
      hell hD hDL hLA hAn hchar
  let exceptional := tailExceptional ∪ regularExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardNat : exceptional.card ≤ tailExceptional.card + regularExceptional.card := by
      exact Finset.card_union_le _ _
    have hcardReal : (exceptional.card : ℝ) ≤
        (tailExceptional.card : ℝ) + (regularExceptional.card : ℝ) := by
      exact_mod_cast hcardNat
    apply hcardReal.trans
    unfold hybridCurveRegular
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
    · apply htailGood z hzTail P hdegree hagree
      rw [challengeSpecialization, heval]
      exact htailRoot
    · apply hregularGood z hzRegular j hj P hdegree hagree
      · rw [challengeSpecialization, heval]
        exact hstageRoot
      · rw [challengeSpecialization, heval]
        exact hstageSeparant

/-- Both retention thresholds are chosen before the challenge; the final maximum is over
the permitted actual derivative degrees. The ordinary theorem is supplied independently. -/
theorem exists_exceptional_firstOrder_hybridCurve_optimized_of_tail
    {F E : Type*} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {n D A h mu M ell : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (descent : FirstOrderHybridDescent Q mu M h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ D < ringChar F)
    (htail : ∀ L₀, D < L₀ → L₀ ≤ A → ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        hybridCurveTail n D ell (mu - descent.actualDegree) h A L₀ ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization descent.tail.equation z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ hybridCurveOptimized n D ell A h mu M ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  obtain ⟨L₀, hDL₀, hL₀A, hL₀⟩ := exists_curveRetentionMinimum
    (hybridCurveTail n D ell (mu - descent.actualDegree) h A) hDA
  obtain ⟨L, hDL, hLA, hL⟩ := exists_curveRetentionMinimum
    (fun L ↦ curveRetentionMinimum D A
      (hybridCurveTail n D ell (mu - descent.actualDegree) h A) +
        hybridCurveRegular n D ell A h mu descent.actualDegree L) hDA
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_firstOrder_hybridCurve_of_tail domain values iota Q descent
      hell hD hDL hLA hAn hchar _ (htail L₀ hDL₀ hL₀A)
  refine ⟨exceptional, ?_, hgood⟩
  rw [hL₀, hL] at hcard
  exact hcard.trans (hybridCurveAtDegree_le_optimized descent.actualDegree_le)

end

end ReedSolomon
