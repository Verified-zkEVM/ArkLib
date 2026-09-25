import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveTransfer
import Mathlib.Analysis.Complex.Polynomial.Basic

open ReedSolomon HiddenDerivative PolynomialDifferential MvPolynomial

private def exceptionDomain : Fin 2 ↪ ℂ where
  toFun i := (i.val : ℂ)
  inj' := by
    intro i j hij
    change (i.val : ℂ) = (j.val : ℂ) at hij
    apply Fin.ext
    exact_mod_cast hij

private noncomputable abbrev exceptionEquation : DifferentialPolynomial (Polynomial ℂ) 1 :=
  MvPolynomial.X (some (1 : Fin 2))

private theorem exceptionEquation_totalDegree : jetTotalDegree exceptionEquation = 1 := by
  rw [jetTotalDegree,
    show exceptionEquation =
      MvPolynomial.monomial (Finsupp.single (some (1 : Fin 2)) 1) 1 by
        rfl,
    MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero]
  rw [Finsupp.weight_single]
  simp [jetDegreeWeight]

private noncomputable def exceptionDescent :
    HiddenDerivative.FirstOrderHybridDescent exceptionEquation 1 1 :=
  Classical.choice (HiddenDerivative.exists_firstOrderHybridDescent exceptionEquation
    (by simp [exceptionEquation])
    (by rw [exceptionEquation_totalDegree])
    (by simp [jetDegree, exceptionEquation, MvPolynomial.degreeOf_X_self])
    (Or.inl (ringChar.eq_zero : ringChar ℂ = 0)))

private theorem exceptionDescent_actualDegree : exceptionDescent.actualDegree = 1 := by
  have hdegree : jetDegree exceptionEquation (1 : Fin 2) = 1 := by
    simp [jetDegree, exceptionEquation, MvPolynomial.degreeOf_X_self]
  exact exceptionDescent.actualDegree_eq.trans hdegree

private theorem exceptionDescent_tail_equation :
    exceptionDescent.tail.equation = (1 : DifferentialPolynomial (Polynomial ℂ) 0) := by
  have h := congrArg JetPrefixPresentation.equation
    (Subsingleton.elim exceptionDescent.tail
      (⟨1, by
        rw [exceptionDescent_actualDegree]
        simp [exceptionEquation, jetDerivative]⟩ :
        JetPrefixPresentation
          (jetDerivative exceptionEquation (1 : Fin 2) exceptionDescent.actualDegree) 0))
  exact h

private def exceptionValues : Fin 2 → Fin 2 → ℂ := fun _ _ ↦ 0

private def exceptionEmbedding : ℂ →+* ℂ := RingHom.id ℂ

private theorem exceptionEquation_height : challengeCoefficientHeight exceptionEquation = 0 := by
  classical
  rw [challengeCoefficientHeight, exceptionEquation, MvPolynomial.support_X]
  simp

example :
    ∃ exceptional : Finset ℂ,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.retainedCoordinateRatio 2 2 2 *
            HiddenDerivative.agreementIncidenceRatio 2 1 2 *
              hybridCurveJointStageSum 1 1 (challengeCoefficientHeight exceptionEquation) 1
                exceptionDescent.actualDegree +
          ((1 : ℕ) : ℝ) * ((2 - 2 : ℕ) : ℝ) *
            HiddenDerivative.fixedCoordinateRatio 2 1 2 *
            HiddenDerivative.regularFiberStageSum 1 1 exceptionDescent.actualDegree ∧
      ∀ z ∉ exceptional, ∀ j < exceptionDescent.actualDegree, ∀ P : Polynomial ℂ,
        P.degree < (↑(1 : ℕ) + 1) →
        2 ≤ (polynomialAgreementSet
          (exceptionDomain.trans ⟨exceptionEmbedding, exceptionEmbedding.injective⟩)
          (powerBatchedWord (fun t i ↦ exceptionEmbedding (exceptionValues t i)) z) P).card →
        differentialSpecialization
            (challengeSpecialization (jetDerivative exceptionEquation (1 : Fin 2) j) z) P = 0 →
        differentialSpecialization
            (separant (challengeSpecialization
              (jetDerivative exceptionEquation (1 : Fin 2) j) z) (1 : Fin 2)) P ≠ 0 →
        HasExactPowerAgreement exceptionDomain exceptionValues exceptionEmbedding (1 + 1 : ℕ)
          z P := by
  classical
  exact exists_exceptional_firstOrder_regularCurveStages
    (n := 2) (D := 1) (A := 2) (L := 2) (mu := 1) (M := 1) (ell := 1)
    exceptionDomain exceptionValues exceptionEmbedding exceptionEquation exceptionDescent
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℂ = 0))

example :
    ∃ exceptional : Finset ℂ,
      (exceptional.card : ℝ) ≤
        0 + hybridCurveRegular 2 1 1 2 (challengeCoefficientHeight exceptionEquation)
          1 exceptionDescent.actualDegree 2 ∧
      ∀ z ∉ exceptional, ∀ P : Polynomial ℂ,
        P.degree < (↑(1 : ℕ) + 1) →
        2 ≤ (polynomialAgreementSet
          (exceptionDomain.trans ⟨exceptionEmbedding, exceptionEmbedding.injective⟩)
          (powerBatchedWord (fun t i ↦ exceptionEmbedding (exceptionValues t i)) z) P).card →
        differentialSpecialization (challengeSpecialization exceptionEquation z) P = 0 →
        HasExactPowerAgreement exceptionDomain exceptionValues exceptionEmbedding (1 + 1 : ℕ)
          z P := by
  classical
  exact exists_exceptional_firstOrder_hybridCurve_of_tail
    (n := 2) (D := 1) (A := 2) (L := 2) (mu := 1) (M := 1) (ell := 1)
    exceptionDomain exceptionValues exceptionEmbedding exceptionEquation exceptionDescent
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℂ = 0)) 0 (by
        refine ⟨∅, by norm_num, ?_⟩
        intro z hz P hdegree hagree hroot
        rw [exceptionDescent_tail_equation] at hroot
        have hroot' : differentialSpecialization (1 : DifferentialPolynomial ℂ 0) P = 0 := by
          simpa only [challengeSpecialization, map_one] using hroot
        have hunit : (Polynomial.C (1 : ℂ) : Polynomial ℂ) = 0 := by
          simpa only [show (1 : DifferentialPolynomial ℂ 0) = MvPolynomial.C 1 by simp,
            differentialSpecialization_C] using hroot'
        exact False.elim ((Polynomial.C_ne_zero.mpr one_ne_zero) hunit))

example :
    ∃ exceptional : Finset ℂ,
      (exceptional.card : ℝ) ≤
        hybridCurveOptimized 2 1 1 2 (challengeCoefficientHeight exceptionEquation) 1 1 ∧
      ∀ z ∉ exceptional, ∀ P : Polynomial ℂ,
        P.degree < (↑(1 : ℕ) + 1) →
        2 ≤ (polynomialAgreementSet
          (exceptionDomain.trans ⟨exceptionEmbedding, exceptionEmbedding.injective⟩)
          (powerBatchedWord (fun t i ↦ exceptionEmbedding (exceptionValues t i)) z) P).card →
        differentialSpecialization (challengeSpecialization exceptionEquation z) P = 0 →
        HasExactPowerAgreement exceptionDomain exceptionValues exceptionEmbedding (1 + 1 : ℕ)
          z P := by
  classical
  exact exists_exceptional_firstOrder_hybridCurve_optimized_of_tail
    (n := 2) (D := 1) (A := 2) (mu := 1) (M := 1) (ell := 1)
    exceptionDomain exceptionValues exceptionEmbedding exceptionEquation exceptionDescent
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℂ = 0)) (by
        intro L₀ hDL₀ hL₀A
        have hL₀ : L₀ = 2 := by omega
        subst L₀
        refine ⟨∅, ?_, ?_⟩
        · rw [hybridCurveTail, exceptionDescent_actualDegree, Nat.sub_self,
          exceptionEquation_height, ordinaryUnifiedPowerFactorAtOrHeight_zero]
          norm_num
        · intro z hz P hdegree hagree hroot
          rw [exceptionDescent_tail_equation] at hroot
          have hroot' : differentialSpecialization (1 : DifferentialPolynomial ℂ 0) P = 0 := by
            simpa only [challengeSpecialization, map_one] using hroot
          have hunit : (Polynomial.C (1 : ℂ) : Polynomial ℂ) = 0 := by
            simpa only [show (1 : DifferentialPolynomial ℂ 0) = MvPolynomial.C 1 by simp,
              differentialSpecialization_C] using hroot'
          exact False.elim ((Polynomial.C_ne_zero.mpr one_ne_zero) hunit))
