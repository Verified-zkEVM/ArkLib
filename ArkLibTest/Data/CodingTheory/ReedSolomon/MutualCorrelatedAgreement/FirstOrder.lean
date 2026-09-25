/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.CurveAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveTransfer
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridTransfer
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.NormNum

/-!
# First-order curve agreement acceptance tests

Concrete examples exercise first-order power-batched curve bounds and both ordinary-tail hybrid
transfer theorems over the complex field.

## Main statements

* Height-slot and certificate bounds have nonvacuous base-field and extension-field instances.
* Regular-stage, hybrid, and optimized exceptional-set bounds have concrete instances.
* Both ordinary-tail hybrid-transfer bounds have concrete instances.

## References

* [DKT26]
-/

open Polynomial Finset PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative

noncomputable section

private def curveDomain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private def curveValues : Fin 1 → Fin 1 → ℚ := fun _ _ ↦ 0

private theorem curveHeightSurplus :
    firstOrderCurveShiftedRowSlotBound 1 1 2 1 1 1 0 1 <
      firstOrderCurveShiftedHeightSlotCount 1 1 2 1 1 0 1 := by
  norm_num [firstOrderCurveShiftedRowSlotBound, firstOrderGradedRankBound,
    firstOrderGradedSourceCount, firstOrderCurveShiftedHeightSlotCount,
    Finset.sum_range_succ]

/-- The one-point zero curve has a finite first-order curve certificate. -/
private def curveCertificate :
    FirstOrderCurveCertificate (F := ℚ) 1 1 2 1 1 1 1 curveDomain
      (fun i ↦ powerBatchedCoordinate (fun t ↦ curveValues t i))
      (firstOrderColumns (D := 1) (A := 1) (m := 2) (M := 1) (μ := 1)) := by
  exact Classical.choice <| exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    (D := 1) (A := 1) (m := 2) (M := 1) (μ := 1) (k := 1) (h := 1) (n := 1)
    0 (by norm_num) (by norm_num) (by norm_num) curveDomain
    (fun i ↦ powerBatchedCoordinate (fun t ↦ curveValues t i))
    (by intro i; norm_num [powerBatchedCoordinate, curveValues]) curveHeightSurplus

private theorem algebraicClosureInfinite : Infinite (AlgebraicClosure ℚ) := by
  exact Infinite.of_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective

local instance : Infinite (AlgebraicClosure ℚ) := algebraicClosureInfinite
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

/-- The base-field height theorem remains nonvacuous at the tight exponent. -/
example : ∃ z : ℚ, ∃ P : ℚ[X], P.degree < 1 ∧
    1 ≤ (polynomialAgreementSet curveDomain (powerBatchedWord curveValues z) P).card ∧
    HasExactPowerAgreement curveDomain curveValues (RingHom.id ℚ) 1 z P := by
  classical
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
      (F := ℚ) (E := AlgebraicClosure ℚ) (D := 1) (A := 1) (m := 2) (M := 1)
      (μ := 1) (k := 1) (h := 1) (n := 1) (K := 2) (L := 1) (ell := 0)
      curveDomain curveValues (algebraMap ℚ (AlgebraicClosure ℚ))
      (by norm_num) (by norm_num) (by norm_num) curveHeightSurplus
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 1 (taylorExponentSufficient_two_mul_sub_three 0 2)
      (taylorExponentSufficient_two_mul_sub_three 1 2) (by norm_num) (by simp)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨z, 0, by simp, ?_, ?_⟩
  · have hset : polynomialAgreementSet curveDomain (powerBatchedWord curveValues z)
        (0 : ℚ[X]) = Finset.univ := by
      ext i
      simp [polynomialAgreementSet, powerBatchedWord, curveValues]
    rw [hset]
    simp
  · apply hgood z hz 0 (by simp)
    simp [polynomialAgreementSet, powerBatchedWord, curveValues]

/-- A finite first-order curve certificate gives the base-field bound. -/
example : ∃ z : ℚ, ∃ P : ℚ[X], P.degree < 1 ∧
    1 ≤ (polynomialAgreementSet curveDomain (powerBatchedWord curveValues z) P).card ∧
    HasExactPowerAgreement curveDomain curveValues (RingHom.id ℚ) 1 z P := by
  classical
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_certificate_of_exponent
      (D := 1) (A := 1) (m := 2) (M := 1) (μ := 1) (k := 1) (h := 1) (n := 1)
      (K := 2) (L := 1) (ell := 0) curveDomain curveValues
      (algebraMap ℚ (AlgebraicClosure ℚ)) _ curveCertificate
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 1 (taylorExponentSufficient_two_mul_sub_three 0 2)
      (taylorExponentSufficient_two_mul_sub_three 1 2) (by norm_num) (by simp)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨z, 0, by simp, ?_, ?_⟩
  · have hset : polynomialAgreementSet curveDomain (powerBatchedWord curveValues z)
        (0 : ℚ[X]) = Finset.univ := by
      ext i
      simp [polynomialAgreementSet, powerBatchedWord, curveValues]
    rw [hset]
    simp
  · apply hgood z hz 0 (by simp)
    simp [polynomialAgreementSet, powerBatchedWord, curveValues]

/-- The extension-field height theorem gives a challenge with exact power agreement. -/
example : ∃ z : AlgebraicClosure ℚ, ∃ P : (AlgebraicClosure ℚ)[X], P.degree < 1 ∧
    1 ≤ (polynomialAgreementSet
      (curveDomain.trans ⟨algebraMap ℚ (AlgebraicClosure ℚ),
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective⟩)
      (powerBatchedWord (fun t i ↦ algebraMap ℚ (AlgebraicClosure ℚ)
        (curveValues t i)) z) P).card ∧
    HasExactPowerAgreement curveDomain curveValues
      (algebraMap ℚ (AlgebraicClosure ℚ)) 1 z P := by
  classical
  let iota : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  let extensionDomain := curveDomain.trans ⟨iota, iota.injective⟩
  let extensionValues : Fin 1 → Fin 1 → AlgebraicClosure ℚ :=
    fun t i ↦ iota (curveValues t i)
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_extensionExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
      (F := ℚ) (E := AlgebraicClosure ℚ) (D := 1) (A := 1) (m := 2) (M := 1)
      (μ := 1) (k := 1) (h := 1) (n := 1) (K := 2) (L := 1) (ell := 0)
      curveDomain curveValues iota
      (by norm_num) (by norm_num) (by norm_num) curveHeightSurplus
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 1 (taylorExponentSufficient_two_mul_sub_three 0 2)
      (taylorExponentSufficient_two_mul_sub_three 1 2) (by norm_num) (by simp)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  have hset : polynomialAgreementSet extensionDomain (powerBatchedWord extensionValues z)
      (0 : (AlgebraicClosure ℚ)[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, extensionValues, curveValues,
      extensionDomain, curveDomain]
  have hagree : 1 ≤ (polynomialAgreementSet extensionDomain
      (powerBatchedWord extensionValues z) (0 : (AlgebraicClosure ℚ)[X])).card := by
    rw [hset]
    simp
  refine ⟨z, 0, by simp, hagree, ?_⟩
  have h := hgood z hz 0 (by simp) hagree
  convert h using 1

/-- A finite curve certificate also gives a nonvacuous extension-field conclusion. -/
example : ∃ z : AlgebraicClosure ℚ, ∃ P : (AlgebraicClosure ℚ)[X], P.degree < 1 ∧
    1 ≤ (polynomialAgreementSet
      (curveDomain.trans ⟨algebraMap ℚ (AlgebraicClosure ℚ),
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective⟩)
      (powerBatchedWord (fun t i ↦ algebraMap ℚ (AlgebraicClosure ℚ)
        (curveValues t i)) z) P).card ∧
    HasExactPowerAgreement curveDomain curveValues
      (algebraMap ℚ (AlgebraicClosure ℚ)) 1 z P := by
  classical
  let iota : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  let extensionDomain := curveDomain.trans ⟨iota, iota.injective⟩
  let extensionValues : Fin 1 → Fin 1 → AlgebraicClosure ℚ :=
    fun t i ↦ iota (curveValues t i)
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_extensionExceptional_firstOrderCurve_of_certificate_of_exponent
      (D := 1) (A := 1) (m := 2) (M := 1) (μ := 1) (k := 1) (h := 1) (n := 1)
      (K := 2) (L := 1) (ell := 0) curveDomain curveValues iota _ curveCertificate
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 1 (taylorExponentSufficient_two_mul_sub_three 0 2)
      (taylorExponentSufficient_two_mul_sub_three 1 2) (by norm_num) (by simp)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  have hset : polynomialAgreementSet extensionDomain (powerBatchedWord extensionValues z)
      (0 : (AlgebraicClosure ℚ)[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, extensionValues, curveValues,
      extensionDomain, curveDomain]
  have hagree : 1 ≤ (polynomialAgreementSet extensionDomain
      (powerBatchedWord extensionValues z) (0 : (AlgebraicClosure ℚ)[X])).card := by
    rw [hset]
    simp
  refine ⟨z, 0, by simp, hagree, ?_⟩
  have h := hgood z hz 0 (by simp) hagree
  convert h using 1

end

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

private theorem constantOneTail_has_no_root (z : ℂ) (P : Polynomial ℂ)
    (hroot : differentialSpecialization
      (challengeSpecialization (1 : DifferentialPolynomial (Polynomial ℂ) 0) z) P = 0) :
    False := by
  have hroot' : differentialSpecialization (1 : DifferentialPolynomial ℂ 0) P = 0 := by
    simpa only [challengeSpecialization, map_one] using hroot
  have hunit : (Polynomial.C (1 : ℂ) : Polynomial ℂ) = 0 := by
    simpa only [show (1 : DifferentialPolynomial ℂ 0) = MvPolynomial.C 1 by simp,
      differentialSpecialization_C] using hroot'
  exact (Polynomial.C_ne_zero.mpr one_ne_zero) hunit

private def exceptionValues : Fin 2 → Fin 2 → ℂ := fun _ _ ↦ 0

private def exceptionEmbedding : ℂ →+* ℂ := RingHom.id ℂ

private theorem exceptionEquation_coeffNatDegree : coeffNatDegree exceptionEquation = 0 := by
  classical
  rw [coeffNatDegree, exceptionEquation, MvPolynomial.support_X]
  simp

private theorem exceptionOrdinaryTailTransfer :
    HasOrdinaryTailTransfer (D := 1) (A := 2)
      (h := coeffNatDegree exceptionEquation) (mu := 1)
      (e := exceptionDescent.actualDegree) exceptionDomain (exceptionValues 0)
      (exceptionValues 1) exceptionEmbedding exceptionDescent.tail.equation := by
  classical
  refine ⟨∅, ?_, ?_⟩
  · simp [HiddenDerivative.ordinaryTailCharge, exceptionEquation_coeffNatDegree,
      exceptionDescent_actualDegree]
  · intro z hz P hdegree hagree hroot
    rw [exceptionDescent_tail_equation] at hroot
    exact False.elim (constantOneTail_has_no_root z P hroot)

example := exists_exceptional_firstOrder_hybrid_raw_of_tail
  (n := 2) (D := 1) (A := 2) (L := 2) (mu := 1) (M := 1)
  exceptionDomain (exceptionValues 0) (exceptionValues 1) exceptionEmbedding
  exceptionEquation exceptionDescent
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (Or.inl (ringChar.eq_zero : ringChar ℂ = 0)) exceptionOrdinaryTailTransfer

example := exists_exceptional_firstOrder_hybrid_optimized_of_tail
  (n := 2) (D := 1) (A := 2) (mu := 1) (M := 1)
  exceptionDomain (exceptionValues 0) (exceptionValues 1) exceptionEmbedding
  exceptionEquation exceptionDescent
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (Or.inl (ringChar.eq_zero : ringChar ℂ = 0)) exceptionOrdinaryTailTransfer

example :
    ∃ exceptional : Finset ℂ,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.retainedCoordinateRatio 2 2 2 *
            HiddenDerivative.agreementIncidenceRatio 2 1 2 *
              hybridCurveJointStageSum 1 1 (coeffNatDegree exceptionEquation) 1
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
        0 + hybridCurveRegular 2 1 1 2 (coeffNatDegree exceptionEquation)
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
        exact False.elim (constantOneTail_has_no_root z P hroot))

example :
    ∃ exceptional : Finset ℂ,
      (exceptional.card : ℝ) ≤
        hybridCurveOptimized 2 1 1 2 (coeffNatDegree exceptionEquation) 1 1 ∧
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
          exceptionEquation_coeffNatDegree, ordinaryUnifiedPowerFactorAtOrHeight_zero]
          norm_num
        · intro z hz P hdegree hagree hroot
          rw [exceptionDescent_tail_equation] at hroot
          exact False.elim (constantOneTail_has_no_root z P hroot))
