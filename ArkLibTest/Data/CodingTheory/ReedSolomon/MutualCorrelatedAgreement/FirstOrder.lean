/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.CurveAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveTransfer
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveRecovery
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveProfile
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthRateBounds
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridTransfer
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.OrdinaryTail
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Profile
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticMcaError
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.RateBounds
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.UniformLineMca
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

/-!
# First-order curve agreement acceptance tests

Concrete examples exercise first-order power-batched curve bounds and both ordinary-tail hybrid
transfer theorems over the complex field.

## Main statements

* Height-slot and certificate bounds have nonvacuous base-field and extension-field instances.
* Regular-stage, hybrid, and optimized exceptional-set bounds have concrete instances.
* Both ordinary-tail hybrid-transfer bounds have concrete instances, with the ordinary-tail
  premise supplied by the order-zero tail of a concrete descent.
* A concrete curve-verified profile gives a base-field challenge with exact power agreement
  through the sharp optimized squarefree bound.
* The hybrid transfer for a nonzero equation has concrete extension-field and base-field
  instances.
* The automatic recipe at rate `1/2` and agreement `3/4`, the rate-slack bounds at slack `1/8`,
  and both finite-field MCA error bounds over `ZMod 2749` have concrete instances.
* The uniform line-agreement bound has a concrete rational instance.
* Optimized curve recovery has concrete instances over an algebraically closed field, over an
  arbitrary field, and from a strict shifted-height slot surplus.
* A verified profile gives exact power agreement at the best optimized envelope.
* A verified profile also gives exact agreement at the optimized hybrid envelope.
* Literal finite-length selectors over four rational evaluation points give a certificate, a
  complete-list bound, and exact correlated agreement outside bounded exceptional sets.
* Automatic finite-length rate bounds give complete lists and exceptional sets over `ℚ`; the
  finite-field consequence bounds constant-code sampling error over `ZMod 2749`.

## References

* [DKT26]
-/

open Polynomial Finset PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative
  ReedSolomon.FirstOrder CoreDefinitions

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
      (exceptionValues 1) exceptionEmbedding exceptionDescent.tail.equation :=
  exceptionDescent.hasOrdinaryTailTransfer exceptionDomain (exceptionValues 0)
    (exceptionValues 1) exceptionEmbedding (by norm_num) (by norm_num) (by norm_num)

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
    (coeffNatDegreeLE_coeffNatDegree _)
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
    (coeffNatDegreeLE_coeffNatDegree _)
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
    (coeffNatDegreeLE_coeffNatDegree _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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

/-! ### Automatic first-order hybrid transfer -/

/-- The hybrid transfer applies to the equation `Y₁` over `ℂ`. -/
example := exists_exceptional_firstOrder_hybrid
  (n := 2) (D := 1) (A := 2) (h := 0) (mu := 1) (M := 1)
  exceptionDomain (exceptionValues 0) (exceptionValues 1) exceptionEmbedding exceptionEquation
  (by simp [exceptionEquation]) exceptionEquation_totalDegree.le
  (by simp [jetDegree, exceptionEquation, MvPolynomial.degreeOf_X_self])
  (MvPolynomial.coeffNatDegreeLE_X _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (Or.inl (ringChar.eq_zero : ringChar ℂ = 0))

/-- The base-field hybrid transfer applies to the same equation, with `ℂ` as the base field. -/
example := exists_exceptional_firstOrder_hybrid_base
  (n := 2) (D := 1) (A := 2) (h := 0) (mu := 1) (M := 1)
  exceptionDomain (exceptionValues 0) (exceptionValues 1) exceptionEquation
  (by simp [exceptionEquation]) exceptionEquation_totalDegree.le
  (by simp [jetDegree, exceptionEquation, MvPolynomial.degreeOf_X_self])
  (MvPolynomial.coeffNatDegreeLE_X _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (Or.inl (ringChar.eq_zero : ringChar ℂ = 0))

private theorem halfRate_threshold_lt_three_quarters :
    firstOrderRateThreshold (1 / 2 : ℝ) < 3 / 4 := by
  rw [firstOrderRateThreshold]
  have hroot : Real.sqrt (27 / 8 : ℝ) < 33 / 16 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 33 / 16)]
    norm_num
  rw [show (1 / 2 : ℝ) * (5 - 1 / 2) * (2 - 1 / 2) = 27 / 8 by norm_num]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 8 - 1 / 2)]
  nlinarith

private def rationalDomain : Fin 4 ↪ ℚ := ⟨![0, 1, 2, 3], by decide⟩

/-- The automatic recipe at rate `1/2` and agreement `3/4` gives the extension-field transfer. -/
example := exists_automaticFirstOrder_hybridEquation (rho := 1 / 2) (a := 3 / 4)
  (n := 4) (D := 1) (A := 3) (k := 2) (by norm_num) (by norm_num)
  halfRate_threshold_lt_three_quarters (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  rationalDomain (fun _ ↦ 0) (fun _ ↦ 1) (algebraMap ℚ ℂ)

/-- The automatic recipe at rate `1/2` and agreement `3/4` gives the base-field transfer. -/
example := exists_automaticFirstOrder_hybridEquation_base (rho := 1 / 2) (a := 3 / 4)
  (n := 4) (D := 1) (A := 3) (k := 2) (by norm_num) (by norm_num)
  halfRate_threshold_lt_three_quarters (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  rationalDomain (fun _ ↦ 0) (fun _ ↦ 1)

/-- The closed exceptional-set bound along a rational received line. -/
example := automatic_first_order_line_agreement (1 / 2) (3 / 4) (by norm_num) (by norm_num)
  halfRate_threshold_lt_three_quarters (by norm_num) 4 2 3 (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (by norm_num) rationalDomain
  (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) (fun _ ↦ 0) (fun _ ↦ 1)

private theorem halfRate_slack_lt_one : firstOrderRateThreshold (1 / 2 : ℝ) + 1 / 8 < 1 := by
  linarith [halfRate_threshold_lt_three_quarters]

private theorem halfRate_finiteLengthDerivativeRatio_le_half :
    finiteLengthDerivativeRatio (1 / 2) (1 / 8) ≤ 1 / 2 := by
  have hrateThreshold : (1 / 2 : ℝ) < firstOrderRateThreshold (1 / 2) :=
    rate_lt_firstOrderRateThreshold (R := 1 / 2) (by norm_num) (by norm_num)
  have hagreement : (1 / 2 : ℝ) <
      automaticAgreement (1 / 2) (firstOrderRateThreshold (1 / 2) + 1 / 8) := by
    rw [automaticAgreement_eq_min]
    apply lt_min
    · linarith [hrateThreshold]
    · linarith [hrateThreshold]
  unfold finiteLengthDerivativeRatio automaticDerivativeRatio firstOrderRateBeta
  norm_num
  linarith

/-- The rate-slack list and line-agreement envelopes over `ℚ` at slack `1/8`. -/
example := automaticFirstOrder_rate_bounds (1 / 2) (1 / 8) 4 2 4 (by norm_num) (by norm_num)
  (by norm_num) halfRate_slack_lt_one (by norm_num) (by norm_num) (by norm_num)
  (by linarith [halfRate_threshold_lt_three_quarters]) (by norm_num) rationalDomain
  (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

local instance : Fact (Nat.Prime 2749) := ⟨by norm_num⟩

private def finiteDomain : Fin 4 ↪ ZMod 2749 := ⟨![0, 1, 2, 3], by decide⟩

/-- At rate `1/2` and slack `1/8`, the derivative cap stays below `2749`. -/
private theorem finiteField_charGuard :
    ringChar (ZMod 2749) = 0 ∨ max (2 - 1)
      (automaticDerivativeCap (1 / 2) (firstOrderRateThreshold (1 / 2) + 1 / 8)) <
        ringChar (ZMod 2749) := by
  refine Or.inr ?_
  have hcap := automaticDerivativeCap_le_inv_eta (rho := 1 / 2) (eta := 1 / 8) (by norm_num)
    (by norm_num) (by norm_num) halfRate_slack_lt_one
  have hgap : 1 / 4 < 1 - firstOrderRateThreshold (1 / 2 : ℝ) := by
    linarith [halfRate_threshold_lt_three_quarters]
  have hfrac : 256 / (3 * (1 - firstOrderRateThreshold (1 / 2 : ℝ))) < 1024 / 3 := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hbound : (automaticDerivativeCap (1 / 2) (firstOrderRateThreshold (1 / 2) + 1 / 8) : ℝ) <
      2749 := by
    refine hcap.trans_lt ?_
    unfold automaticMultiplicityBoundConstant automaticRateGap
    linarith
  rw [ZMod.ringChar_zmod_n]
  exact max_lt (by norm_num) (by exact_mod_cast hbound)

/-- The finite-field line MCA error bounds over `ZMod 2749`. -/
example := automaticFirstOrder_hybrid_mcaError_le (rho := 1 / 2)
  (a := firstOrderRateThreshold (1 / 2) + 1 / 8) (n := 4) (k := 2) (by norm_num) (by norm_num)
  (by linarith) halfRate_slack_lt_one (by norm_num) (by norm_num) (by norm_num) finiteDomain
  finiteField_charGuard

/-- The quintic slack envelope bounds the line MCA error over `ZMod 2749`. -/
example := automaticFirstOrder_rate_mcaError_le (1 / 2) (1 / 8) 4 2 (by norm_num) (by norm_num)
  (by norm_num) halfRate_slack_lt_one (by norm_num) (by norm_num) (by norm_num) finiteDomain
  finiteField_charGuard

private def uniformLineDomain : Fin 3 ↪ ℚ := ⟨![0, 1, 2], by decide⟩

/-- The uniform line-agreement bound applies at `n = 3`, `k = 2` and `A = 3` over `ℚ`. -/
example := exists_uniformFirstOrder_lineMca_of_two_le 3 2 3 uniformLineDomain (fun _ ↦ 0)
  (fun _ ↦ 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

/-- Optimized curve recovery over `ℂ` applies to the equation `Y₁`. -/
example := exists_exceptional_firstOrder_hybridCurve_optimized
  (n := 2) (D := 1) (A := 2) (h := 0) (mu := 1) (M := 1)
  exceptionDomain exceptionValues exceptionEmbedding exceptionEquation
  (by simp [exceptionEquation]) exceptionEquation_totalDegree.le
  (by simp [jetDegree, exceptionEquation, MvPolynomial.degreeOf_X_self])
  (coeffNatDegreeLE_X _)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (Or.inl (ringChar.eq_zero : ringChar ℂ = 0))

/-- The base-field form applies to the same equation, with the algebraic closure internal. -/
example := exists_baseExceptional_firstOrder_hybridCurve_optimized
  (n := 2) (D := 1) (A := 2) (h := 0) (mu := 1) (M := 1)
  exceptionDomain exceptionValues exceptionEquation
  (by simp [exceptionEquation]) exceptionEquation_totalDegree.le
  (by simp [jetDegree, exceptionEquation, MvPolynomial.degreeOf_X_self])
  (coeffNatDegreeLE_X _)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (Or.inl (ringChar.eq_zero : ringChar ℂ = 0))

private def recoveryDomain : Fin 3 ↪ ℚ where
  toFun i := (i.val : ℚ)
  inj' := by
    intro i j hij
    change (i.val : ℚ) = (j.val : ℚ) at hij
    exact Fin.ext (by exact_mod_cast hij)

private def recoveryValues : Fin 2 → Fin 3 → ℚ := fun _ _ ↦ 0

private theorem recoveryHeightSurplus :
    firstOrderCurveShiftedRowSlotBound 1 3 1 0 1 3 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 3 1 0 1 1 1 := by
  norm_num [firstOrderCurveShiftedRowSlotBound, firstOrderGradedRankBound,
    firstOrderGradedSourceCount, firstOrderCurveShiftedHeightSlotCount,
    Finset.sum_range_succ]

/-- A shifted-height slot surplus at three rational points below full dimension gives optimized
curve recovery: outside the exceptional set, the zero candidate has exact power agreement. -/
example : ∃ z : ℚ, ∃ P : ℚ[X], P.degree < 2 ∧
    3 ≤ (polynomialAgreementSet recoveryDomain (powerBatchedWord recoveryValues z) P).card ∧
    HasExactPowerAgreement recoveryDomain recoveryValues (RingHom.id ℚ) 2 z P := by
  obtain ⟨exceptional, _, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized
      (D := 1) (A := 3) (m := 1) (M := 0) (mu := 1) (h := 1) recoveryDomain recoveryValues
      le_rfl (by norm_num) recoveryHeightSurplus (by norm_num) (by norm_num) le_rfl
      (Or.inr (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  have hagree : 3 ≤ (polynomialAgreementSet recoveryDomain
      (powerBatchedWord recoveryValues z) (0 : ℚ[X])).card := by
    have hset : polynomialAgreementSet recoveryDomain (powerBatchedWord recoveryValues z)
        (0 : ℚ[X]) = Finset.univ := by
      ext i
      simp [polynomialAgreementSet, powerBatchedWord, recoveryValues]
    rw [hset]
    simp
  have hdegree : (0 : ℚ[X]).degree < 2 := by
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe 2
  exact ⟨z, 0, hdegree, hagree, hgood z hz 0 hdegree hagree⟩

private def ternaryLineDomain : Fin 3 ↪ ZMod 3 := ⟨![0, 1, 2], by decide⟩

/-- The uniform line-agreement bound applies over `ZMod 3` at `k = 2`, where the characteristic is
below the first-order derivative cap. -/
example := exists_uniformFirstOrder_lineMca 3 2 3 ternaryLineDomain (fun _ ↦ 0) (fun _ ↦ 1)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (Or.inr (by rw [ZMod.ringChar_zmod_n]; norm_num))

/-! ### Sharp squarefree profile bound -/

/-- A curve-verified profile at `n = k = A = 2` with derivative cap `1`. -/
private def sharpSquarefreeProfile : ReedSolomon.HiddenDerivative.CurveProfile.LineProfile :=
  { n := 2
    k := 2
    agreement := 2
    multiplicity := 1
    firstDerivativeCap := 1
    totalJetCap := 1
    batchingDegree := 1
    supportDimension := 5
    localRank := 2
    columnY₀Weight := 1
    height := 1
    heightSlots := 9 }

private def sharpProfileDomain : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ (i.val : ℚ), fun i j h ↦ by
    change (i.val : ℚ) = (j.val : ℚ) at h
    exact Fin.ext (by exact_mod_cast h)⟩

private def sharpProfileValues : Fin 2 → Fin 2 → ℚ := fun _ _ ↦ 0

/-- The sharp optimized profile bound gives a base-field challenge at which the zero polynomial
has exact power agreement with the zero line. -/
example : ∃ z : ℚ, HasExactPowerAgreement sharpProfileDomain sharpProfileValues
    (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, -, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_squarefreeSharpOptimized
      (E := AlgebraicClosure ℚ) (p := sharpSquarefreeProfile) (by decide) 2
      ⟨le_rfl, le_rfl, le_rfl⟩ Nat.one_pos le_rfl le_rfl sharpProfileDomain
      sharpProfileValues (algebraMap ℚ (AlgebraicClosure ℚ))
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨z, hgood z hz 0 (WithBot.bot_lt_coe 2) (by
    norm_num [sharpSquarefreeProfile, polynomialAgreementSet, powerBatchedWord,
      sharpProfileValues])⟩

open Classical in
/-- The best optimized profile bound gives one exceptional set and a good rational challenge. -/
example :
    letI : DecidableEq ℚ := Classical.decEq ℚ
    ∃ exceptional : Finset ℚ,
    (exceptional.card : ℝ) ≤ bestOptimizedCurveEnvelope sharpSquarefreeProfile 2 ∧
    ∃ z ∉ exceptional, HasExactPowerAgreement sharpProfileDomain sharpProfileValues
      (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_bestOptimized
      (E := AlgebraicClosure ℚ) (p := sharpSquarefreeProfile) (by decide) 2
      ⟨le_rfl, le_rfl, le_rfl⟩ (by norm_num [sharpSquarefreeProfile]) le_rfl le_rfl
      sharpProfileDomain
      sharpProfileValues (algebraMap ℚ (AlgebraicClosure ℚ))
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨exceptional, hcard, z, hz, hgood z hz 0 (WithBot.bot_lt_coe 2) (by
    norm_num [sharpSquarefreeProfile, polynomialAgreementSet, powerBatchedWord,
      sharpProfileValues])⟩

noncomputable local instance : DecidableEq ℚ := Classical.decEq ℚ

/-- The optimized hybrid profile also gives a bounded exceptional set and exact agreement for
the zero polynomial on the verified rational curve. -/
example : ∃ exceptional : Finset ℚ,
    (exceptional.card : ℝ) ≤ hybridOptimizedCurveEnvelope sharpSquarefreeProfile ∧
    ∃ z ∉ exceptional, HasExactPowerAgreement sharpProfileDomain sharpProfileValues
      (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_hybridOptimized
      (p := sharpSquarefreeProfile) (by decide) le_rfl le_rfl
      (by norm_num [sharpSquarefreeProfile]) sharpProfileDomain sharpProfileValues
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, hcard, z, hz, ?_⟩
  simpa only [sharpSquarefreeProfile] using hgood z hz 0 (WithBot.bot_lt_coe 2) (by
    norm_num [sharpSquarefreeProfile, polynomialAgreementSet, powerBatchedWord,
      sharpProfileValues])

/-! ### Finite-length selectors and rate bounds -/

/-- At rate `1/2`, the literal finite-length selectors give a symbolic certificate for a
four-point rational zero line. -/
private theorem rationalFiniteLengthZeroCertificate :
    Nonempty (FirstOrderSymbolicCertificate (F := ℚ) 1 4
      (finiteLengthMultiplicity (1 / 2) (1 / 8) 4)
      (finiteLengthDerivativeCap (1 / 2) (1 / 8) 4)
      (finiteLengthJetDegree (1 / 2) (1 / 8) 4) 2
      (finiteLengthChallengeHeight (1 / 2) (1 / 8) 4)
      rationalDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (firstOrderColumns (D := 1) (A := 4)
        (m := finiteLengthMultiplicity (1 / 2) (1 / 8) 4)
        (M := finiteLengthDerivativeCap (1 / 2) (1 / 8) 4)
        (μ := finiteLengthJetDegree (1 / 2) (1 / 8) 4))) := by
  exact exists_finiteLengthFirstOrder_symbolicCertificate
    (rho := 1 / 2) (eta := 1 / 8) (n := 4) (k := 2) (A := 4)
    (by norm_num) (by norm_num) (by norm_num) halfRate_slack_lt_one (by norm_num)
    halfRate_finiteLengthDerivativeRatio_le_half (by norm_num) (by norm_num)
    (by nlinarith [halfRate_slack_lt_one]) rationalDomain (fun _ ↦ 0) (fun _ ↦ 0)

private noncomputable def rationalFiniteLengthZeroCertificateValue :=
  Classical.choice rationalFiniteLengthZeroCertificate

/-- A four-point zero word belongs to a finite complete list with the literal selector bound. -/
example :
    (closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4).Finite ∧
    (0 : ℚ[X]) ∈ closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4 ∧
    ((closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4).ncard : ℝ) ≤
      7 * finiteLengthMcaParameterConstant (1 / 2) ^ 3 * 4 /
        finiteLengthSlack (1 / 8) 4 ^ 2 := by
  obtain ⟨hfinite, hcard⟩ :=
    closePolynomialSet_finite_and_card_le_finiteLength_of_selector_certificate
      (rho := 1 / 2) (eta := 1 / 8) (n := 4) (k := 2) (A := 4)
      (by norm_num) (by norm_num) (by norm_num) halfRate_slack_lt_one
      (by norm_num) halfRate_finiteLengthDerivativeRatio_le_half
      (by norm_num) (by nlinarith [halfRate_slack_lt_one]) (by norm_num)
      rationalDomain (fun _ ↦ 0)
      (firstOrderColumns (D := 1) (A := 4)
        (m := finiteLengthMultiplicity (1 / 2) (1 / 8) 4)
        (M := finiteLengthDerivativeCap (1 / 2) (1 / 8) 4)
        (μ := finiteLengthJetDegree (1 / 2) (1 / 8) 4))
      rationalFiniteLengthZeroCertificateValue
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  refine ⟨hfinite, ?_, hcard⟩
  change (0 : ℚ[X]).degree < 2 ∧
    4 ≤ (polynomialAgreementSet rationalDomain (fun _ ↦ 0) 0).card
  constructor
  · exact WithBot.bot_lt_coe 2
  · norm_num [polynomialAgreementSet, rationalDomain]

/-- The literal selector certificate bounds exceptional challenges, and a zero candidate has
exact correlated agreement outside that set. -/
example : ∃ exceptional : Finset ℚ,
    (exceptional.card : ℝ) ≤
      140 * finiteLengthMcaParameterConstant (1 / 2) ^ 6 * 4 ^ 2 /
        finiteLengthSlack (1 / 8) 4 ^ 4 ∧
    ∃ z ∉ exceptional,
      HasExactCorrelatedPair rationalDomain (fun _ ↦ 0) (fun _ ↦ 0)
        (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_finiteLengthMca_of_selector_certificate
      (E := AlgebraicClosure ℚ) (rho := 1 / 2) (eta := 1 / 8)
      (n := 4) (k := 2) (A := 4)
      (by norm_num) (by norm_num) (by norm_num) halfRate_slack_lt_one
      (by norm_num) halfRate_finiteLengthDerivativeRatio_le_half
      (by norm_num) (by norm_num) (by nlinarith [halfRate_slack_lt_one])
      (by norm_num) rationalDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (algebraMap ℚ (AlgebraicClosure ℚ))
      (firstOrderColumns (D := 1) (A := 4)
        (m := finiteLengthMultiplicity (1 / 2) (1 / 8) 4)
        (M := finiteLengthDerivativeCap (1 / 2) (1 / 8) 4)
        (μ := finiteLengthJetDegree (1 / 2) (1 / 8) 4))
      rationalFiniteLengthZeroCertificateValue
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨exceptional, hcard, z, hz,
    hgood z hz 0 (WithBot.bot_lt_coe 2) (by
      norm_num [polynomialAgreementSet, rationalDomain])⟩

/-- The same zero word has both a bounded complete list and a nonexceptional exact correlated
pair under the combined finite-length theorem. -/
example :
    ((closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4).Finite ∧
      ((closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4).ncard : ℝ) ≤
        7 * finiteLengthMcaParameterConstant (1 / 2) ^ 3 * 4 /
          finiteLengthSlack (1 / 8) 4 ^ 2) ∧
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤
        140 * finiteLengthMcaParameterConstant (1 / 2) ^ 6 * 4 ^ 2 /
          finiteLengthSlack (1 / 8) 4 ^ 4 ∧
      ∃ z ∉ exceptional,
        HasExactCorrelatedPair rationalDomain (fun _ ↦ 0) (fun _ ↦ 0)
          (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨hlist, exceptional, hcard, hgood⟩ :=
    finiteLength_completeList_and_exceptionalMca_of_selector_certificates
      (E := AlgebraicClosure ℚ) (rho := 1 / 2) (eta := 1 / 8)
      (n := 4) (k := 2) (A := 4)
      (by norm_num) (by norm_num) (by norm_num) halfRate_slack_lt_one
      (by norm_num) halfRate_finiteLengthDerivativeRatio_le_half
      (by norm_num) (by norm_num) (by nlinarith [halfRate_slack_lt_one])
      (by norm_num) rationalDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (algebraMap ℚ (AlgebraicClosure ℚ))
      (firstOrderColumns (D := 1) (A := 4)
        (m := finiteLengthMultiplicity (1 / 2) (1 / 8) 4)
        (M := finiteLengthDerivativeCap (1 / 2) (1 / 8) 4)
        (μ := finiteLengthJetDegree (1 / 2) (1 / 8) 4))
      (firstOrderColumns (D := 1) (A := 4)
        (m := finiteLengthMultiplicity (1 / 2) (1 / 8) 4)
        (M := finiteLengthDerivativeCap (1 / 2) (1 / 8) 4)
        (μ := finiteLengthJetDegree (1 / 2) (1 / 8) 4))
      rationalFiniteLengthZeroCertificateValue rationalFiniteLengthZeroCertificateValue
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨hlist, exceptional, hcard, z, hz,
    hgood z hz 0 (WithBot.bot_lt_coe 2) (by
      norm_num [polynomialAgreementSet, rationalDomain])⟩

/-- Automatic finite-length bounds make the four-point rational zero list finite and give a
nonexceptional exact correlated pair with the exact finite-length slack. -/
example :
    ((closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4).Finite ∧
      ((closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4).ncard : ℝ) ≤
        7 * finiteLengthMcaParameterConstant (1 / 2) ^ 3 * 4 /
          finiteLengthSlack (1 / 8) 4 ^ 2) ∧
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤
        140 * finiteLengthMcaParameterConstant (1 / 2) ^ 6 * 4 ^ 2 /
          finiteLengthSlack (1 / 8) 4 ^ 4 ∧
      ∃ z ∉ exceptional,
        HasExactCorrelatedPair rationalDomain (fun _ ↦ 0) (fun _ ↦ 0)
          (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨hlist, hline⟩ := automaticFirstOrder_finiteLength_finiteSlack_bounds
    (1 / 2) (1 / 8) 4 2 4 (by norm_num) (by norm_num) (by norm_num)
    halfRate_slack_lt_one halfRate_finiteLengthDerivativeRatio_le_half
    (by norm_num) (by norm_num) (by nlinarith [halfRate_slack_lt_one])
    (by norm_num) rationalDomain
    (Or.inr (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)))
  obtain ⟨exceptional, hcard, hgood⟩ := hline (fun _ ↦ 0) (fun _ ↦ 0)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨hlist (fun _ ↦ 0), exceptional, hcard, z, hz,
    hgood z hz 0 (WithBot.bot_lt_coe 2) (by
      norm_num [polynomialAgreementSet, rationalDomain])⟩

/-- The inverse-`eta` automatic bounds retain both a finite rational zero list and exact
agreement at a challenge outside the exceptional set. -/
example :
    ((closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4).Finite ∧
      ((closePolynomialSet rationalDomain (fun _ ↦ 0) 2 4).ncard : ℝ) ≤
        7 * finiteLengthMcaParameterConstant (1 / 2) ^ 3 * 4 / (1 / 8) ^ 2) ∧
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤
        140 * finiteLengthMcaParameterConstant (1 / 2) ^ 6 * 4 ^ 2 / (1 / 8) ^ 4 ∧
      ∃ z ∉ exceptional,
        HasExactCorrelatedPair rationalDomain (fun _ ↦ 0) (fun _ ↦ 0)
          (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨hlist, hline⟩ := automaticFirstOrder_finiteLength_rate_bounds
    (1 / 2) (1 / 8) 4 2 4 (by norm_num) (by norm_num) (by norm_num)
    halfRate_slack_lt_one halfRate_finiteLengthDerivativeRatio_le_half
    (by norm_num) (by norm_num) (by nlinarith [halfRate_slack_lt_one])
    (by norm_num) rationalDomain
    (Or.inr (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)))
  obtain ⟨exceptional, hcard, hgood⟩ := hline (fun _ ↦ 0) (fun _ ↦ 0)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨hlist (fun _ ↦ 0), exceptional, hcard, z, hz,
    hgood z hz 0 (WithBot.bot_lt_coe 2) (by
      norm_num [polynomialAgreementSet, rationalDomain])⟩

/-- The finite-field automatic bound controls sampling error for the four-point constant code
over `ZMod 2749`. -/
example :
    mcaError (AffineLineGenerator (ZMod 2749)) (code finiteDomain 1)
        (1 - (firstOrderRateThreshold (1 / 2) + 1 / 8)) ≤
      min 1 (ENNReal.ofReal
        ((140 * finiteLengthMcaParameterConstant (1 / 2) ^ 6 * 4 ^ 2 /
          (1 / 8) ^ 4) / (Fintype.card (ZMod 2749) : ℝ))) := by
  exact automaticFirstOrder_finiteLength_mcaError_le
    (1 / 2) (1 / 8) 4 1 (by norm_num) (by norm_num) (by norm_num)
    halfRate_slack_lt_one halfRate_finiteLengthDerivativeRatio_le_half
    (by norm_num) (by norm_num) finiteDomain (Or.inl rfl)
