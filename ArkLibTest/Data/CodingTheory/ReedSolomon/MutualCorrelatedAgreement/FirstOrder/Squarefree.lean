/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Factorwise
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.TailBound
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Certificates
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.RetainedTail
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CurveMCA
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.SharpCurve
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NormNum

/-!
# Squarefree agreement acceptance tests

Concrete rational examples check factorwise and squarefree certificate counts, retained-tail
routing, degree envelopes, challenge heights, nonvanishing, and the line and sharp certificate
theorems.
-/

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.FirstOrder.Squarefree ReedSolomon.HiddenDerivative

private def factorwiseDomain : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ (i.val : ℚ), fun i j h ↦ by
    change (i.val : ℚ) = (j.val : ℚ) at h
    have h' : i.val = j.val := by exact_mod_cast h
    exact Fin.ext h'⟩

private def factorwiseReceived : Fin 2 → ℚ := fun _ ↦ 0

private noncomputable abbrev factorwiseEquation : DifferentialPolynomial ℚ 1 :=
  MvPolynomial.X (some (0 : Fin 2))

private noncomputable def factorwiseTail : FixedWordSingularTail factorwiseEquation 1 1 where
  equation := MvPolynomial.X (some (0 : Fin 1))
  nonzero := MvPolynomial.X_ne_zero _
  degree_le := by
    change weightedTotalDegree jetDegreeWeight
      (MvPolynomial.monomial (Finsupp.single (some (0 : Fin 1)) 1) (1 : ℚ)) ≤ _
    rw [weightedTotalDegree_monomial _ _ _ (by norm_num)]
    simp [Finsupp.weight_single, jetDegreeWeight, ordinaryDegreeEnvelope]
  routes_nonregular := by
    intro P hroot _
    rw [differentialSpecialization_jet] at hroot ⊢
    exact hroot

private noncomputable def factorwiseChosenTail :
    FixedWordRegularTail factorwiseEquation (1 : DifferentialPolynomial ℚ 1) 1 1 where
  regular_degree_zero := by
    intro _
    rfl
  equation := MvPolynomial.X (some (0 : Fin 1))
  nonzero := MvPolynomial.X_ne_zero _
  degree_le := by
    change weightedTotalDegree jetDegreeWeight
      (MvPolynomial.monomial (Finsupp.single (some (0 : Fin 1)) 1) (1 : ℚ)) ≤ _
    rw [weightedTotalDegree_monomial _ _ _ (by norm_num)]
    simp [Finsupp.weight_single, jetDegreeWeight, ordinaryDegreeEnvelope]
  routes_nonregular := by
    intro P hroot _
    rw [differentialSpecialization_jet] at hroot ⊢
    exact hroot

private noncomputable def factorwiseSolutions : Finset ℚ[X] := {0}

private theorem factorwise_solutions_are_roots :
    ∀ P ∈ factorwiseSolutions,
      differentialSpecialization factorwiseEquation P = 0 := by
  intro P hP
  simp only [factorwiseSolutions, Finset.mem_singleton] at hP
  subst P
  change differentialSpecialization
    (MvPolynomial.X (some (0 : Fin 2)) : DifferentialPolynomial ℚ 1) 0 = 0
  rw [differentialSpecialization_jet]
  simp

example :
    (factorwiseSolutions.card : ℝ) ≤
      (firstOrderCurveFiberStageOne 2
          (jetTotalDegree (radicalPrimPart (some (1 : Fin 2)) factorwiseEquation))
          (jetDegree (radicalPrimPart (some (1 : Fin 2)) factorwiseEquation) 1)
          (regularTaylorExponent 1) : ℝ) *
          ((2 - 1 : ℕ) : ℝ) / (2 - 1 : ℕ) + ordinaryDegreeEnvelope 1 1 := by
  exact finite_factorwise_agreement_solutions_card_le_actual
    factorwiseDomain factorwiseReceived factorwiseEquation (by norm_num) (by norm_num)
    (by norm_num) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
    factorwiseTail factorwiseSolutions
    factorwise_solutions_are_roots (by
      intro P hP
      simp only [factorwiseSolutions, Finset.mem_singleton] at hP
      subst P
      constructor
      · exact WithBot.bot_lt_coe 2
      · norm_num [factorwiseReceived, factorwiseDomain])

private theorem certificateWithPositiveDerivativeCap :
    Nonempty (FirstOrderSymbolicCertificate (F := ℚ) 1 2 1 1 1 2 1
      factorwiseDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1))) := by
  have hheight : firstOrderCurveShiftedRowSlotBound 1 2 1 1 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 1 1 1 1 1 := by decide
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (F := ℚ) (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1) (k := 2) (h := 1)
    (by norm_num) (by norm_num) (by norm_num) factorwiseDomain (fun _ ↦ 0) (fun _ ↦ 0)
    hheight

private noncomputable def certificateSolutions : Finset ℚ[X] := {0}

/-- A concrete symbolic certificate with a positive derivative cap bounds an actual solution. -/
example :
    (certificateSolutions.card : ℝ) ≤
      (firstOrderCurveFiberStageOne 2 1 1 (regularTaylorExponent 1) : ℝ) *
          ((2 - 2 + 1 : ℕ) : ℝ) / (2 - 2 + 1 : ℕ) +
        ordinaryDegreeEnvelope 1 1 := by
  obtain ⟨cert⟩ := certificateWithPositiveDerivativeCap
  exact firstOrder_finite_agreement_solutions_card_le_squarefree
    (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1) (k := 2) (h := 1) (n := 2)
    factorwiseDomain (fun _ ↦ 0)
    (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1)) cert
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
    certificateSolutions (by
      intro P hP
      simp only [certificateSolutions, Finset.mem_singleton] at hP
      subst P
      constructor
      · exact WithBot.bot_lt_coe 2
      · norm_num [factorwiseDomain])

example :
    (factorwiseSolutions.card : ℝ) ≤
      (firstOrderCurveFiberStageOne 2
          (jetTotalDegree (1 : DifferentialPolynomial ℚ 1))
          (jetDegree (1 : DifferentialPolynomial ℚ 1) 1)
          (regularTaylorExponent 1) : ℝ) *
          ((2 - 1 : ℕ) : ℝ) / (2 - 1 : ℕ) + ordinaryDegreeEnvelope 1 1 := by
  exact finite_factorwise_agreement_solutions_card_le_actual_of_regular_equation
    (n := 2) (D := 1) (A := 2) (B := 1) (M := 1)
    factorwiseDomain factorwiseReceived factorwiseEquation (1 : DifferentialPolynomial ℚ 1)
    (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) factorwiseChosenTail
    factorwiseSolutions factorwise_solutions_are_roots (by
      intro P hP
      simp only [factorwiseSolutions, Finset.mem_singleton] at hP
      subst P
      constructor
      · exact WithBot.bot_lt_coe 2
      · norm_num [factorwiseReceived, factorwiseDomain])

example :
    (factorwiseSolutions.card : ℝ) ≤
      (firstOrderCurveFiberStageOne 2 1 1 (regularTaylorExponent 1) : ℝ) *
          ((2 - 1 : ℕ) : ℝ) / (2 - 1 : ℕ) + ordinaryDegreeEnvelope 1 1 := by
  exact finite_factorwise_agreement_solutions_card_le_of_regular_equation
    (n := 2) (D := 1) (A := 2) (B := 1) (M := 1)
    factorwiseDomain factorwiseReceived factorwiseEquation (1 : DifferentialPolynomial ℚ 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      change weightedTotalDegree jetDegreeWeight
        (1 : MvPolynomial (JetVariable 1) ℚ) ≤ 1
      rw [← MvPolynomial.C_1, MvPolynomial.weightedTotalDegree_C]
      exact Nat.zero_le 1)
    (by simp [jetDegree])
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) factorwiseChosenTail
    factorwiseSolutions factorwise_solutions_are_roots (by
      intro P hP
      simp only [factorwiseSolutions, Finset.mem_singleton] at hP
      subst P
      constructor
      · exact WithBot.bot_lt_coe 2
      · norm_num [factorwiseReceived, factorwiseDomain])

private theorem retainedCurveTransferTest_jetTotalDegree :
    jetTotalDegree
      (MvPolynomial.X (some (0 : Fin 2)) :
        DifferentialPolynomial (AlgebraicClosure ℚ)[X] 1) ≤ 1 := by
  refine (jetTotalDegree_le_iff _ 1).mpr fun u hu ↦ ?_
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hu
  rw [hu]
  simp [totalJetDegree_eq_sum, Fin.sum_univ_two]

noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

/-- A concrete retained squarefree equation has a bounded exact-agreement exceptional set. -/
example :
    ∃ exceptional : Finset (AlgebraicClosure ℚ),
      (exceptional.card : ℝ) ≤
        retainedSquarefreeCurveAgreementCharge
          (agreementIncidenceRatio 2 1 2) 2 1 0 2 2 1 1 1 ∧
      ∀ z ∉ exceptional, ∀ P : (AlgebraicClosure ℚ)[X], P.degree < 2 →
        2 ≤ (ReedSolomon.polynomialAgreementSet
          (factorwiseDomain.trans ⟨algebraMap ℚ (AlgebraicClosure ℚ),
            (algebraMap ℚ (AlgebraicClosure ℚ)).injective⟩)
          (ReedSolomon.powerBatchedWord
            (fun (_ : Fin 1) (i : Fin 2) ↦ algebraMap ℚ (AlgebraicClosure ℚ)
              (factorwiseReceived i)) z) P).card →
        differentialSpecialization
          (challengeSpecialization
            (MvPolynomial.X (some (0 : Fin 2)) :
              DifferentialPolynomial (AlgebraicClosure ℚ)[X] 1) z) P = 0 →
        ReedSolomon.HasExactPowerAgreement factorwiseDomain
          (fun (_ : Fin 1) (i : Fin 2) ↦ factorwiseReceived i)
          (algebraMap ℚ (AlgebraicClosure ℚ)) 2 z P := by
  classical
  let iota : ℚ →+* AlgebraicClosure ℚ := algebraMap _ _
  let values : Fin 1 → Fin 2 → ℚ := fun _ i ↦ factorwiseReceived i
  let Q : DifferentialPolynomial (AlgebraicClosure ℚ)[X] 1 :=
    MvPolynomial.X (some (0 : Fin 2))
  have hQ : Q ≠ 0 := MvPolynomial.X_ne_zero _
  have hjet : jetTotalDegree Q ≤ 1 := retainedCurveTransferTest_jetTotalDegree
  have hderiv : Q.degreeOf (some (1 : Fin 2)) ≤ 1 := by
    change degreeOf (some (1 : Fin 2))
      (MvPolynomial.X (some (0 : Fin 2)) :
        DifferentialPolynomial (AlgebraicClosure ℚ)[X] 1) ≤ 1
    rw [degreeOf_X_of_ne (by decide)]
    norm_num
  have hheight : CoeffNatDegreeLE Q 1 :=
    (coeffNatDegreeLE_X _).mono (by omega)
  have htail : HasRetainedOrdinaryCurveAgreementTransfer
      (D := 1) (A := 2) (B := 1) (M := 1) (H := 1)
      factorwiseDomain values iota (singularCurveEquation Q) := by
    refine ⟨∅, ?_, ?_⟩
    · norm_num [retainedOrdinaryCurveAgreementCharge, agreementIncidenceRatio]
    · intro z hz P hdegree hagree hroot
      exact ReedSolomon.hasExactPowerAgreement_singleton
        factorwiseDomain values iota 2 z P hdegree hagree
  exact exists_exceptional_retainedSquarefreeCurveAgreement_of_tail
    (D := 1) (ell := 0) (L := 2) (A := 2) (B := 1) (M := 1) (H := 1)
    factorwiseDomain values iota Q hQ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hjet hderiv hheight (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) htail

private noncomputable abbrev retainedTailTestEquation : DifferentialPolynomial ℚ[X] 1 :=
  MvPolynomial.X (some (0 : Fin 2))

private theorem retainedTailTest_positiveEquation :
    positiveCurveEquation retainedTailTestEquation = 1 := by
  have hcoordinates :
      challengeRetainingRootFirst retainedTailTestEquation =
        (MvPolynomial.X (some (some (0 : Fin 2))) :
          MvPolynomial (Option (JetVariable 1)) ℚ) := by
    simp [challengeRetainingRootFirst, retainedTailTestEquation, Equiv.swap_apply_def]
  have hrootDegree :
      degreeOf none (challengeRetainingRootFirst retainedTailTestEquation) = 0 := by
    rw [hcoordinates]
    rw [degreeOf_X_of_ne (by decide)]
  have hpositiveDegree :
      degreeOf none (radicalPrimPart none
        (challengeRetainingRootFirst retainedTailTestEquation)) = 0 :=
    le_antisymm
      ((degreeOf_radicalPrimPart_le none none
        (challengeRetainingRootFirst retainedTailTestEquation)).trans_eq hrootDegree)
      (Nat.zero_le _)
  have hpositive := radicalPrimPart_eq_one_of_degreeOf_eq_zero none
    (challengeRetainingRootFirst retainedTailTestEquation) hpositiveDegree
  simpa [positiveCurveEquation, fromFlattenedRootFirst] using
    congrArg fromFlattenedRootFirst hpositive

/-- A concrete first-order equation is routed to its singular tail after specialization. -/
example :
    differentialSpecialization
      (challengeSpecialization (singularCurveEquation retainedTailTestEquation) 0) 0 = 0 := by
  apply singularCurveEquation_routes_nonregular retainedTailTestEquation
    (MvPolynomial.X_ne_zero _) 0 0
  · simp [retainedTailTestEquation, challengeSpecialization,
      differentialSpecialization, differentialSpecializationHom]
  · left
    rw [retainedTailTest_positiveEquation]
    simp [challengeSpecialization, differentialSpecialization, differentialSpecializationHom]

/-- The retained singular polynomial satisfies its `Y₀` degree bound on a concrete equation. -/
example :
    (singularCurveEquation retainedTailTestEquation).degreeOf (some 0) ≤
      ordinaryDegreeEnvelope 1 1 := by
  apply singularCurveEquation_degree_le retainedTailTestEquation
  · change weightedTotalDegree jetDegreeWeight
      (MvPolynomial.monomial (Finsupp.single (some (0 : Fin 2)) 1) (1 : ℚ[X])) ≤ 1
    rw [weightedTotalDegree_monomial _ _ _ (by norm_num)]
    simp [Finsupp.weight_single, jetDegreeWeight]
  · change degreeOf (some (1 : Fin 2))
      (MvPolynomial.X (some (0 : Fin 2)) : DifferentialPolynomial ℚ[X] 1) ≤ 1
    rw [degreeOf_X_of_ne (by decide)]
    norm_num
  · norm_num

/-- The challenge-degree envelope applies to a concrete retained singular equation. -/
example : CoeffNatDegreeLE (singularCurveEquation retainedTailTestEquation) 0 := by
  apply singularCurveEquation_coeffNatDegreeLE (H := 0) (M := 1)
  · change CoeffNatDegreeLE
      (MvPolynomial.X (some (0 : Fin 2)) : DifferentialPolynomial ℚ[X] 1) 0
    exact coeffNatDegreeLE_X _
  · norm_num
  · change degreeOf (some (1 : Fin 2))
      (MvPolynomial.X (some (0 : Fin 2)) : DifferentialPolynomial ℚ[X] 1) ≤ 1
    rw [degreeOf_X_of_ne (by decide)]
    norm_num

/-- A concrete retained singular equation is nonzero in characteristic zero. -/
example : singularCurveEquation retainedTailTestEquation ≠ 0 := by
  apply singularCurveEquation_ne_zero (M := 1)
  · change degreeOf (some (1 : Fin 2))
      (MvPolynomial.X (some (0 : Fin 2)) : DifferentialPolynomial ℚ[X] 1) ≤ 1
    rw [degreeOf_X_of_ne (by decide)]
    norm_num
  · exact Or.inl (ringChar.eq_zero : ringChar ℚ = 0)

namespace ReedSolomon.FirstOrder.Squarefree

open Polynomial ReedSolomon.HiddenDerivative

private noncomputable abbrev exampleRho : ℝ := 2 / 49
private noncomputable abbrev exampleEta : ℝ := 1 / 100
private noncomputable abbrev exampleAgreement := firstOrderRateThreshold exampleRho + exampleEta
private noncomputable abbrev exampleJet := automaticJetDegree exampleRho exampleAgreement
private noncomputable abbrev exampleCap := automaticDerivativeCap exampleRho exampleAgreement

example : (firstOrderCurveFiberStageOne 2 exampleJet exampleCap (regularTaylorExponent 1) : ℝ) *
    agreementIncidenceRatio 100 1 20 + ordinaryDegreeEnvelope exampleJet exampleCap ≤
    automaticSquarefreeListBoundConstant exampleRho * 100 / exampleEta ^ 2 := by
  have ht : firstOrderRateThreshold exampleRho = 79 / 455 := by
    unfold firstOrderRateThreshold exampleRho
    rw [show (2 / 49 : ℝ) * (5 - 2 / 49) * (2 - 2 / 49) = (216 / 343 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs]
    norm_num
  have hc : (2 : ℝ) < (⌈4 / ((1081506391 : ℝ) / 42598400000)⌉₊ : ℝ) := by
    exact_mod_cast Nat.lt_ceil.mpr (by norm_num)
  apply automaticSquarefreeListExpression_le (rho := exampleRho) (eta := exampleEta)
  all_goals norm_num [ht,
    automaticDerivativeCap, automaticDerivativeCapRaw, automaticMultiplicity, automaticSurplus,
    automaticDerivativeRatio, automaticAgreement, automaticGapBracket, firstOrderCleanExpression,
    firstOrderRateBeta]
  · constructor
    · nlinarith [hc]
    · norm_num [automaticJetDegree, automaticMultiplicity, automaticSurplus,
        automaticDerivativeRatio, automaticAgreement, automaticGapBracket,
        firstOrderCleanExpression, firstOrderRateBeta, ht]
end ReedSolomon.FirstOrder.Squarefree

example :
    (factorwiseSolutions.card : ℝ) ≤
      (firstOrderCurveFiberStageOne 2 1 1 (regularTaylorExponent 1) : ℝ) *
          ((2 - 1 : ℕ) : ℝ) / (2 - 1 : ℕ) + ordinaryDegreeEnvelope 1 1 := by
  exact finite_squarefree_agreement_solutions_card_le
    factorwiseDomain factorwiseReceived factorwiseEquation (MvPolynomial.X_ne_zero _)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      change weightedTotalDegree jetDegreeWeight
        (MvPolynomial.monomial (Finsupp.single (some (0 : Fin 2)) 1) (1 : ℚ)) ≤ 1
      rw [weightedTotalDegree_monomial _ _ _ (by norm_num)]
      simp [Finsupp.weight_single, jetDegreeWeight])
    (by
      change degreeOf (some (1 : Fin 2))
        (MvPolynomial.X (some (0 : Fin 2)) : DifferentialPolynomial ℚ 1) ≤ 1
      rw [degreeOf_X_of_ne (by decide)]
      norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) factorwiseSolutions
    factorwise_solutions_are_roots (by
      intro P hP
      simp only [factorwiseSolutions, Finset.mem_singleton] at hP
      subst P
      constructor
      · exact WithBot.bot_lt_coe 2
      · norm_num [factorwiseReceived, factorwiseDomain])

example :
    (factorwiseSolutions.card : ℝ) ≤
      (firstOrderCurveFiberStageOne 2 1 1 (regularTaylorExponent 1) : ℝ) *
          ((2 - 1 : ℕ) : ℝ) / (2 - 1 : ℕ) + ordinaryDegreeEnvelope 1 1 := by
  exact finite_factorwise_agreement_solutions_card_le
    factorwiseDomain factorwiseReceived factorwiseEquation (MvPolynomial.X_ne_zero _)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      change weightedTotalDegree jetDegreeWeight
        (MvPolynomial.monomial (Finsupp.single (some (0 : Fin 2)) 1) (1 : ℚ)) ≤ 1
      rw [weightedTotalDegree_monomial _ _ _ (by norm_num)]
      simp [Finsupp.weight_single, jetDegreeWeight])
    (by
      change degreeOf (some (1 : Fin 2))
        (MvPolynomial.X (some (0 : Fin 2)) : DifferentialPolynomial ℚ 1) ≤ 1
      rw [degreeOf_X_of_ne (by decide)]
      norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) factorwiseTail factorwiseSolutions
    factorwise_solutions_are_roots (by
      intro P hP
      simp only [factorwiseSolutions, Finset.mem_singleton] at hP
      subst P
      constructor
      · exact WithBot.bot_lt_coe 2
      · norm_num [factorwiseReceived, factorwiseDomain])

private def certificateValues : Fin 2 → Fin 2 → ℚ := fun _ _ ↦ 0

private theorem certificateHeightSurplus :
    firstOrderCurveShiftedRowSlotBound 1 2 1 1 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 1 1 1 1 1 := by
  norm_num [firstOrderCurveShiftedRowSlotBound, firstOrderGradedRankBound,
    firstOrderGradedSourceCount, firstOrderCurveShiftedHeightSlotCount, Finset.sum_range_succ]

/-- The zero line over two points has a finite first-order curve certificate at recovery
degree `1`. -/
private noncomputable def certificateCurve :
    FirstOrderCurveCertificate (F := ℚ) 1 2 1 1 1 2 1 factorwiseDomain
      (fun i ↦ ReedSolomon.powerBatchedCoordinate (fun t ↦ certificateValues t i))
      (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1)) :=
  Classical.choice <| exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1) (k := 2) (h := 1) (n := 2)
    1 (by norm_num) (by norm_num) (by norm_num) factorwiseDomain _
    (by intro i; norm_num [ReedSolomon.powerBatchedCoordinate, certificateValues])
    certificateHeightSurplus

/-- A finite certificate gives a base-field challenge at which the zero polynomial has exact
power agreement with the zero line. -/
example : ∃ z : ℚ, ReedSolomon.HasExactPowerAgreement factorwiseDomain certificateValues
    (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, -, hgood⟩ :=
    exists_baseExceptional_retainedSquarefreeCurveAgreement_of_certificate
      (E := AlgebraicClosure ℚ) (L := 2) factorwiseDomain certificateValues
      (algebraMap ℚ (AlgebraicClosure ℚ)) _ certificateCurve
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨z, hgood z hz 0 (WithBot.bot_lt_coe 2) (by
    norm_num [ReedSolomon.polynomialAgreementSet, ReedSolomon.powerBatchedWord,
      certificateValues])⟩

/-- On a line of length `4` with agreement `3` and recovery degree `1`, the retained charge at
the balanced split is at most the closed line envelope. -/
example :
    retainedSquarefreeCurveAgreementCharge (agreementIncidenceRatio 4 1 3) 4 1 1
        (balancedSplit 1 3) 3 1 1 0 ≤
      retainedSquarefreeLineAgreementEnvelope (agreementIncidenceRatio 4 1 3) 4 1 1 1 0 :=
  retainedSquarefreeCurveAgreementCharge_balancedSplit_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A symbolic line certificate gives a base-field challenge at which the zero polynomial has an
exact correlated pair with the zero line. -/
example : ∃ z : ℚ, ReedSolomon.HasExactCorrelatedPair factorwiseDomain (fun _ ↦ 0) (fun _ ↦ 0)
    (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨cert⟩ := certificateWithPositiveDerivativeCap
  obtain ⟨exceptional, -, hgood⟩ :=
    exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate
      (E := AlgebraicClosure ℚ) factorwiseDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (algebraMap ℚ (AlgebraicClosure ℚ)) _ cert
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨z, hgood z hz 0 (WithBot.bot_lt_coe 2) (by
    norm_num [ReedSolomon.polynomialAgreementSet])⟩

/-- The sharp optimized certificate bound gives a base-field challenge at which the zero
polynomial has exact power agreement with the zero line. -/
example : ∃ z : ℚ, ReedSolomon.HasExactPowerAgreement factorwiseDomain certificateValues
    (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, -, hgood⟩ :=
    exists_baseExceptional_retainedSquarefreeCurveAgreement_sharpOptimized_of_certificate
      (E := AlgebraicClosure ℚ) (L := 2) factorwiseDomain certificateValues
      (algebraMap ℚ (AlgebraicClosure ℚ)) _ certificateCurve
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  exact ⟨z, hgood z hz 0 (WithBot.bot_lt_coe 2) (by
    norm_num [ReedSolomon.polynomialAgreementSet, ReedSolomon.powerBatchedWord,
      certificateValues])⟩
