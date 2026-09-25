/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Factorwise
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.TailBound
import Mathlib.Tactic.NormNum

/-!
# Factorwise agreement acceptance tests

Concrete rational examples check the actual-degree and capped factorwise agreement list bounds.
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
