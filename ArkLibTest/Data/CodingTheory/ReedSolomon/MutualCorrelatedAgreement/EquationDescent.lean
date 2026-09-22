/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import Mathlib.FieldTheory.Finite.Extension

open Polynomial PolynomialDifferential ReedSolomon

private def pointDomain : Fin 1 ↪ ZMod 3 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private theorem zeroCandidate_has_exact_pair (z : ZMod 3) (P : (ZMod 3)[X])
    (hdegree : P.degree < 0) :
    HasExactCorrelatedPair pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (RingHom.id (ZMod 3)) 0 z P := by
  by_cases hP : P = 0
  · subst P
    refine ⟨(0, 0), by simp, by simp, ?_, ?_⟩
    · simp [correlatedPairSpecialization]
    · ext i
      simp [polynomialAgreementSet, commonPolynomialAgreementSet]
  · exfalso
    have hdegree' := Polynomial.degree_eq_natDegree hP
    rw [hdegree'] at hdegree
    exact (by simp : ¬ (P.natDegree : WithBot ℕ) < 0) hdegree

/-- The equation-restricted descent theorem specializes to the zero equation and a one-point
domain, with no exceptional challenges. -/
example :
    ∃ baseExceptional : Finset (ZMod 3), baseExceptional.card ≤ 0 ∧
      ∀ z ∉ baseExceptional, ∀ P : (ZMod 3)[X], P.degree < 0 →
        1 ≤ (polynomialAgreementSet pointDomain (fun _ ↦ 0) P).card →
        differentialSpecialization (challengeSpecialization
          (0 : DifferentialPolynomial (ZMod 3)[X] 0) z) P = 0 →
        HasExactCorrelatedPair pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
          (RingHom.id (ZMod 3)) 0 z P := by
  refine exists_exceptional_equation_correlatedAgreement_descend
    (domain := pointDomain) (f := fun _ ↦ 0) (g := fun _ ↦ 0)
    (ι := RingHom.id (ZMod 3)) (Q := 0) (k := 0) (A := 1) (exceptional := ∅) ?_
  intro z _ P hdegree _ _
  exact zeroCandidate_has_exact_pair z P hdegree
