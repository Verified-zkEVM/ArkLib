/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
import Mathlib.FieldTheory.Finite.Extension

/-!
# Equation-restricted agreement descent acceptance tests

Concrete examples check descent of a satisfiable differential equation with a positive degree
bound, and verify its mapped root and nonempty agreement set over a proper field extension.
-/

open Polynomial PolynomialDifferential ReedSolomon

noncomputable section

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
local instance : DecidableEq E₄ := Classical.decEq _

private def pointDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private def agreementEquation : DifferentialPolynomial (ZMod 2)[X] 0 :=
  MvPolynomial.X (some 0) - MvPolynomial.C (Polynomial.X)

private theorem constant_has_exact_pair (ι : ZMod 2 →+* E₄) (z : E₄)
    (P : E₄[X])
    (hroot : differentialSpecialization
      (challengeSpecialization
        (MvPolynomial.map (Polynomial.mapRingHom ι) agreementEquation) z) P = 0) :
    HasExactCorrelatedPair pointDomain (fun _ ↦ 0) (fun _ ↦ 1) ι 2 z P := by
  have hpoly : P - C z = 0 := by
    simpa [agreementEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom] using hroot
  have hP : P = C z := sub_eq_zero.mp hpoly
  subst P
  refine ⟨(0, 1), ?_, by norm_num, ?_, ?_⟩
  · simpa using (show (⊥ : WithBot ℕ) < (2 : WithBot ℕ) by decide)
  · simp [correlatedPairSpecialization]
  · ext i
    simp [polynomialAgreementSet, commonPolynomialAgreementSet, pointDomain]

/-- The equation `P = z` has an exact correlated-pair explanation over the degree-two extension;
the strict degree bound is positive and the one-point agreement set is nonempty. -/
example :
    ∃ baseExceptional : Finset (ZMod 2), baseExceptional.card ≤ 0 ∧
      ∀ z ∉ baseExceptional, ∀ P : (ZMod 2)[X], P.degree < 2 →
        1 ≤ (polynomialAgreementSet pointDomain (fun _ ↦ 0 + z * 1) P).card →
        differentialSpecialization (challengeSpecialization agreementEquation z) P = 0 →
        HasExactCorrelatedPair pointDomain (fun _ ↦ 0) (fun _ ↦ 1)
          (RingHom.id (ZMod 2)) 2 z P := by
  refine exists_exceptional_equation_correlatedAgreement_descend
    (domain := pointDomain) (f := fun _ ↦ 0) (g := fun _ ↦ 1)
    (ι := algebraMap (ZMod 2) E₄) (Q := agreementEquation) (k := 2) (A := 1)
    (exceptional := ∅) ?_
  intro z _ P _ _ hroot
  exact constant_has_exact_pair (algebraMap (ZMod 2) E₄) z P hroot

/-- At challenge `1`, the mapped equation has the constant root `1`, which agrees at the
evaluation point of the one-point domain. -/
example :
    differentialSpecialization
        (challengeSpecialization
          (MvPolynomial.map
            (Polynomial.mapRingHom (algebraMap (ZMod 2) E₄)) agreementEquation)
          (algebraMap (ZMod 2) E₄ 1))
        (C (algebraMap (ZMod 2) E₄ 1)) = 0 ∧
      (polynomialAgreementSet
        (pointDomain.trans
          ⟨algebraMap (ZMod 2) E₄, (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ 1) (C (algebraMap (ZMod 2) E₄ 1))).card = 1 := by
  constructor
  · simp [agreementEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom]
  · simp [polynomialAgreementSet, pointDomain]
