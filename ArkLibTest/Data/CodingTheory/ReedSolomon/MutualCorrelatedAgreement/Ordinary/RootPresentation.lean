/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.RootPresentation
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Acceptance tests for ordinary root presentations

The tests compute root degrees and evaluations for a concrete equation, verify the coefficient
height bound, and specialize the exceptional-set theorem to the equation `Y₀ = 0`, where the
resultant has degree zero and the exceptional set is empty. The zero equation shows why a
nonzero premise is needed for the presentation's nonvanishing theorem.
-/

open Polynomial PolynomialDifferential MvPolynomial

namespace ReedSolomon.RootPresentationTest

private noncomputable def rootVariable {F : Type*} [Field F] :
    DifferentialPolynomial F[X] 0 :=
  MvPolynomial.X (some 0)

/-- A second-degree root monomial has the expected root degree after reordering. -/
example {F : Type*} [Field F] :
  (ordinaryRootPresentation
      (MvPolynomial.X (some 0) ^ 2 : DifferentialPolynomial F[X] 0)).natDegree = 2 := by
  rw [natDegree_ordinaryRootPresentation]
  simp

/-- The derivative variable becomes the outer root variable. -/
example {F : Type*} [Field F] :
    ordinaryRootPresentation
      (MvPolynomial.X (some (0 : Fin 1)) : DifferentialPolynomial F[X] 0) = Polynomial.X := by
  simpa [MvPolynomial.monomial_eq] using (ordinaryRootPresentation_monomial
    (m := Finsupp.single (some (0 : Fin 1)) 1) (1 : F[X]))

/-- Evaluating the presentation of `Y₀` at a polynomial gives that polynomial. -/
example {F : Type*} [Field F] (w : F) (P : F[X]) :
    ((ordinaryRootPresentation (rootVariable (F := F))).map
      (Polynomial.evalRingHom (Polynomial.C w))).eval P
      = P := by
  rw [eval_ordinaryRootPresentation]
  simp [rootVariable, challengeSpecialization]

/-- The coefficient-height bound applies to a challenge coefficient of degree one. -/
example {F : Type*} [Field F] :
    Polynomial.Bivariate.degreeX
      (ordinaryRootPresentation
        (MvPolynomial.C (Polynomial.X + 1) * MvPolynomial.X (some 0) :
          DifferentialPolynomial F[X] 0))
      ≤ 1 := by
  apply degreeX_ordinaryRootPresentation_le
  have hC : MvPolynomial.CoeffNatDegreeLE
      (MvPolynomial.C (Polynomial.X + 1) : DifferentialPolynomial F[X] 0) 1 := by
    apply MvPolynomial.coeffNatDegreeLE_C
    simp
  have hY : MvPolynomial.CoeffNatDegreeLE
      (MvPolynomial.X (some 0) : DifferentialPolynomial F[X] 0) 0 :=
    MvPolynomial.coeffNatDegreeLE_X _
  have hmul := MvPolynomial.CoeffNatDegreeLE.mul hC hY
  exact hmul

/-- The original derivative-first resultant follows from the padded resultant theorem. -/
example {F : Type*} [Field F] {Q : DifferentialPolynomial F[X] 0}
    (hQ : Irreducible Q) (_hpos : 0 < Q.degreeOf (some 0))
    (hder : MvPolynomial.pderiv (some 0) Q ≠ 0) :
    Polynomial.resultant (ordinaryRootPresentation Q).derivative
      (ordinaryRootPresentation Q) (Q.degreeOf (some 0) - 1) (Q.degreeOf (some 0)) ≠ 0 := by
  rw [Polynomial.resultant_comm_sub_one]
  exact resultant_derivative_ordinaryRootPresentation_ne_zero hQ hder

/-- `Y₀` is irreducible, has nonzero derivative, and has no exceptional challenges. -/
example {F : Type*} [Field F] :
    ∀ w : F, ∀ P : F[X],
      differentialSpecialization
        (challengeSpecialization (rootVariable (F := F)) w) P = 0 →
      differentialSpecialization
        (separant (challengeSpecialization (rootVariable (F := F)) w) (Fin.last 0)) P ≠ 0 := by
  have hirr : Irreducible (rootVariable (F := F)) := by
    apply MvPolynomial.irreducible_of_totalDegree_eq_one
    · simp [rootVariable]
    · intro c hc
      apply isUnit_of_dvd_one
      have h := hc (Finsupp.single (some (0 : Fin 1)) 1)
      simpa [rootVariable] using h
  have hpos : 0 < (rootVariable (F := F)).degreeOf (some 0) := by
    simp [rootVariable, MvPolynomial.degreeOf_X_self]
  have hder : MvPolynomial.pderiv (some 0) (rootVariable (F := F)) ≠ 0 := by
    simp [rootVariable]
  have hheight : MvPolynomial.CoeffNatDegreeLE (rootVariable (F := F)) 0 := by
    simpa [rootVariable] using MvPolynomial.coeffNatDegreeLE_X (some 0)
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_ordinary_separant hirr hpos hder hheight
  have hcard0 : exceptional.card = 0 := by
    simpa [rootVariable] using hcard
  have hexceptional : exceptional = ∅ := Finset.card_eq_zero.mp hcard0
  subst exceptional
  intro w P hroot
  exact hgood w (by simp) P hroot

/-- The zero equation has zero presentation, so the nonzero premise cannot be omitted. -/
example {F : Type*} [Field F] :
    ordinaryRootPresentation (0 : DifferentialPolynomial F[X] 0) = 0 := by
  simp [ordinaryRootPresentation]

end ReedSolomon.RootPresentationTest
