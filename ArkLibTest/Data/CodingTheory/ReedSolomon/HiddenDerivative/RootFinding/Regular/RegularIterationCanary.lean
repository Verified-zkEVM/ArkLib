/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.Iteration
import Mathlib.Algebra.Field.ZMod
/-!
# Canaries for iterated regular-jet uniqueness

The positive example uses the equation `Y₁ - X = 0` over `ZMod 5`.  Its fixed zero initial jet
extends, among degree-at-most-four polynomials, only to `3X²`.  This exercises more than the
initial jet: the quadratic coefficient is forced by the differential equation.

The boundary example shows why the strict characteristic hypothesis is necessary.  For `Y₁ = 0`
in characteristic five, both `0` and `X⁵` are solutions with the same initial first jet, and the
zero jet is regular.  Thus uniqueness fails exactly when the allowed degree reaches the
characteristic.
-/

namespace ReedSolomon.HiddenDerivative

open Polynomial

open PolynomialDifferential

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def forcedQuadraticEquation : DifferentialPolynomial (ZMod 5) 1 :=
  MvPolynomial.X (some (Fin.last 1)) - MvPolynomial.X none

private def forcedQuadratic : (ZMod 5)[X] :=
  C 3 * X ^ 2

private theorem forcedQuadratic_solution :
    differentialSpecialization forcedQuadraticEquation forcedQuadratic = 0 := by
  have hcoefficient : (3 : ZMod 5) * (1 + 1) = 1 := by decide
  have hpolynomial : (C (3 : ZMod 5) : (ZMod 5)[X]) * (1 + 1) = 1 := by
    simpa only [map_mul, map_add, map_one] using congrArg C hcoefficient
  have htarget :
      (C (3 : ZMod 5) : (ZMod 5)[X]) * ((1 + 1) * X) - X = 0 := by
    calc
      (C (3 : ZMod 5) : (ZMod 5)[X]) * ((1 + 1) * X) - X =
        ((C (3 : ZMod 5) : (ZMod 5)[X]) * (1 + 1) - 1) * X := by ring
      _ = 0 := by rw [hpolynomial]; simp
  simpa [forcedQuadraticEquation, forcedQuadratic, differentialSpecialization] using htarget

private theorem forcedQuadratic_regular :
    IsRegularJet forcedQuadraticEquation (Fin.last 1) 0
      (polynomialJet (d := 1) 0 forcedQuadratic) := by
  simp [IsRegularJet, forcedQuadraticEquation, separant, jetEvaluation, polynomialJet,
    forcedQuadratic]

/-- A regular zero initial jet forces the nonzero quadratic coefficient `3`. -/
example (P : (ZMod 5)[X]) (hdegree : P.degree ≤ 4)
    (hsolution : differentialSpecialization forcedQuadraticEquation P = 0)
    (hjet : polynomialJet (d := 1) 0 P = polynomialJet (d := 1) 0 forcedQuadratic) :
    P = forcedQuadratic := by
  have hregular :
      IsRegularJet forcedQuadraticEquation (Fin.last 1) 0 (polynomialJet (d := 1) 0 P) := by
    rw [hjet]
    exact forcedQuadratic_regular
  apply eq_of_regular_solutions_of_degree_le_of_polynomialJet_eq
      forcedQuadraticEquation 0 P forcedQuadratic 4 hregular
  · exact hdegree
  · have hthree : (3 : ZMod 5) ≠ 0 := by decide
    norm_num [forcedQuadratic, hthree]
  · simp [ZMod.ringChar_zmod_n]
  · exact hsolution
  · exact forcedQuadratic_solution
  · exact hjet

private def characteristicBoundaryEquation : DifferentialPolynomial (ZMod 5) 1 :=
  MvPolynomial.X (some (Fin.last 1))

/-- At degree equal to the characteristic, a fixed regular initial jet can have two extensions. -/
example :
    IsRegularJet characteristicBoundaryEquation (Fin.last 1) 0
        (polynomialJet (d := 1) 0 (0 : (ZMod 5)[X])) ∧
      differentialSpecialization characteristicBoundaryEquation (0 : (ZMod 5)[X]) = 0 ∧
      differentialSpecialization characteristicBoundaryEquation (X ^ 5 : (ZMod 5)[X]) = 0 ∧
      polynomialJet (d := 1) 0 (0 : (ZMod 5)[X]) =
        polynomialJet (d := 1) 0 (X ^ 5 : (ZMod 5)[X]) ∧
      (0 : (ZMod 5)[X]) ≠ X ^ 5 := by
  constructor
  · simp [IsRegularJet, characteristicBoundaryEquation, separant, jetEvaluation,
      polynomialJet]
  constructor
  · simp [characteristicBoundaryEquation, differentialSpecialization]
  constructor
  · have hfive : (4 + 1 : ZMod 5) = 0 := by decide
    simp [characteristicBoundaryEquation, differentialSpecialization, hfive]
  constructor
  · funext i
    fin_cases i
    · simp [polynomialJet, hasseJet_apply]
    · have hfive : (4 + 1 : ZMod 5) = 0 := by decide
      simp [polynomialJet, hasseJet_apply, hfive]
  · intro h
    have hcoeff := congrArg (fun P : (ZMod 5)[X] ↦ P.coeff 5) h
    simp at hcoeff

end

end ReedSolomon.HiddenDerivative
