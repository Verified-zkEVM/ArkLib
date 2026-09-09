/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Numerator
import Mathlib.Algebra.Field.ZMod
/-!
# Canaries for the rational Taylor parametrization

These examples exercise a regular positive instance and show independently that the
binomial-pivot and separant hypotheses cannot be removed from the semantic theorem.
-/

namespace ReedSolomon.HiddenDerivative.RationalTaylorCanary

open PolynomialDifferential

noncomputable section

open Polynomial

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def forcedEquation : DifferentialPolynomial (ZMod 5) 1 :=
  MvPolynomial.X (some (Fin.last 1)) - MvPolynomial.X none

private def forcedSolution : (ZMod 5)[X] := C 3 * Polynomial.X ^ 2

private theorem forcedSolution_solution :
    differentialSpecialization forcedEquation forcedSolution = 0 := by
  have hcoefficient : (3 : ZMod 5) * (1 + 1) = 1 := by decide
  have hpolynomial : (C (3 : ZMod 5) : (ZMod 5)[X]) * (1 + 1) = 1 := by
    simpa only [map_mul, map_add, map_one] using congrArg C hcoefficient
  have htarget :
      (C (3 : ZMod 5) : (ZMod 5)[X]) * ((1 + 1) * Polynomial.X) -
          Polynomial.X = 0 := by
    calc
      (C (3 : ZMod 5) : (ZMod 5)[X]) * ((1 + 1) * Polynomial.X) -
          Polynomial.X =
          ((C (3 : ZMod 5) : (ZMod 5)[X]) * (1 + 1) - 1) * Polynomial.X := by ring
      _ = 0 := by rw [hpolynomial]; simp
  simpa [forcedEquation, forcedSolution, differentialSpecialization] using htarget

private theorem forcedSolution_separant :
    jetEvaluation (separant forcedEquation (Fin.last 1)) 0
      (polynomialJet (d := 1) 0 forcedSolution) ≠ 0 := by
  simp [forcedEquation, separant, jetEvaluation]

/-- The rational parametrization recovers the forced quadratic coefficient. -/
example :
    rationalTaylorCoefficient 0 forcedEquation
        (polynomialJet (d := 1) 0 forcedSolution) 2 =
      (Polynomial.taylor 0 forcedSolution).coeff 2 := by
  apply rationalTaylorCoefficient_eq_solution 0 forcedEquation forcedSolution
    forcedSolution_solution forcedSolution_separant 2
  intro i hi hil
  have : i = 2 := by omega
  subst i
  decide

private def characteristicBoundaryEquation : DifferentialPolynomial (ZMod 5) 1 :=
  MvPolynomial.X (some (Fin.last 1))

/-- At the characteristic boundary the pivot vanishes and two regular solutions with the same
initial jet have different fifth Taylor coefficients. -/
example :
    differentialSpecialization characteristicBoundaryEquation
        (0 : (ZMod 5)[X]) = 0 ∧
      differentialSpecialization characteristicBoundaryEquation
        (Polynomial.X ^ 5 : (ZMod 5)[X]) = 0 ∧
      polynomialJet (d := 1) 0 (0 : (ZMod 5)[X]) =
        polynomialJet (d := 1) 0 (Polynomial.X ^ 5 : (ZMod 5)[X]) ∧
      jetEvaluation (separant characteristicBoundaryEquation (Fin.last 1)) 0
        (polynomialJet (d := 1) 0 (0 : (ZMod 5)[X])) ≠ 0 ∧
      (Nat.choose 5 1 : ZMod 5) = 0 ∧
      (Polynomial.taylor 0 (0 : (ZMod 5)[X])).coeff 5 ≠
        (Polynomial.taylor 0 (Polynomial.X ^ 5 : (ZMod 5)[X])).coeff 5 := by
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
  constructor
  · simp [characteristicBoundaryEquation, separant, jetEvaluation]
  constructor
  · decide
  · simp

private def singularEquation : DifferentialPolynomial ℚ 1 :=
  MvPolynomial.X (some (Fin.last 1)) ^ 2 - MvPolynomial.X (some 0)

private def singularSolution : ℚ[X] := C (1 / 4) * Polynomial.X ^ 2

private theorem singularSolution_solution :
    differentialSpecialization singularEquation singularSolution = 0 := by
  have hd : Polynomial.hasseDeriv 1 singularSolution = C (1 / 2) * Polynomial.X := by
    rw [Polynomial.hasseDeriv_one', singularSolution, Polynomial.derivative_mul,
      Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_X_pow, pow_one,
      ← mul_assoc, ← Polynomial.C_mul]
    norm_num
  simp only [singularEquation, differentialSpecialization, map_sub, map_pow,
    MvPolynomial.eval₂Hom_X', Fin.val_last]
  rw [hd]
  change (C (1 / 2) * Polynomial.X) ^ 2 -
    Polynomial.hasseDeriv 0 singularSolution = 0
  rw [Polynomial.hasseDeriv_zero', singularSolution]
  have hs : (1 / 2 : ℚ) ^ 2 = 1 / 4 := by norm_num
  have hc := congrArg (Polynomial.C : ℚ →+* ℚ[X]) hs
  simp only [map_pow] at hc
  rw [mul_pow, hc, sub_self]

/-- In characteristic zero, a zero separant likewise permits two solutions with one initial jet
and different next coefficients, even though the binomial pivot is nonzero. -/
example :
    differentialSpecialization singularEquation (0 : ℚ[X]) = 0 ∧
      differentialSpecialization singularEquation singularSolution = 0 ∧
      polynomialJet (d := 1) 0 (0 : ℚ[X]) =
        polynomialJet (d := 1) 0 singularSolution ∧
      jetEvaluation (separant singularEquation (Fin.last 1)) 0
        (polynomialJet (d := 1) 0 singularSolution) = 0 ∧
      (Nat.choose 2 1 : ℚ) ≠ 0 ∧
      (Polynomial.taylor 0 (0 : ℚ[X])).coeff 2 ≠
        (Polynomial.taylor 0 singularSolution).coeff 2 := by
  constructor
  · simp [singularEquation, differentialSpecialization]
  constructor
  · exact singularSolution_solution
  constructor
  · funext i
    fin_cases i <;> simp [polynomialJet, hasseJet_apply, singularSolution]
  constructor
  · simp [singularEquation, separant, jetEvaluation, polynomialJet, hasseJet_apply,
      singularSolution]
  constructor
  · norm_num
  · norm_num [singularSolution]

end

end ReedSolomon.HiddenDerivative.RationalTaylorCanary
