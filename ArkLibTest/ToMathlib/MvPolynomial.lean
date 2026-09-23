/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for multivariate polynomial evaluation

The evaluation bridges are computed on polynomials that depend on both the distinguished
polynomial variable and a remaining multivariate variable, with distinct values assigned to them.
-/

open MvPolynomial Polynomial

namespace MvPolynomialEvaluationTest

noncomputable section

private def point : Option Unit → ℚ
  | none => 2
  | some () => 3

/-- A flattened polynomial depending on both evaluation coordinates. -/
private abbrev flattened : MvPolynomial (Option Unit) ℚ :=
  X none ^ 2 * X (some ()) + X none + X (some ())

/-- A polynomial-coefficient polynomial depending on both evaluation coordinates. -/
private abbrev polynomialCoefficients : MvPolynomial Unit (Polynomial ℚ) :=
  MvPolynomial.C ((Polynomial.X : ℚ[X]) ^ 2 + 1) * MvPolynomial.X () +
    MvPolynomial.C ((Polynomial.X : ℚ[X]) + 2)

/-- Evaluation after flattening computes the same value as direct evaluation. -/
example :
    aeval (fun j : Unit ↦ point (some j))
        (map (Polynomial.aeval (point none)).toRingHom
          (optionEquivRight ℚ Unit flattened)) = 17 ∧
      aeval point flattened = 17 := by
  constructor
  · rw [aeval_map_optionEquivRight]
    norm_num [point, flattened]
  · norm_num [point, flattened]

/-- Evaluation after unflattening computes the same value as successive evaluation. -/
example :
    aeval point ((optionEquivRight ℚ Unit).symm polynomialCoefficients) = 19 ∧
      aeval (fun j : Unit ↦ point (some j))
        (map (Polynomial.aeval (point none)).toRingHom polynomialCoefficients) = 19 := by
  constructor
  · rw [aeval_optionEquivRight_symm]
    norm_num [point, polynomialCoefficients]
  · norm_num [point, polynomialCoefficients]

end

end MvPolynomialEvaluationTest
