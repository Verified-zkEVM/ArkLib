/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.DegreeBounds.SpecializationDegree
/-!
# Canaries for differential-specialization degree

The main example attains the exact weighted bound: with ambient degree five, the monomial
`X² Y₁³` has weight `2 + 3(5-1) = 14`, and substituting `P = X⁵` produces a nonzero
degree-four first Hasse derivative and hence a polynomial of degree fourteen.
-/

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

noncomputable section

open Polynomial

private def exactDegreeEquation : DifferentialPolynomial ℚ 1 :=
  MvPolynomial.X none ^ 2 * MvPolynomial.X (some (Fin.last 1)) ^ 3

private theorem hasseDeriv_one_X_five :
    hasseDeriv 1 (X ^ 5 : ℚ[X]) = C 5 * X ^ 4 := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  norm_num
  rw [← C_mul_X_pow_eq_monomial]

/-- The exact specialization reaches degree fourteen, so the weighted estimate is tight. -/
example :
    (differentialSpecialization exactDegreeEquation (X ^ 5)).natDegree = 14 := by
  simp only [exactDegreeEquation, differentialSpecialization, map_mul, map_pow,
    MvPolynomial.eval₂Hom_X', Fin.last, hasseDeriv_one_X_five]
  rw [Polynomial.natDegree_mul (by simp) (by norm_num), Polynomial.natDegree_pow,
    Polynomial.natDegree_pow, Polynomial.natDegree_mul (by norm_num) (by simp),
    Polynomial.natDegree_pow]
  simp

/-- The generic theorem recovers the same sharp upper bound. -/
example :
    (differentialSpecialization exactDegreeEquation (X ^ 5)).natDegree ≤
      differentialWeightedDegree 5 exactDegreeEquation := by
  apply natDegree_differentialSpecialization_le
  simp

end

end ReedSolomon.HiddenDerivative
