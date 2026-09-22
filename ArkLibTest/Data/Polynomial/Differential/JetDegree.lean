/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.JetDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for finite-jet degree budgets

The examples cover a sharp specialization bound, the zero-weight boundary, and the distinction
between characteristic-free degree loss and characteristic-sensitive separant nonvanishing.
-/

namespace PolynomialDifferential

noncomputable section

open Polynomial

private def exactDegreeEquation : DifferentialPolynomial ℚ 1 :=
  MvPolynomial.X none ^ 2 * MvPolynomial.X (some (Fin.last 1)) ^ 3

private theorem hasseDeriv_one_X_five :
    hasseDeriv 1 (Polynomial.X ^ 5 : ℚ[X]) =
      Polynomial.C 5 * Polynomial.X ^ 4 := by
  rw [Polynomial.X_pow_eq_monomial, hasseDeriv_monomial]
  norm_num
  rw [← Polynomial.C_mul_X_pow_eq_monomial]

/-- The source monomial `X² Y₁³` attains its specialization weight
`2 + 3 * (5 - 1) = 14`. -/
example :
    (differentialSpecialization exactDegreeEquation (Polynomial.X ^ 5)).natDegree = 14 ∧
      (differentialSpecialization exactDegreeEquation (Polynomial.X ^ 5)).natDegree ≤
        differentialWeightedDegree 5 exactDegreeEquation := by
  constructor
  · have hspec :
        differentialSpecialization exactDegreeEquation (Polynomial.X ^ 5) =
          Polynomial.X ^ 2 * (Polynomial.C 5 * Polynomial.X ^ 4) ^ 3 := by
      rw [exactDegreeEquation, differentialSpecialization, map_mul, map_pow, map_pow]
      simp only [differentialSpecializationHom, MvPolynomial.aeval_X, Fin.last]
      rw [hasseDeriv_one_X_five]
    rw [hspec]
    rw [Polynomial.natDegree_mul (by simp) (by norm_num), Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, Polynomial.natDegree_mul (by norm_num) (by simp),
      Polynomial.natDegree_pow]
    norm_num
  · exact natDegree_differentialSpecialization_le exactDegreeEquation
      (Polynomial.X ^ 5) (by simp)

/-- At `D = d`, the top jet variable has weight zero and its powers still satisfy the
specialization bound. This does not assert that the corresponding bounded-support space is
finite-dimensional. -/
example (n : ℕ) :
    differentialWeight (d := 1) 1 (some (Fin.last 1)) = 0 ∧
      (differentialSpecialization
        (MvPolynomial.X (some (Fin.last 1)) ^ n : DifferentialPolynomial ℚ 1)
        Polynomial.X).natDegree ≤
          differentialWeightedDegree 1
            (MvPolynomial.X (some (Fin.last 1)) ^ n : DifferentialPolynomial ℚ 1) := by
  constructor
  · exact differentialWeight_top_eq_zero 1
  · exact natDegree_differentialSpecialization_le _ Polynomial.X (by simp)

/-- In characteristic two the separant of `Y₀²` vanishes, although the total-degree upper
bound remains valid. -/
example :
    separant
        (MvPolynomial.X (some 0) ^ 2 : DifferentialPolynomial (ZMod 2) 0) 0 = 0 ∧
      jetTotalDegree
          (separant
            (MvPolynomial.X (some 0) ^ 2 : DifferentialPolynomial (ZMod 2) 0) 0) ≤
        jetTotalDegree
            (MvPolynomial.X (some 0) ^ 2 : DifferentialPolynomial (ZMod 2) 0) - 1 := by
  constructor
  · rw [separant, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, mul_one]
    change MvPolynomial.C ((2 : ℕ) : ZMod 2) * MvPolynomial.X (some 0) ^ 1 = 0
    rw [ZMod.natCast_self, MvPolynomial.C_0, zero_mul]
  · exact separant_total_le _ _

/-- In characteristic zero, the corresponding ordinary separant is nonzero under the cast
hypothesis supplied by the generic partial-derivative API. -/
example :
    separant (MvPolynomial.X (some 0) ^ 2 : DifferentialPolynomial ℚ 0) 0 ≠ 0 := by
  change MvPolynomial.pderiv (some 0)
    (MvPolynomial.X (some 0) ^ 2 : DifferentialPolynomial ℚ 0) ≠ 0
  apply MvPolynomial.pderiv_ne_zero_of_natCast_ne_zero
  norm_num

/-- Total jet degree is exactly the exponent-level total used by interpolation support bounds. -/
example (u : JetVariable 2 →₀ ℕ) :
    totalJetDegree u = Finsupp.degree u.some :=
  totalJetDegree_eq_degree_some u

end

end PolynomialDifferential
