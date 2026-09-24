/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.RationalTaylorDerivativeDegree

/-!
# Acceptance tests for rational Taylor derivative-degree bounds

For the first-order equation `Y₁ + X Y₀`, these examples check the separant, the rational
numerator at index `2`, and its padding to a sufficient common denominator exponent.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- The first-order equation `Y₁ + X Y₀` over `ℚ[X]`. -/
private abbrev linearEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  X (some 1) + C Polynomial.X * X (some 0)

/-- The equation has degree at most one in its derivative variable `Y₁`. -/
private theorem linearEquation_derivativeDegree :
    linearEquation.degreeOf (some 1) ≤ 1 := by
  apply (degreeOf_add_le _ _ _).trans
  apply max_le
  · simp
  · exact (degreeOf_mul_le _ _ _).trans (by simp [degreeOf_X])

/-- The separant bound for `Y₁ + X Y₀` at center `0`. -/
example :
    (initialJetSeparant (Polynomial.C (0 : ℚ)) linearEquation).degreeOf 1 ≤
      linearEquation.degreeOf (some 1) - 1 := by
  exact degreeOf_initialJetSeparant_le _ _

/-- The rational numerator at index `2` has derivative-variable degree at most `2`. -/
example :
    (rationalTaylorNumeratorOver ℚ (Polynomial.C (0 : ℚ)) linearEquation 2).degreeOf 1 ≤
      2 := by
  have h := degreeOf_rationalTaylorNumeratorOver_firstOrder
    (Polynomial.C (0 : ℚ)) linearEquation 1 (by decide) linearEquation_derivativeDegree 2
  simpa using h

/-- At the sufficient exponent `3`, the common numerator at index `2` has degree at most `2`. -/
example :
    (commonTaylorNumeratorOver ℚ (Polynomial.C (0 : ℚ)) linearEquation 3 2).degreeOf 1 ≤
      2 := by
  have h := degreeOf_commonTaylorNumeratorOver_firstOrder
    (Polynomial.C (0 : ℚ)) linearEquation 1 3 3 (by intro l; omega) (by decide)
    linearEquation_derivativeDegree 2
  simpa using h

end

end PolynomialDifferential
