/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.Algebra.Field.ZMod

/-! Padded resultants over a ring with zero divisors, and the middle-axis derivative bound. -/

open Polynomial

-- Unequal budgets expose accidental reversal of the Sylvester column counts:
-- Res_Y(Y - X^5, Y^3) = X^15, saturating 3 * 5 + 1 * 0.
example :
    (resultant (X - C ((X : Polynomial ℤ) ^ 5)) (X ^ 3) 1 3).natDegree = 15 := by
  rw [resultant_X_sub_C_left _ _ _ (by simp)]
  simp [← pow_mul]

-- The determinant bound needs only a commutative ring, even for arbitrary padded dimensions.
example (P Q : Polynomial (Polynomial (ZMod 4))) (m n A B : ℕ)
    (hP : ∀ j, (P.coeff j).natDegree ≤ A) (hQ : ∀ j, (Q.coeff j).natDegree ≤ B) :
    (resultant P Q m n).natDegree ≤ n * A + m * B :=
  natDegree_resultant_le_of_coeff_natDegree_le P Q m n A B hP hQ

-- With base ring F₂[Z], the resultant lies in F₂[Z][X] and the bound measures its X-degree.
example (P : Polynomial (Polynomial (Polynomial (ZMod 2)))) :
    (resultant P P.derivative).natDegree ≤ (2 * P.natDegree - 1) * Bivariate.degreeX P :=
  natDegree_resultant_derivative_le P

-- Natural subtraction also covers the zero-degree boundary without a spurious positive budget.
example (a : Polynomial (ZMod 2)) :
    (resultant (C a) (C a).derivative).natDegree ≤ 0 := by
  simp

-- Padded derivative resultants retain the same budget when characteristic forces a degree drop.
example (P : Polynomial (Polynomial (ZMod 3))) :
    (resultant P P.derivative P.natDegree (P.natDegree - 1)).natDegree ≤
      (2 * P.natDegree - 1) * Bivariate.degreeX P :=
  natDegree_resultant_derivative_padded_le P
