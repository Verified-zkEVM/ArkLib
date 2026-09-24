/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients

/-!
# Acceptance tests for multivariate polynomial degree bounds

These concrete examples check the separate-variable degree bounds for cleared substitution and
for moving polynomial coefficients into a distinguished variable.
-/

open MvPolynomial

/-- A one-variable monomial remains within the cleared-substitution degree budget. -/
example :
    (clearedSubstitution C (X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ)
      (fun _ : Fin 1 ↦ X (0 : Fin 1)) (fun _ : Fin 1 ↦ 1) 1
      (X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ)).degreeOf 0 ≤ 2 := by
  apply degreeOf_clearedSubstitution (R := ℚ) (i := (0 : Fin 1))
    (S := X 0) (N := fun _ : Fin 1 ↦ X 0) (d := fun _ : Fin 1 ↦ 1)
    (w := fun _ : Fin 1 ↦ 1) (H := 1) (b := 1) (v := 1)
  · simp
  · intro j
    simp
  · intro m hm
    have hm' : m = Finsupp.single (0 : Fin 1) 1 := by
      simpa only [support_X, Finset.mem_singleton] using hm
    rw [hm']
    simp [Finsupp.weight_single]
  · intro m hm
    have hm' : m = Finsupp.single (0 : Fin 1) 1 := by
      simpa only [support_X, Finset.mem_singleton] using hm
    rw [hm']
    simp [Finsupp.weight_single]

/-- The coefficient-polynomial variable does not contribute to the degree in `Y₁`. -/
example :
    degreeOf (some (1 : Fin 2)) ((optionEquivRight ℚ (Fin 2)).symm
      (X (0 : Fin 2) ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 2) (Polynomial ℚ))) ≤
      (X (0 : Fin 2) ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 2) (Polynomial ℚ)).degreeOf 1 := by
  exact degreeOf_optionEquivRight_symm_le _ _
