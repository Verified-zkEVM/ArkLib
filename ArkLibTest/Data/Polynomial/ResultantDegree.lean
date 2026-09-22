/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ResultantDegree
import ArkLib.Data.Polynomial.ResultantSpecialization
import Mathlib.Algebra.Field.ZMod

/-! Padded resultants over a ring with zero divisors, the middle-axis derivative bound, and the
total-degree (coefficient-triangle) bounds with their sharpness and degree-drop cases. -/

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

/-! ### Total-degree bounds -/

-- Res_Y(Y - X, Y^2 + X^3) = X^2 + X^3 has X-degree 3.
private theorem resultant_line_cubic :
    resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2 = (X : ℚ[X]) ^ 2 + X ^ 3 := by
  rw [resultant_X_sub_C_left _ _ _ (by compute_degree!)]
  simp

-- The weighted bound `n * dP + m * dQ - m * n = 2 * 1 + 1 * 3 - 2 = 3` is attained, while the
-- budget-only bound `natDegree_resultant_le_of_coeff_natDegree_le` gives `2 * 1 + 1 * 3 = 5`.
example :
    (resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2).natDegree = 3 ∧
      (resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2).natDegree ≤ 2 * 1 + 1 * 3 - 1 * 2 := by
  refine ⟨by rw [resultant_line_cubic]; compute_degree!, ?_⟩
  apply natDegree_resultant_le_of_coeff_add_le
  · intro i hi
    interval_cases i <;> simp only [coeff_sub, coeff_X, coeff_C] <;> simp
  · intro i hi
    interval_cases i <;> simp only [coeff_add, coeff_X_pow, coeff_C] <;> simp

-- The Bezout form gives `dP * dQ = 1 * 3` on the same pair.
example :
    (resultant (X - C (X : ℚ[X])) (X ^ 2 + C (X ^ 3)) 1 2).natDegree ≤ 1 * 3 := by
  apply natDegree_resultant_le_mul_of_coeff_add_le
  · intro i hi
    interval_cases i <;> simp only [coeff_sub, coeff_X, coeff_C] <;> simp
  · intro i hi
    interval_cases i <;> simp only [coeff_add, coeff_X_pow, coeff_C] <;> simp

-- Res_Y(Y^2 - X^2, 2Y) = -4X^2, computed in the source argument order and converted.
private theorem resultant_derivative_sq_sub_sq :
    resultant (X ^ 2 - C ((X : ℚ[X]) ^ 2)) (X ^ 2 - C ((X : ℚ[X]) ^ 2)).derivative 2 1 =
      -4 * X ^ 2 := by
  have hder : (X ^ 2 - C ((X : ℚ[X]) ^ 2)).derivative = C 2 * (X - C 0) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, C_0, sub_zero]
    simp
  rw [← resultant_comm_sub_one, hder, resultant_C_mul_left, show (2 : ℕ) - 1 = 1 from rfl,
    resultant_X_sub_C_left _ _ _ (by compute_degree!)]
  simp
  ring

-- The padded derivative bound `(2 * 2 - 1) * 2 - 2 ^ 2 = 2` is attained by `Y^2 - X^2`; the
-- `degreeX` bound `natDegree_resultant_derivative_padded_le` gives `3 * 2 = 6`.
example :
    (resultant (X ^ 2 - C ((X : ℚ[X]) ^ 2))
        (X ^ 2 - C ((X : ℚ[X]) ^ 2)).derivative 2 1).natDegree = 2 ∧
      (resultant (X ^ 2 - C ((X : ℚ[X]) ^ 2))
        (X ^ 2 - C ((X : ℚ[X]) ^ 2)).derivative 2 (2 - 1)).natDegree ≤
        (2 * 2 - 1) * 2 - 2 ^ 2 := by
  refine ⟨by rw [resultant_derivative_sq_sub_sq]; compute_degree!, ?_⟩
  apply natDegree_resultant_derivative_padded_le_of_coeff_add_le
  intro i hi
  interval_cases i <;> simp only [coeff_sub, coeff_X_pow, coeff_C] <;> simp

-- Declared degree above the actual degree, with the derivative degree dropping in
-- characteristic two: `Y^2 - t` declared at degree `3` with total-degree budget `3`.
example :
    (resultant (X ^ 2 - C (X : (ZMod 2)[X])) (X ^ 2 - C (X : (ZMod 2)[X])).derivative
        3 (3 - 1)).natDegree ≤ (2 * 3 - 1) * 3 - 3 ^ 2 := by
  apply natDegree_resultant_derivative_padded_le_of_coeff_add_le
  intro i hi
  interval_cases i <;> simp only [coeff_sub, coeff_X_pow, coeff_C] <;> simp

-- The source statement: `separableResultant A b = resultant A.derivative A (b - 1) b`, with
-- exact outer degree `b`, `0 < b`, and the coefficient triangle at every index. The exact
-- degree and `0 < b` are not used.
example (A : Polynomial (Polynomial (ZMod 4))) {b j : ℕ} (_hb : 0 < b)
    (_hdegree : A.natDegree = b) (hcoeff : ∀ i, i + (A.coeff i).natDegree ≤ j) :
    (resultant A.derivative A (b - 1) b).natDegree + b ^ 2 ≤ (2 * b - 1) * j ∧
      (resultant A.derivative A (b - 1) b).natDegree ≤ (2 * b - 1) * j - b ^ 2 := by
  rw [resultant_comm_sub_one]
  exact ⟨natDegree_resultant_derivative_padded_add_sq_le A b j fun i _ ↦ hcoeff i,
    natDegree_resultant_derivative_padded_le_of_coeff_add_le A b j fun i _ ↦ hcoeff i⟩

-- Boundary `b = 0`: the Sylvester matrix is empty, so the bound is `0` for every budget `j`.
example (A : Polynomial (Polynomial ℤ)) :
    (resultant A A.derivative 0 (0 - 1)).natDegree + 0 ^ 2 ≤
      (2 * 0 - 1) * (A.coeff 0).natDegree :=
  natDegree_resultant_derivative_padded_add_sq_le A 0 _ fun i hi ↦ by
    rw [Nat.le_zero.mp hi, Nat.zero_add]

-- The inequality can be strict: in characteristic two, `C (X ^ 3) * Y ^ 2` has a coefficient of
-- `X`-degree `3`, while its derivative is `0`.
example : Bivariate.degreeX (C ((X : (ZMod 2)[X]) ^ 3) * X ^ 2).derivative = 0 := by
  have h : ((2 : ℕ) : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  rw [derivative_C_mul_X_pow, h, mul_zero, C_0, zero_mul]
  simp [Bivariate.degreeX]

-- The source bound with separate budgets for `A` and its derivative, in the source argument
-- order: `(2 * b - 1) * h`.
example (A : Polynomial (Polynomial (ZMod 4))) {b h : ℕ} (hA : Bivariate.degreeX A ≤ h)
    (hA' : Bivariate.degreeX A.derivative ≤ h) :
    (resultant A.derivative A (b - 1) b).natDegree ≤ (2 * b - 1) * h := by
  rw [resultant_comm_sub_one]
  refine (natDegree_resultant_le_degreeX A A.derivative b (b - 1)).trans ?_
  calc (b - 1) * Bivariate.degreeX A + b * Bivariate.degreeX A.derivative
      ≤ (b - 1) * h + b * h := Nat.add_le_add (Nat.mul_le_mul_left _ hA) (Nat.mul_le_mul_left _ hA')
    _ = (2 * b - 1) * h := by
      rw [← Nat.add_mul]
      congr 1
      omega

-- The source bound from the height of `A` alone: with `degreeX_derivative_le`, the declared
-- degree `b` need not be the actual degree.
example (A : Polynomial (Polynomial (ZMod 4))) {b h : ℕ} (hA : Bivariate.degreeX A ≤ h) :
    (resultant A A.derivative b (b - 1)).natDegree ≤ (2 * b - 1) * h := by
  refine (natDegree_resultant_le_degreeX A A.derivative b (b - 1)).trans ?_
  calc (b - 1) * Bivariate.degreeX A + b * Bivariate.degreeX A.derivative
      ≤ (b - 1) * h + b * h := Nat.add_le_add (Nat.mul_le_mul_left _ hA)
        (Nat.mul_le_mul_left _ ((Bivariate.degreeX_derivative_le A).trans hA))
    _ = (2 * b - 1) * h := by
      rw [← Nat.add_mul]
      congr 1
      omega
