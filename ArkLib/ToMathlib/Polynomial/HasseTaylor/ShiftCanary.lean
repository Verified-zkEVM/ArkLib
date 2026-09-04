/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! Mutation canaries for Hasse--Taylor shift orientation, characteristic, and signs. -/

namespace Polynomial

noncomputable section

/-- Detects wrong sign, fixed-basepoint derivatives, and confusion with the increment quotient. -/
example : normalizedBackwardTaylorError (1 : ℤ) (X ^ 2) 1 = -X := by
  have hderiv : hasseDeriv 1 (X ^ 2 : ℤ[X]) = C 2 * X := by
    rw [X_pow_eq_monomial, hasseDeriv_monomial]
    norm_num
    rw [← C_mul_X_pow_eq_monomial]
    simp
  have hshift : taylor (1 : ℤ) (hasseDeriv 1 (X ^ 2)) = C 2 * X + C 2 := by
    rw [hderiv, taylor_mul, taylor_C, taylor_X, mul_add]
    change C (2 : ℤ) * X + C 2 * C 1 = C 2 * X + C 2
    rw [← C_mul]
    norm_num
  have hres : backwardTaylorResidual (1 : ℤ) (X ^ 2) 1 = -(X ^ 2) := by
    norm_num [backwardTaylorResidual, movingHasseSum, taylor_apply, hshift]
    ring
  rw [normalizedBackwardTaylorError, hres]
  ext n
  by_cases hn : n = 1
  · simp [coeff_divX, coeff_X_pow, coeff_X, hn]
  · have hn' : 1 ≠ n := Ne.symm hn
    simp [coeff_divX, coeff_X_pow, coeff_X, hn, hn']

private theorem hasseDeriv_one_X_cube :
    hasseDeriv 1 (X ^ 3 : ℤ[X]) = monomial 2 3 := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  norm_num

private theorem hasseDeriv_two_X_cube :
    hasseDeriv 2 (X ^ 3 : ℤ[X]) = monomial 1 3 := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  norm_num

/-- A genuine order-two example exercises both the positive first-Hasse and negative
second-Hasse moving terms. -/
private theorem X_cube_order_two_oracle :
    movingHasseSum (1 : ℤ) (X ^ 3) 2 = C 3 * X + C 3 * X ^ 2 ∧
      normalizedBackwardTaylorError (1 : ℤ) (X ^ 3) 2 = X ^ 2 := by
  have hm : movingHasseSum (1 : ℤ) (X ^ 3) 2 = C 3 * X + C 3 * X ^ 2 := by
    norm_num [movingHasseSum, Finset.sum_range_succ, hasseDeriv_one_X_cube,
      hasseDeriv_two_X_cube, taylor_monomial, taylor_C, taylor_apply]
    ring
  refine ⟨hm, ?_⟩
  have hr : backwardTaylorResidual (1 : ℤ) (X ^ 3) 2 = X ^ 3 := by
    rw [backwardTaylorResidual, hm]
    norm_num [taylor_apply]
    ring
  rw [normalizedBackwardTaylorError, hr]
  ext n
  by_cases hn : n = 2
  · subst n
    simp [coeff_divX, coeff_X_pow]
  · simp [coeff_divX, coeff_X_pow, hn]

/-- A nontrivial scalar checks the packaged linear map and its coefficient action. -/
example :
    normalizedBackwardTaylorErrorLinearMap (1 : ℤ) 2
        ((7 : ℤ) • (X ^ 3 : ℤ[X])) = C 7 * X ^ 2 := by
  rw [LinearMap.map_smul, normalizedBackwardTaylorErrorLinearMap_apply,
    X_cube_order_two_oracle.2, smul_eq_C_mul]

/-- Asymmetric centers detect an inverse shift or a dropped first center in composition. -/
example :
    movingHasseSum (1 : ZMod 5) (taylor (2 : ZMod 5) (X ^ 2)) 1 =
      C 2 * X ^ 2 + X := by
  rw [movingHasseSum_taylor]
  have hc : (1 + 2 : ZMod 5) = 3 := by decide
  rw [hc]
  norm_num [movingHasseSum, hasseDeriv_monomial, taylor_apply]
  have h : C (2 : ZMod 5) * C 3 = 1 := by
    rw [← C_mul]
    congr 1
  calc
    (X * (C 2 * (X + C 3)) : (ZMod 5)[X]) =
        C 2 * X ^ 2 + X * (C 2 * C 3) := by ring
    _ = C 2 * X ^ 2 + X := by rw [h, mul_one]

/-- Scaling by `2` exercises both powers of `2` and the alternating order-one sign;
the normalized error carries the additional leading factor from removing `X`. -/
example :
    normalizedBackwardTaylorError (0 : ZMod 5)
        ((X ^ 3).comp (C 2 * X)) 1 = C 4 * X ^ 2 := by
  rw [normalizedBackwardTaylorError_comp_C_mul_X]
  simp only [mul_zero]
  have hbase : normalizedBackwardTaylorError (0 : ZMod 5) (X ^ 3) 1 = C 3 * X ^ 2 := by
    have hres : backwardTaylorResidual (0 : ZMod 5) (X ^ 3) 1 = C 3 * X ^ 3 := by
      norm_num [backwardTaylorResidual, movingHasseSum, hasseDeriv_monomial,
        Finset.sum_range_succ, taylor_zero]
      have hc : (1 - C 3 : (ZMod 5)[X]) = C 3 := by
        rw [← C_1, ← map_sub]
        congr 1
      calc
        (X ^ 3 - X * (C 3 * X ^ 2) : (ZMod 5)[X]) =
            (1 - C 3) * X ^ 3 := by ring
        _ = C 3 * X ^ 3 := by rw [hc]
    rw [normalizedBackwardTaylorError, hres]
    ext n
    simp [coeff_divX, coeff_X_pow]
  norm_num [hbase, mul_pow]
  calc
    (C 2 * (C 3 * (C 2 ^ 2 * X ^ 2)) : (ZMod 5)[X]) =
        (C 2 * C 3 * C 2 ^ 2) * X ^ 2 := by ring
    _ = C (2 * 3 * 2 ^ 2 : ZMod 5) * X ^ 2 := by
      simp only [map_mul, map_pow]
    _ = C 4 * X ^ 2 := by congr 2

/-- Order zero reduces to the ordinary shifted increment quotient. -/
example (a : ℤ) (p : ℤ[X]) :
    normalizedBackwardTaylorError a p 0 = shiftIncrementQuotient a p :=
  normalizedBackwardTaylorError_zero a p

/-- Once the truncation reaches the polynomial degree, both residuals vanish. -/
example :
    backwardTaylorResidual (7 : ℤ) (X ^ 2) 2 = 0 ∧
      normalizedBackwardTaylorError (7 : ℤ) (X ^ 2) 2 = 0 := by
  constructor
  · apply backwardTaylorResidual_eq_zero_of_natDegree_le
    norm_num [natDegree_X_pow]
  · apply normalizedBackwardTaylorError_eq_zero_of_natDegree_le
    norm_num [natDegree_X_pow]

/-- A concrete coefficient reduction checks naturality across genuinely different rings. -/
example :
    (normalizedBackwardTaylorError (2 : ℤ) (X ^ 3 + C 7) 2).map
        (Int.castRingHom (ZMod 5)) =
      normalizedBackwardTaylorError ((Int.castRingHom (ZMod 5)) 2)
        ((X ^ 3 + C 7 : ℤ[X]).map (Int.castRingHom (ZMod 5))) 2 := by
  exact map_normalizedBackwardTaylorError (Int.castRingHom (ZMod 5))
    (2 : ℤ) (X ^ 3 + C 7) 2

end

end Polynomial
