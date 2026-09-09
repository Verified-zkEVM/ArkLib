/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageSum
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Numerator
/-!
# Tight first-order curve stage-charge acceptance tests

These examples cover the common-exponent boundary and the degenerate cap schedules used by the
finite first-order curve bound.
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

open SymbolicSeparantChain

/-- Natural subtraction gives the tight common exponent one when `K = 2`. -/
example : 2 * (2 : ℕ) - 3 = 1 := by omega

/-- That tight exponent is sufficient for the order-one Taylor chart. -/
example : TaylorExponentSufficient 1 2 (2 * 2 - 3) :=
  taylorExponentSufficient_two_mul_sub_three 1 (by omega)

/-- At the full-triangle boundary, the order-one joint factor is `λ₁ * η`. -/
example : curveStageOne 2 3 5 (2 : ℚ) 5 7 4 4 (τ := 1) (η := 3) = 2576 := by
  norm_num [curveStageOne, firstOrderCurveJointStageOne, firstOrderCurveFiberStageOne,
    firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    AffineHilbert.mixedDerivativeImageDegree, AffineHilbert.fixedFiberDerivativeImageDegree]

/-- Full stage charges promote from order zero to order one when all three ratios and the
accidental-agreement factor are in their geometric ranges. -/
example : curveStageZero 2 3 5 (2 : ℚ) 7 4 (τ := 1) ≤
    curveStageOne 2 3 5 (2 : ℚ) 5 7 4 1 (τ := 1) (η := 3) := by
  exact curveStageZero_le_one_of_factors 2 3 5 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 4 1

/-- A zero derivative cap leaves no order-one stages. -/
example (K μ ell h τ : ℕ) : firstOrderCurveJointOne K μ 0 ell h (τ := τ) = 0 := by
  unfold firstOrderCurveJointOne
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < μ := Finset.mem_range.mp hi
  simp [not_le_of_gt hi']

/-- A zero derivative cap also leaves no order-one fiber budget. -/
example (K μ τ : ℕ) : firstOrderCurveFiberOne K μ 0 (τ := τ) = 0 := by
  unfold firstOrderCurveFiberOne
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < μ := Finset.mem_range.mp hi
  simp [not_le_of_gt hi']

/-- When the derivative cap exceeds the jet cap, natural subtraction leaves no order-zero
stages. -/
example (K ell h τ : ℕ) : firstOrderCurveJointZero K 2 5 ell h (τ := τ) = 0 := by
  simp [firstOrderCurveJointZero]

/-- The same overlarge cap leaves no order-zero fiber budget. -/
example : firstOrderCurveFiberZero 2 5 = 0 := by
  simp [firstOrderCurveFiberZero]

/-- Missing stages add only nonnegative full charges to the extremal schedule. -/
example : curveStageZero 2 3 5 (2 : ℚ) 7 2 (τ := 1) ≤
    firstOrderStageCap
      (fun v ↦ curveStageZero 2 3 5 (2 : ℚ) 7 v (τ := 1))
      (fun v r ↦ curveStageOne 2 3 5 (2 : ℚ) 5 7 v r (τ := 1) (η := 3)) 4 2 := by
  norm_num [firstOrderStageCap, curveStageZero, curveStageOne,
    Finset.sum_range_succ, Finset.sum_Ico_succ_top, firstOrderCurveJointStageOne,
    firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    AffineHilbert.mixedDerivativeImageDegree, AffineHilbert.fixedFiberDerivativeImageDegree]

/-- The direct order-one joint ratio is at least one, including at an endpoint. -/
example : 1 ≤ firstOrderCurveDirectRatio 11 3 8 :=
  firstOrderCurveDirectRatio_one_le (by omega) (by omega)

end ReedSolomon.HiddenDerivative
