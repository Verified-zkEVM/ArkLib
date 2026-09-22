/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageComparison

/-!
# Stage-charge comparison acceptance tests

The two stage charges at a concrete stage, the comparison in the form with incidence ratios at
least one, and cases showing that `2 ≤ K`, `1 ≤ η` and `1 ≤ t` are needed.
-/

namespace ReedSolomon.HiddenDerivative

/-- At `ℓ = h = 1`, `v = 3`, `τ = 2`, `s = 1` and `c = 0`, the order-zero charge is
`1 · 5 + 3 · 3 = 14`. -/
example : orderZeroCurveStageCharge 1 1 1 0 3 2 = 14 := by
  norm_num [orderZeroCurveStageCharge, firstOrderTaylorTotalCap]

/-- At `K = 3` and `η = t = 1`, the order-one charge at first-derivative degree `1` is the joint
degree `70`. -/
example : orderOneCurveStageCharge 3 1 1 1 1 0 3 1 2 1 = 70 := by
  have : firstOrderCurveJointStageOne 3 1 1 3 1 2 = 70 := rfl
  norm_num [orderOneCurveStageCharge, this]

/-- The comparison with all incidence ratios at least one. -/
example (K ell h : ℕ) {s η t c : ℚ} (hK : 2 ≤ K) (hs : 1 ≤ s) (hη : 1 ≤ η) (ht : 1 ≤ t)
    (hc : 0 ≤ c) (v τ : ℕ) :
    orderZeroCurveStageCharge ell h s c v τ ≤ orderOneCurveStageCharge K ell h s t c v 1 τ η :=
  orderZeroCurveStageCharge_le_orderOne K ell h hK (by linarith) hη ht hc v τ

/-- `orderZeroCurveStageCharge_le_orderOne` needs `2 ≤ K`: at `K = 1`, `ℓ = h = 0`, `v = 2`,
`τ = 0` and unit factors, the order-zero charge is `2` and the order-one charge is `1`. -/
example : orderZeroCurveStageCharge 0 0 1 1 2 0 = 2 ∧
    orderOneCurveStageCharge 1 0 0 1 1 1 2 1 0 1 = 1 := by
  have hJ : firstOrderCurveJointStageOne 1 0 0 2 1 0 = 0 := rfl
  have hB : firstOrderCurveFiberStageOne 1 2 1 0 = 1 := rfl
  norm_num [orderZeroCurveStageCharge, orderOneCurveStageCharge, firstOrderTaylorTotalCap, hJ, hB]

/-- `orderZeroCurveStageCharge_le_orderOne` needs `1 ≤ η`: at `η = 0`, `s = 1`, `c = 0` the
order-one charge is `0` and the order-zero charge at `K = 2`, `ℓ = 1`, `v = 1` is `1`. -/
example : orderZeroCurveStageCharge 1 0 1 0 1 0 = 1 ∧
    orderOneCurveStageCharge 2 1 0 1 1 0 1 1 0 0 = 0 := by
  norm_num [orderZeroCurveStageCharge, orderOneCurveStageCharge, firstOrderTaylorTotalCap]

/-- `orderZeroCurveStageCharge_le_orderOne` needs `1 ≤ t`: at `t = 0`, `s = 0`, `c = 1` the
order-one charge is `0` and the order-zero charge at `v = 1` is `1`. -/
example : orderZeroCurveStageCharge 0 0 0 1 1 0 = 1 ∧
    orderOneCurveStageCharge 2 0 0 0 0 1 1 1 0 1 = 0 := by
  norm_num [orderZeroCurveStageCharge, orderOneCurveStageCharge]

end ReedSolomon.HiddenDerivative
