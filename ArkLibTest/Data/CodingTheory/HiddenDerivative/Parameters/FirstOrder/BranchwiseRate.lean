/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.BranchwiseRate

/-!
# Branchwise first-order rate acceptance tests

The upper branch evaluated at `ρ = 1/2`, `firstOrderBranchBeta_pos` under the stronger
hypotheses `ρ < 1` and a threshold bound, and a case showing that `a < 1` is needed there.
-/

namespace ReedSolomon.HiddenDerivative

private theorem rateSwitch_lt_half : firstOrderRateSwitch < 1 / 2 := by
  -- `11 - 3√13 < 1/2` iff `7 < 2√13` iff `49 < 52`.
  have h : (7 : ℝ) < 2 * Real.sqrt 13 := by
    have h13 : (7 / 2 : ℝ) < Real.sqrt 13 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  unfold firstOrderRateSwitch
  linarith

/-- At `ρ = 1/2` the ratio is on the upper branch: `3(1 - a) / (2 · 3/2) = 1 - a`. -/
example (a : ℝ) : firstOrderBranchBeta (1 / 2) a = 1 - a := by
  rw [firstOrderBranchBeta_eq_clean rateSwitch_lt_half.le, firstOrderRateBeta]
  ring

/-- At `ρ = 1/2`, `a = 3/4`, the ratio is `1/4`. -/
example : firstOrderBranchBeta (1 / 2) (3 / 4) = 1 / 4 := by
  rw [firstOrderBranchBeta_eq_clean rateSwitch_lt_half.le, firstOrderRateBeta]
  norm_num

/-- `firstOrderBranchBeta_pos` under the stronger hypotheses `ρ < 1` and a threshold bound,
neither of which it needs. -/
example {rho a : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (_ha : firstOrderBranchThreshold rho < a) (haOne : a < 1) :
    0 < firstOrderBranchBeta rho a :=
  firstOrderBranchBeta_pos hrho (by linarith) haOne

/-- `a < 1` is needed in `firstOrderBranchBeta_pos`: on the upper branch at `a = 1` the ratio is
`0`. -/
example : ¬ 0 < firstOrderBranchBeta (1 / 2) 1 := by
  rw [firstOrderBranchBeta_eq_clean rateSwitch_lt_half.le, firstOrderRateBeta]
  norm_num

end ReedSolomon.HiddenDerivative
