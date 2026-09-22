/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RateBound

/-!
# First-order rate threshold acceptance tests

The recipe at `R = 1/2`, `a = 3/4` computed in full, the threshold at the boundary `R = 1`, cases
showing that the kept hypotheses are needed, and the forms under `0 < R < a < 1` derived from the
stated theorems.
-/

namespace ReedSolomon.HiddenDerivative

/-! ### A concrete instance: `R = 1/2`, `a = 3/4` -/

/-- `β = 3 (1/4) / (2 (3/2)) = 1/4`. -/
private theorem test_beta : firstOrderRateBeta (1 / 2) (3 / 4) = 1 / 4 := by
  norm_num [firstOrderRateBeta]

/-- `Q(1/2, 3/4) = 9/8 + 1/32 = 37/32`. -/
private theorem test_clean : firstOrderCleanExpression (1 / 2) (3 / 4) = 37 / 32 := by
  norm_num [firstOrderCleanExpression]

/-- Rank density `1/8 - 1/32 + 1/192 = 19/192` at `β = 1/4`. -/
private theorem test_rank : firstOrderRankDensity (1 / 4) = 19 / 192 := by
  norm_num [firstOrderRankDensity]

/-- Source density `9/64 - 3/128 + 1/768 = 91/768` at `β = 1/4`. -/
private theorem test_source : firstOrderSourceDensity (1 / 2) (3 / 4) (1 / 4) = 91 / 768 := by
  norm_num [firstOrderSourceDensity]

/-- The factorization at this instance: `91/768 - 19/192 = (1/8)(37/32 - 1)`. -/
example : firstOrderSourceDensity (1 / 2) (3 / 4) (1 / 4) - firstOrderRankCubicEnvelope (1 / 4) =
    1 / 8 * (firstOrderCleanExpression (1 / 2) (3 / 4) - 1) := by
  rw [firstOrderSourceDensity_sub_cubicEnvelope _ _ _ (by norm_num), ← test_beta,
    firstOrderRateBeta_bracket _ _ (by norm_num) (by norm_num), test_beta]
  norm_num

/-- `a₁(1/2) < √(1/2) < 3/4`. -/
private theorem test_threshold_lt : firstOrderRateThreshold (1 / 2) < 3 / 4 := by
  refine (firstOrderRateThreshold_lt_sqrt (by norm_num) (by norm_num)).trans ?_
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- The surplus theorem at this instance agrees with the computed densities. -/
example : firstOrderRankDensity (firstOrderRateBeta (1 / 2) (3 / 4)) <
    firstOrderSourceDensity (1 / 2) (3 / 4) (firstOrderRateBeta (1 / 2) (3 / 4)) :=
  firstOrderRate_surplus_pos (by norm_num) (by norm_num) (by norm_num) test_threshold_lt

example : firstOrderRankDensity (1 / 4) < firstOrderSourceDensity (1 / 2) (3 / 4) (1 / 4) := by
  rw [test_rank, test_source]
  norm_num

/-! ### The boundary `R = 1` -/

/-- `a₁(1) = (3 + 2√4) / 7 = 1`. -/
private theorem test_threshold_one : firstOrderRateThreshold 1 = 1 := by
  have h : Real.sqrt (1 * (5 - 1) * (2 - 1)) = 2 := by
    rw [show (1 * (5 - 1) * (2 - 1) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [firstOrderRateThreshold, h]
  norm_num

/-- `rate_lt_firstOrderRateThreshold` needs `R < 1`: `a₁(1) = 1`. -/
example : ¬ (1 : ℝ) < firstOrderRateThreshold 1 := by
  rw [test_threshold_one]
  exact lt_irrefl 1

/-- `firstOrderRateThreshold_lt_sqrt` needs `R < 1`: `a₁(1) = √1`. -/
example : ¬ firstOrderRateThreshold 1 < Real.sqrt 1 := by
  rw [test_threshold_one, Real.sqrt_one]
  exact lt_irrefl 1

/-- `Q(1, 1) = 1` also at the boundary, as `firstOrderCleanExpression_threshold_eq_one` allows. -/
example : firstOrderCleanExpression 1 (firstOrderRateThreshold 1) = 1 :=
  firstOrderCleanExpression_threshold_eq_one one_pos (by norm_num)

/-! ### The kept hypotheses are needed -/

/-- `firstOrderRateBeta_pos` needs `R < 2`: `β(3, 0) = -3/2`. -/
example : firstOrderRateBeta 3 0 = -3 / 2 := by
  norm_num [firstOrderRateBeta]

/-- `firstOrderRateBeta_pos` needs `a < 1`: `β(R, 1) = 0`. -/
example (R : ℝ) : firstOrderRateBeta R 1 = 0 := by
  norm_num [firstOrderRateBeta]

/-- `firstOrderRateBeta_lt_three_four` needs `R < 2a`: `β(1, 1/2) = 3/4`. -/
example : firstOrderRateBeta 1 (1 / 2) = 3 / 4 := by
  norm_num [firstOrderRateBeta]

/-- `firstOrderRateBeta_lt_agreement_div_rate` cannot drop `R ≤ a`: at `R = 1`, `a = 3/5` the
exact condition `3R < a(4 + R)` is an equality and `β = a / R`. -/
example : firstOrderRateBeta 1 (3 / 5) = 3 / 5 / 1 := by
  norm_num [firstOrderRateBeta]

/-- `firstOrderRate_surplus_pos` needs `a < 1`: at `a = 1` both densities are `0`, although
`a₁(1/2) < 1`. -/
example : firstOrderRateThreshold (1 / 2) < 1 ∧
    ¬ firstOrderRankDensity (firstOrderRateBeta (1 / 2) 1) <
      firstOrderSourceDensity (1 / 2) 1 (firstOrderRateBeta (1 / 2) 1) := by
  refine ⟨test_threshold_lt.trans (by norm_num), ?_⟩
  norm_num [firstOrderRateBeta, firstOrderRankDensity, firstOrderSourceDensity]

/-! ### Forms under `0 < R < a < 1` -/

example {R a : ℝ} (ha : a < 1) (hR : R < 1) : 0 < firstOrderRateBeta R a :=
  firstOrderRateBeta_pos ha (by linarith)

example {R a : ℝ} (hR : 0 < R) (hRa : R < a) (ha : a < 1) :
    firstOrderRateBeta R a < 3 / 4 :=
  firstOrderRateBeta_lt_three_four (by linarith) (by linarith)

example {R a : ℝ} (hR : 0 < R) (hRa : R < a) (ha : a < 1) :
    firstOrderRateBeta R a < a / R :=
  firstOrderRateBeta_lt_agreement_div_rate hR (by linarith) hRa.le

example {R : ℝ} (hR : 0 < R) (hRone : R < 1) :
    firstOrderCleanExpression R (firstOrderRateThreshold R) = 1 :=
  firstOrderCleanExpression_threshold_eq_one hR (by linarith)

end ReedSolomon.HiddenDerivative
