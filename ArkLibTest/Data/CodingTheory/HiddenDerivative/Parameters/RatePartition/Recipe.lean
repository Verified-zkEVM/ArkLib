/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Recipe

/-!
# Finite multiplicity recipe acceptance tests

A concrete strict rate gate supplies an accepted multiplicity, and the selected multiplicity is
no larger than any other multiplicity with positive budget and finite ratio above one.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

private theorem test_rate_gate : 1 < rateGamma 1 2 5 := by
  have hcoef : fixedRateCoefficient 1 ≤ Real.log 5 := by
    rw [fixedRateCoefficient]
    norm_num only [one_mul, mul_one, mul_zero, add_zero]
    apply Real.log_le_log <;> norm_num
  have horder : fixedRateCoefficient 1 + 0 ≤ 1 * Real.log (5 : ℝ) := by
    nlinarith [hcoef]
  have hmargin : 0 < 0 + 1 * Real.log (27 * 1 / 20) := by
    norm_num only [zero_add, one_mul]
    exact Real.log_pos (by norm_num)
  have h := rateGamma_gt_one_of_exponent_margin (rate := 1) (gap := 1) (epsilon := 0)
    (order := 5) (by norm_num) (by norm_num) (by norm_num) horder hmargin
  have hsum : (1 : ℝ) + 1 = 2 := by norm_num
  rw [← hsum]
  exact h

/-- The selected multiplicity at `R = 1`, `a = 2`, and `d = 5` passes all finite checks. -/
example :
    let multiplicity := rateMultiplicity (by norm_num) (by norm_num) (by norm_num) test_rate_gate
    0 < multiplicity ∧
      0 < partitionWeightBudget 1 2 5 multiplicity ∧
      1 < partitionFiniteRatio 1 2 5 multiplicity :=
  rateMultiplicity_spec (by norm_num) (by norm_num) (by norm_num) test_rate_gate

/-- The selected multiplicity is no larger than any accepted multiplicity for this gate. -/
example :
    ∃ candidate, rateMultiplicity (by norm_num) (by norm_num) (by norm_num) test_rate_gate ≤
        candidate ∧
      0 < candidate ∧ 0 < partitionWeightBudget 1 2 5 candidate ∧
        1 < partitionFiniteRatio 1 2 5 candidate := by
  obtain ⟨candidate, hcandidate⟩ :=
    exists_partitionFiniteParameters_of_rateGamma_gt_one (by norm_num) (by norm_num)
      (by norm_num) test_rate_gate
  exact ⟨candidate, rateMultiplicity_minimal (by norm_num) (by norm_num) (by norm_num)
    test_rate_gate hcandidate, hcandidate⟩

/-- At `R = a = d = 1`, the limiting gate is `9/20`, so the recipe's strict gate hypothesis fails.
-/
example : ¬ 1 < rateGamma 1 1 1 := by norm_num [rateGamma]

end ReedSolomon.HiddenDerivative.RatePartition
