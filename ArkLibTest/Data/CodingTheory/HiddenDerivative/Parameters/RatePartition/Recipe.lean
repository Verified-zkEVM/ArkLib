/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Recipe
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite multiplicity recipe acceptance tests

A concrete strict rate gate supplies an accepted multiplicity, and the selected multiplicity is
no larger than any other multiplicity with positive budget and finite ratio above one.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

private theorem test_rate_gate : 1 < rateGamma 1 2 20 := by
  have hcoef : fixedRateCoefficient 1 ≤ Real.log 20 := by
    rw [fixedRateCoefficient]
    norm_num only [one_mul, mul_one, mul_zero, add_zero]
    apply Real.log_le_log <;> norm_num
  have horder : fixedRateCoefficient 1 + 0 ≤ 1 * Real.log (20 : ℝ) := by
    nlinarith [hcoef]
  have hmargin : 0 < 0 + 1 * Real.log (27 * 1 / 20) := by
    norm_num only [zero_add, one_mul]
    exact Real.log_pos (by norm_num)
  have h := rateGamma_gt_one_of_exponent_margin (rate := 1) (gap := 1) (epsilon := 0)
    (order := 20) (by norm_num) (by norm_num) (by norm_num) horder hmargin
  have hsum : (1 : ℝ) + 1 = 2 := by norm_num
  rw [← hsum]
  exact h

private theorem test_log_one_twenty_lt_five : Real.log 120 < 5 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hexp5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hexpLower : (27 / 10 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num at h ⊢
    linarith
  calc
    (120 : ℝ) < (27 / 10 : ℝ) ^ 5 := by norm_num
    _ < Real.exp 1 ^ 5 := by gcongr
    _ = Real.exp 5 := by rw [← hexp5]

/-- The candidate multiplicity `100000` has a positive derivative-weight budget. -/
private theorem test_candidate_weight_budget :
    800000 ≤ partitionWeightBudget 1 2 20 100000 := by
  have hlog : Real.log 120 < 5 := test_log_one_twenty_lt_five
  unfold partitionWeightBudget
  norm_num only [Nat.cast_ofNat]
  apply Nat.le_floor
  rw [le_div_iff₀ (show (0 : ℝ) < 1 * Real.log 120 by positivity)]
  have hscaled : (800000 : ℝ) * Real.log 120 ≤ 4000000 := by nlinarith [hlog]
  simp only [one_mul]
  exact_mod_cast hscaled

/-- The finite ratio for `R = 1`, `a = 2`, `d = 20`, `m = 100000` exceeds one. -/
private theorem test_candidate_finite_ratio :
    1 < partitionFiniteRatio 1 2 20 100000 := by
  have hbudget := test_candidate_weight_budget
  have hbudget_pos : 0 < partitionWeightBudget 1 2 20 100000 := by
    exact lt_of_lt_of_le (by norm_num) hbudget
  have hbudget_real : (800000 : ℝ) ≤ partitionWeightBudget 1 2 20 100000 := by
    exact_mod_cast hbudget
  have hlambda : partitionInverseRadius 1 2 20 100000 ≤ 5 / 2 := by
    rw [partitionInverseRadius_eq]
    apply (div_le_iff₀ (show (0 : ℝ) <
      (partitionWeightBudget 1 2 20 100000 : ℝ) by exact_mod_cast hbudget_pos)).mpr
    norm_num
    nlinarith
  let lambda := partitionInverseRadius 1 2 20 100000
  have hfactor : (1 : ℝ) + 20 * 21 / (2 * 100000) = 10021 / 10000 := by norm_num
  have hexponent : lambda * (1 + 20 * 21 / (2 * 100000)) < 3 := by
    rw [hfactor]
    dsimp only [lambda] at hlambda ⊢
    nlinarith
  have hexp3 : Real.exp 3 < 27 := by
    have hpow : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hpow]
    calc
      Real.exp 1 ^ 3 < 3 ^ 3 := by gcongr; exact Real.exp_one_lt_three
      _ = 27 := by norm_num
  have hexponent_exp : Real.exp (lambda * (1 + 20 * 21 / (2 * 100000))) < 27 :=
    (Real.exp_lt_exp.mpr hexponent).trans hexp3
  have hnegative_exp : 1 / 27 <
      Real.exp (-(lambda * (1 + 20 * 21 / (2 * 100000))) : ℝ) := by
    rw [Real.exp_neg]
    have hreciprocal :=
      (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 27) (Real.exp_pos _)).2 hexponent_exp
    simpa only [one_div] using hreciprocal
  have hnumerator : 1001 / 1000 <
      (27 / 20 : ℝ) * 21 * Real.exp (-(lambda * (1 + 20 * 21 / (2 * 100000)))) := by
    calc
      (1001 / 1000 : ℝ) < (27 / 20) * 21 * (1 / 27) := by norm_num
      _ < (27 / 20) * 21 *
          Real.exp (-(lambda * (1 + 20 * 21 / (2 * 100000)))) := by
        gcongr
  have hdenominator : 1 + 21 * lambda / 100000 < 1001 / 1000 := by
    dsimp only [lambda] at hlambda ⊢
    norm_num
    nlinarith
  have hlambda_nonneg : 0 ≤ lambda := by
    dsimp only [lambda]
    exact partitionInverseRadius_nonneg 1 2 20 100000
  have hdenominator_pos : 0 < 1 + 21 * lambda / 100000 := by positivity
  have hratio_expr : 1 <
    (27 / 20 : ℝ) * (20 + 1) *
      Real.exp (-(lambda * (1 + (20 : ℝ) * (20 + 1) / (2 * 100000)))) /
      (1 + (20 + 1) * lambda / 100000) := by
    norm_num
    apply (lt_div_iff₀ hdenominator_pos).2
    linarith [hnumerator, hdenominator]
  simpa [partitionFiniteRatio, lambda, Nat.cast_add] using hratio_expr

/-- The selected multiplicity at `R = 1`, `a = 2`, and `d = 20` passes all finite checks. -/
example :
    let multiplicity := rateMultiplicity (by norm_num) (by norm_num) (by norm_num) test_rate_gate
    0 < multiplicity ∧
      0 < partitionWeightBudget 1 2 20 multiplicity ∧
      1 < partitionFiniteRatio 1 2 20 multiplicity :=
  rateMultiplicity_spec (by norm_num) (by norm_num) (by norm_num) test_rate_gate

/-- The candidate `m = 100000` is accepted, and the recipe returns a no-larger multiplicity. -/
example :
    rateMultiplicity (by norm_num) (by norm_num) (by norm_num) test_rate_gate ≤ 100000 := by
  apply rateMultiplicity_minimal (by norm_num) (by norm_num) (by norm_num) test_rate_gate
  refine ⟨by norm_num, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) test_candidate_weight_budget
  · exact test_candidate_finite_ratio

/-- At `R = a = d = 1`, the limiting gate is `9/20`, so the recipe's strict gate hypothesis fails.
-/
example : ¬ 1 < rateGamma 1 1 1 := by norm_num [rateGamma]

end ReedSolomon.HiddenDerivative.RatePartition
