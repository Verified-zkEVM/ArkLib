/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.BlockLength
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.ClosedMultiplicity
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Gate
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Moment
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformParameters
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rate-partition parameter acceptance tests

Concrete checks for the block-length guards, multiplicity rounding bounds, finite-ratio limits,
rate gate, simplex moments and gap-only ambient guards.
-/

open MeasureTheory Set Finset Filter Topology

namespace ReedSolomon.HiddenDerivative.RatePartition

private theorem one_lt_log_six : 1 < Real.log 6 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [Real.exp_one_lt_d9]

private theorem log_six_lt_two : Real.log 6 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9]

private theorem test_weightBudget : partitionWeightBudget 1 1 1 2 = 1 := by
  have hlog := one_lt_log_six
  have hlog' := log_six_lt_two
  rw [partitionWeightBudget, Nat.floor_eq_iff (by norm_num; positivity)]
  norm_num
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-! ### Block-length thresholds -/

/-- At `n = 13`, with message dimension `6` and agreement `(1/2) · 13 ≤ 7`, the ambient degree
`D = ⌊13/2⌋₊` satisfies `3 ≤ D`, `D + 1 ≤ 13`, and `⌈13/2⌉₊ ≤ 7`. -/
example : 3 ≤ ⌊(1 / 2 : ℝ) * 13⌋₊ ∧ ⌊(1 / 2 : ℝ) * 13⌋₊ + 1 ≤ 13 ∧
    ⌈(1 / 2 : ℝ) * 13⌉₊ ≤ 7 := by
  obtain ⟨hD, -, -, hn, -, -, hA, -⟩ :=
    rateBlockThreshold_guards (rate := 1 / 2) (agreement := 1 / 2) (order := 2)
      (multiplicity := 3) (n := 13) (k := 6) (A := 7) (by norm_num) (by norm_num)
      (by norm_num [rateBlockThreshold, rateJetCap]) (by norm_num) (by norm_num)
  exact ⟨hD, hn, hA⟩

/-- At `n = 24`, with `R = a = 1/2`, `d = 2` and `m = 3`, the padded threshold gives the
ambient-degree and agreement guards. -/
example : 3 ≤ ⌊(1 / 2 : ℝ) * 24⌋₊ ∧ ⌊(1 / 2 : ℝ) * 24⌋₊ + 1 ≤ 24 ∧
    ⌈(1 / 2 : ℝ) * 24⌉₊ ≤ 12 := by
  obtain ⟨hD, -, -, hn, -, -, hA, -⟩ :=
    paddedRateBlockThreshold_guards (rate := 1 / 2) (agreement := 1 / 2) (order := 2)
      (multiplicity := 3) (n := 24) (k := 12) (A := 12) (by norm_num) (by norm_num)
      (by norm_num [paddedRateBlockThreshold, rateJetCap]) (by norm_num) (by norm_num)
  exact ⟨hD, hn, hA⟩

/-- At the ratio `3/2 = 1 + 1/2`, the margin height of `3` is `⌈3 / (1/2)⌉₊ = 6`. -/
example : marginHeight 3 (3 / 2) = 6 := by
  have h := marginHeight_one_add_inv (bound := 3) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-! ### Closed-form multiplicity -/

/-- The exact ratio factorization at `R = a = d = 1`, `m = 2`. -/
example : partitionFiniteRatio 1 1 1 2 =
    (27 / 20 : ℝ) * 1 * (((1 : ℕ) : ℝ) + 1) *
      Real.exp (-((1 : ℝ) / 1 * Real.log (6 * ((1 : ℕ) : ℝ)))) *
      Real.exp (-partitionRoundingLoss 1 1 1 2) :=
  partitionFiniteRatio_eq_mul_exp_neg_roundingLoss 1 1 1 2

/-- At scale `3`, order `1` has closed-form multiplicity at least `1 + 2`. -/
example : 1 + 2 ≤ closedMultiplicity 3 1 :=
  add_two_le_closedMultiplicity (by norm_num) (by norm_num)

/-- At scale `3`, order `1`, the closed-form weight budget is positive. -/
example : 0 < partitionWeightBudget 1 1 1 (closedMultiplicity 3 1) :=
  partitionWeightBudget_closedMultiplicity_pos (by norm_num) (by norm_num) (by norm_num)

/-- At scale `3`, order `1`, the inverse radius is bounded by the stated rounding factor. -/
example : partitionInverseRadius 1 1 1 (closedMultiplicity 3 1) ≤
    1 / 1 * Real.log (6 * ((1 : ℕ) : ℝ)) *
      (3 * ((1 : ℕ) : ℝ) ^ 3 / (3 * ((1 : ℕ) : ℝ) ^ 3 - 1)) :=
  partitionInverseRadius_closedMultiplicity_le (rate := 1) (agreement := 1) (scale := 3)
    (order := 1) (by norm_num) (by norm_num) (by norm_num)

/-- At scale `3`, order `1`, the rounding loss is bounded by `closedMultiplicityLoss`. -/
example : partitionRoundingLoss 1 1 1 (closedMultiplicity 3 1) ≤ closedMultiplicityLoss 3 1 :=
  partitionRoundingLoss_closedMultiplicity_le (by norm_num) (by norm_num) (by norm_num)

/-- At scale `3`, order `1`, the finite ratio is at least the limit times its loss factor. -/
example : (27 / 20 : ℝ) * 1 * (((1 : ℕ) : ℝ) + 1) *
      Real.exp (-(1 / 1 * Real.log (6 * ((1 : ℕ) : ℝ)))) *
      Real.exp (-closedMultiplicityLoss 3 1) ≤
    partitionFiniteRatio 1 1 1 (closedMultiplicity 3 1) :=
  partitionFiniteRatio_closedMultiplicity_ge (rate := 1) (agreement := 1) (scale := 3)
    (order := 1) (by norm_num) (by norm_num) (by norm_num)

/-- At scale `1000` and order `6`, the numerical rounding-loss bound holds. -/
example : closedMultiplicityLoss 1000 6 < 1 / 1000 :=
  closedMultiplicityLoss_thousand_lt (by norm_num)

/-- At scale `300` and order `500`, the numerical rounding-loss bound holds. -/
example : closedMultiplicityLoss 300 500 < 1677 / 1000000 :=
  closedMultiplicityLoss_three_hundred_lt (by norm_num)

/-- At scale `1000` and order `6`, the finite ratio exceeds its limit with margin `1/1000`. -/
example : (27 / 20 : ℝ) * 1 * (6 + 1) * Real.exp (-(1 / 1 * Real.log (6 * (6 : ℝ)))) *
      Real.exp (-(1 / 1000 : ℝ)) <
    partitionFiniteRatio 1 1 6 (closedMultiplicity 1000 6) := by
  apply partitionFiniteRatio_closedMultiplicity_gt (by norm_num) (by norm_num) (by norm_num)
  exact closedMultiplicityLoss_thousand_lt (by norm_num)

/-! ### Finite ratio -/

/-- The inverse radius is `d m / W = 2` at `R = a = 1`, `d = 1`, `m = 2`. -/
example : partitionInverseRadius 1 1 1 2 = 2 := by
  rw [partitionInverseRadius_eq, test_weightBudget]
  norm_num

/-- For `R = a = 1`, `d = 1`, `m = 2`, the finite ratio in terms of `W` uses `W = 1`. -/
example : partitionFiniteRatio 1 1 1 2 =
    (let budget : ℝ := partitionWeightBudget 1 1 1 2
     (27 / 20) * 1 * (1 + 1) *
       Real.exp (-((1 : ℝ) / budget * (2 + (1 + 1) * 1 / 2))) /
         (1 + (1 + 1) * 1 / budget)) := by
  have hmultiplicity : 0 < (2 : ℕ) := by norm_num
  have hbudget : 0 < partitionWeightBudget 1 1 1 2 := by
    rw [test_weightBudget]
    norm_num
  simpa [test_weightBudget] using
    (partitionFiniteRatio_eq_weightBudget (rate := 1) (agreement := 1) (order := 1)
      (multiplicity := 2) hmultiplicity hbudget)

/-! ### Rate-dependent gate -/

/-- `Γ(1, 1, 1) = (27/20) · 2 / 6 = 9/20`. -/
example : 0 < rateGamma 1 1 1 := rateGamma_pos (by norm_num) (by norm_num)

/-- The logarithm identity at `R = 1`, `a = 1`, `d = 1` agrees with `log(9/20)`. -/
example : Real.log (27 * 1 / 20) + Real.log ((1 : ℕ) + 1 : ℝ) -
    1 / 1 * Real.log (6 * ((1 : ℕ) : ℝ)) = Real.log (9 / 20) := by
  have h : rateGamma 1 1 1 = 9 / 20 := by norm_num [rateGamma]
  rw [← log_rateGamma one_ne_zero one_pos, h]

/-- `log(40/9) + log(27/20) = log 6` at `R = 1`. -/
example : Real.log (40 / (9 * 1)) + Real.log (27 * 1 / 20) = Real.log 6 :=
  complementary_rate_logs (by norm_num)

/-- The fixed-rate logarithm identity at `R = 1`, `δ = 1`, `d = 1`. -/
example : (1 + 1) * Real.log (rateGamma 1 (1 + 1) 1) =
    1 * Real.log ((1 : ℕ) : ℝ) - fixedRateCoefficient 1 + 1 * Real.log (27 * 1 / 20) +
      (1 + 1) * Real.log (1 + 1 / ((1 : ℕ) : ℝ)) :=
  fixed_rate_log_identity (rate := 1) (gap := 1) (order := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- The fixed-rate coefficient is positive at rate `1`. -/
example : 0 < fixedRateCoefficient 1 :=
  fixedRateCoefficient_pos (by norm_num) (by norm_num)

/-! ### Weighted-simplex moments -/

/-- On the segment `[0, 1]`, `⨍ (0 - 1 * u₀) ^ 2 = (harmonic 1 ^ 2 + 1) / (2 * 3) = 1 / 3`. -/
example : ⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) 1, (0 - 1 * ∑ i, u i) ^ 2 =
    1 / 3 := by
  rw [setAverage_weightedSimplex_succ_sub_mul_sum_sq 1 one_pos]
  norm_num [harmonic]

/-- The upper-tail bound at dimension `1` is a concrete positive-dimensional case. -/
example : ⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) 1,
    max (((1 : ℕ) : ℝ) * ∑ i, u i - Real.log ((1 : ℕ) : ℝ) - Real.log 6) 0 ^ 2 ≤
      1 / 3 :=
  setAverage_weightedSimplex_succ_upperTail_sq_le 1

/-- The lower-tail bound at `d = 500` and budget `2`. -/
example : (27 / 10 : ℝ) < ⨍ u in weightedSimplex (fun i : Fin 500 ↦ (i : ℝ) + 1) 2,
    max (Real.log (6 * (500 : ℕ)) - (500 : ℕ) * (∑ i, u i) / 2) 0 ^ 2 :=
  setAverage_weightedSimplex_succ_lowerTail_sq_gt le_rfl (by norm_num)

/-! ### Gap-only parameters -/

/-- The multiplicity is at least `3` at the concrete gap `δ = 1`. -/
example : 3 ≤ uniformMultiplicity 1 := by
  have h₁ := uniformDerivativeOrder_pos 1
  have h₂ := add_two_le_uniformMultiplicity 1
  omega

/-- At `δ = 1`, the block threshold gives the multiplicity and total-jet guards. -/
example : 2 * (uniformMultiplicity 1 : ℝ) ≤ (1 : ℝ) ^ 2 * uniformBlockThreshold 1 ∧
    uniformMultiplicity 1 ≤ uniformBlockThreshold 1 ∧ 0 < uniformJetCap 1 ∧
    uniformJetCap 1 < uniformBlockThreshold 1 :=
  uniformBlockThreshold_guards (δ := 1) (n := uniformBlockThreshold 1) (by norm_num)
    (by norm_num) (Nat.le_refl _)

/-- The high-rate guards hold at `δ = 1/2`, `d = 1`, `m = 3`, `n = 24`, `k = 6`, `A = 18`. -/
example : 1 + 1 ≤ 6 ∧ 6 + 1 ≤ 24 := by
  exact high_rate_ambient_guards (δ := 1 / 2) (d := 1) (m := 3) (n := 24) (k := 6) (A := 18)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- For `δ = 1/2`, `d = 1`, `m = 3` and `n = 12`, the low-rate padded guards hold. -/
example : 1 + 1 ≤ ⌊2 * (1 / 2 : ℝ) ^ 2 * 12⌋₊ ∧
    (1 / 2 : ℝ) ^ 2 * 12 ≤ ⌊2 * (1 / 2 : ℝ) ^ 2 * 12⌋₊ ∧
      ⌊2 * (1 / 2 : ℝ) ^ 2 * 12⌋₊ + 1 ≤ 12 := by
  exact low_rate_padded_ambient_guards (δ := 1 / 2) (d := 1) (m := 3) (n := 12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end ReedSolomon.HiddenDerivative.RatePartition
