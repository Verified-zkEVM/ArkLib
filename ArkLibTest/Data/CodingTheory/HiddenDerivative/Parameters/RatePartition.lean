/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.BlockLength
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.ClosedMultiplicity
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FixedRateGate
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Gate
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Moment
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Recipe
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformGamma
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformParameters
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rate-partition parameter acceptance tests

Concrete checks for the block-length guards, multiplicity rounding bounds, finite-ratio limits,
rate gate, simplex moments and gap-only ambient guards.
-/

open MeasureTheory Set Finset Filter Topology

namespace ReedSolomon.HiddenDerivative.RatePartition

private theorem fixedRateGateInputs :
    fixedRateCoefficient 1 ≤ Real.log 5 ∧ 0 < 0 + 1 * Real.log (27 * 1 / 20) := by
  constructor
  · rw [fixedRateCoefficient]
    norm_num only [one_mul, mul_one, mul_zero, add_zero]
    apply Real.log_le_log <;> norm_num
  · norm_num only [zero_add, one_mul]
    exact Real.log_pos (by norm_num)

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

/-- At scale `1000` and order `6`, the finite ratio exceeds its limit with margin `1/1000`. -/
example : (27 / 20 : ℝ) * 1 * (6 + 1) * Real.exp (-(1 / 1 * Real.log (6 * (6 : ℝ)))) *
      Real.exp (-(1 / 1000 : ℝ)) <
    partitionFiniteRatio 1 1 6 (closedMultiplicity 1000 6) := by
  apply partitionFiniteRatio_closedMultiplicity_gt (by norm_num) (by norm_num) (by norm_num)
  exact closedMultiplicityLoss_thousand_lt (by norm_num)

/-! ### Finite ratio -/

/-- At rate and agreement `1`, the finite ratio tends to `9/20`. -/
example : Tendsto (partitionFiniteRatio 1 1 1) atTop (𝓝 (9 / 20 : ℝ)) := by
  convert tendsto_partitionFiniteRatio (rate := 1) (agreement := 1) (order := 1)
    (by norm_num) (by norm_num) (by norm_num) using 1
  rw [show (1 : ℝ) / 1 * Real.log (6 * ((1 : ℕ) : ℝ)) = Real.log 6 by norm_num]
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 6)]
  norm_num

/-- At rate and agreement `1`, the limit `9/20` exceeds `2/5`, so a finite ratio does too. -/
example : ∃ multiplicity : ℕ, 0 < multiplicity ∧
    0 < partitionWeightBudget 1 1 1 multiplicity ∧
    2 / 5 < partitionFiniteRatio 1 1 1 multiplicity := by
  apply exists_partitionFiniteRatio_gt (rate := 1) (agreement := 1) (order := 1)
    (γ := 2 / 5) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / 1 * Real.log (6 * ((1 : ℕ) : ℝ)) = Real.log 6 by norm_num]
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 6)]
  norm_num

/-! ### Rate-dependent gate -/

/-- The selected order and multiplicity at rate `1/2` and gap `1/4` give finite parameters. -/
example : 500 ≤ fixedRatePartitionOrder (1 / 2) (1 / 4) ∧
    1 < rateGamma (1 / 2) (1 / 2 + 1 / 4) (fixedRatePartitionOrder (1 / 2) (1 / 4)) ∧
    0 < fixedRatePartitionMultiplicity (rate := 1 / 2) (gap := 1 / 4)
      (by norm_num) (by norm_num) ∧
    0 < partitionWeightBudget (1 / 2) (1 / 2 + 1 / 4) (fixedRatePartitionOrder (1 / 2) (1 / 4))
      (fixedRatePartitionMultiplicity (rate := 1 / 2) (gap := 1 / 4)
        (by norm_num) (by norm_num)) ∧
    1 < partitionFiniteRatio (1 / 2) (1 / 2 + 1 / 4) (fixedRatePartitionOrder (1 / 2) (1 / 4))
      (fixedRatePartitionMultiplicity (rate := 1 / 2) (gap := 1 / 4)
        (by norm_num) (by norm_num)) ∧
    Nonempty (PartitionFiniteParameters (1 / 2) (1 / 2 + 1 / 4)
      (fixedRatePartitionOrder (1 / 2) (1 / 4))) := by
  obtain ⟨hm, hbudget, hratio⟩ := fixedRatePartitionMultiplicity_spec (rate := 1 / 2)
    (gap := 1 / 4) (by norm_num) (by norm_num)
  exact ⟨fixedRatePartitionOrder_ge_500 (rate := 1 / 2) (gap := 1 / 4),
    fixedRateGamma_gt_one (by norm_num) (by norm_num), hm, hbudget, hratio,
    exists_fixedRatePartitionFiniteParameters (rate := 1 / 2) (gap := 1 / 4)
      (by norm_num) (by norm_num)⟩

/-- At rate `1`, gap `1` and order `5`, the positive exponent margin supplies finite parameters.
-/
example : 1 < rateGamma (1 : ℝ) (1 + 1) 5 ∧
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      0 < partitionWeightBudget 1 2 5 multiplicity ∧
      1 < partitionFiniteRatio 1 2 5 multiplicity := by
  obtain ⟨hcoef, hmargin⟩ := fixedRateGateInputs
  have hlogMargin : 0 < (1 + 1) * Real.log (27 * 1 / 20) + 1 * Real.log 5 - 1 * Real.log 6 := by
    rw [fixedRateCoefficient_eq (rate := 1) (by norm_num)] at hcoef
    nlinarith
  have hlogGate := rateGamma_gt_one_of_log_bound (rate := 1) (gap := 1) (order := 5)
    (by norm_num) (by norm_num) (by norm_num) hlogMargin
  have horderBound : fixedRateCoefficient 1 + 0 ≤ 1 * Real.log 5 := by
    simpa only [add_zero, one_mul] using hcoef
  have hgate' : 1 < rateGamma 1 (1 + 1) 5 := by
    apply rateGamma_gt_one_of_exponent_margin (rate := 1) (gap := 1) (epsilon := 0)
      (order := 5) (by norm_num) (by norm_num) (by norm_num) horderBound hmargin
  have hmarginGate : 1 < rateGamma 1 2 5 := by
    simpa only [show (1 + 1 : ℝ) = 2 by norm_num] using hgate'
  exact ⟨by simpa only [show (1 + 1 : ℝ) = 2 by norm_num] using hlogGate,
    exists_partitionFiniteParameters_of_rateGamma_gt_one (rate := 1) (agreement := 2)
      (order := 5) (by norm_num) (by norm_num) (by norm_num) hmarginGate⟩

/-- Every sufficiently small positive gap at rate `1/2` has a concrete exponential order gate. -/
example : ∃ gapBound : ℝ, 0 < gapBound ∧ ∀ gap : ℝ, 0 < gap → gap < gapBound →
    let order := ⌈Real.exp ((fixedRateCoefficient (1 / 2) + 1) / gap)⌉₊
    (1 / 2 : ℝ) + gap < 1 ∧ 500 ≤ order ∧ 1 < rateGamma (1 / 2) ((1 / 2) + gap) order :=
  exists_small_gap_rate_gate (rate := 1 / 2) (epsilon := 1) (by norm_num) (by norm_num)
    (by norm_num)

/-! ### Uniform rate-gamma margins -/

/-- The uniform order at gap `1/5` gives the low- and high-rate base bounds and margins. -/
example :
    500 ≤ uniformDerivativeOrder (1 / 5 : ℝ) ∧
    Real.exp (3 / 2 - Real.log (40 / 9 : ℝ)) <
      rateGamma (2 * (1 / 5 : ℝ) ^ 2) (1 / 5) (uniformDerivativeOrder (1 / 5)) ∧
    Real.exp (3 / 2 - Real.log (40 / 9 : ℝ)) <
      rateGamma (1 / 2) (1 / 2 + 1 / 5) (uniformDerivativeOrder (1 / 5)) ∧
    (151 / 150 : ℝ) <
      rateGamma (2 * (1 / 5 : ℝ) ^ 2) (1 / 5) (uniformDerivativeOrder (1 / 5)) *
        Real.exp (-1 / 1000) ∧
    (151 / 150 : ℝ) <
      rateGamma (1 / 2) (1 / 2 + 1 / 5) (uniformDerivativeOrder (1 / 5)) *
        Real.exp (-1 / 1000) := by
  exact ⟨uniformDerivativeOrder_ge_500 (by norm_num) (by norm_num),
    uniformRateGamma_low_base_gt (by norm_num) (by norm_num),
    uniformRateGamma_high_base_gt (R := 1 / 2) (δ := 1 / 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    uniformRateGamma_low_gt (by norm_num) (by norm_num),
    uniformRateGamma_high_gt (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

private theorem recipe_rate_gate : 1 < rateGamma 1 2 20 := by
  have hlog : Real.log 5 ≤ Real.log 20 := Real.log_le_log (by norm_num) (by norm_num)
  have hcoef : fixedRateCoefficient 1 ≤ Real.log 20 := fixedRateGateInputs.1.trans hlog
  have horder : fixedRateCoefficient 1 + 0 ≤ 1 * Real.log (20 : ℝ) := by
    nlinarith [hcoef]
  have hmargin := fixedRateGateInputs.2
  have h := rateGamma_gt_one_of_exponent_margin (rate := 1) (gap := 1) (epsilon := 0)
    (order := 20) (by norm_num) (by norm_num) (by norm_num) horder hmargin
  norm_num at h ⊢
  exact h

private theorem candidateWeightBudget :
    800000 ≤ partitionWeightBudget 1 2 20 100000 := by
  have hlog : Real.log 120 < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have hexp5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have hexp : (27 / 10 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      norm_num at this ⊢
      linarith
    calc
      (120 : ℝ) < (27 / 10 : ℝ) ^ 5 := by norm_num
      _ < Real.exp 1 ^ 5 := by gcongr
      _ = Real.exp 5 := by rw [← hexp5]
  unfold partitionWeightBudget
  norm_num only [Nat.cast_ofNat]
  apply Nat.le_floor
  apply (le_div_iff₀ (show (0 : ℝ) < 1 * Real.log 120 by positivity)).2
  have hscaled : (800000 : ℝ) * Real.log 120 < 4000000 := by nlinarith [hlog]
  norm_num only [one_mul] at hscaled ⊢
  linarith

private theorem candidateFiniteRatio : 1 < partitionFiniteRatio 1 2 20 100000 := by
  have hbudget := candidateWeightBudget
  have hbudget_pos : 0 < partitionWeightBudget 1 2 20 100000 :=
    lt_of_lt_of_le (by norm_num) hbudget
  have hbudget_real : (800000 : ℝ) ≤ partitionWeightBudget 1 2 20 100000 := by
    exact_mod_cast hbudget
  have hlambda : partitionInverseRadius 1 2 20 100000 ≤ 5 / 2 := by
    rw [partitionInverseRadius_eq]
    apply (div_le_iff₀ (show (0 : ℝ) <
      (partitionWeightBudget 1 2 20 100000 : ℝ) by exact_mod_cast hbudget_pos)).mpr
    norm_num
    nlinarith
  let lambda := partitionInverseRadius 1 2 20 100000
  have hexponent : lambda * (1 + 20 * 21 / (2 * 100000)) < 3 := by
    have hfactor : (1 : ℝ) + 20 * 21 / (2 * 100000) = 10021 / 10000 := by norm_num
    rw [hfactor]
    dsimp only [lambda] at hlambda ⊢
    nlinarith
  have hexp3 : Real.exp 3 < 27 := by
    rw [show Real.exp 3 = Real.exp 1 ^ 3 by rw [← Real.exp_nat_mul]; norm_num]
    calc
      Real.exp 1 ^ 3 < 3 ^ 3 := by gcongr; exact Real.exp_one_lt_three
      _ = 27 := by norm_num
  have hexp := (Real.exp_lt_exp.mpr hexponent).trans hexp3
  have hnegative : 1 / 27 < Real.exp (-(lambda * (1 + 20 * 21 / (2 * 100000)))) := by
    rw [Real.exp_neg]
    have h := (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 27) (Real.exp_pos _)).2 hexp
    simpa only [one_div] using h
  have hnumerator : 1001 / 1000 <
      (27 / 20 : ℝ) * 21 * Real.exp (-(lambda * (1 + 20 * 21 / (2 * 100000)))) := by
    calc
      (1001 / 1000 : ℝ) < (27 / 20) * 21 * (1 / 27) := by norm_num
      _ < _ := by gcongr
  have hlambda_nonneg : 0 ≤ lambda := by
    dsimp only [lambda]
    exact partitionInverseRadius_nonneg 1 2 20 100000
  have hdenominator : 1 + 21 * lambda / 100000 < 1001 / 1000 := by
    dsimp only [lambda] at hlambda ⊢
    norm_num
    nlinarith
  have hdenominator_pos : 0 < 1 + 21 * lambda / 100000 := by positivity
  have hdenominator_pos' : 0 < 1 + (20 + 1) * lambda / 100000 := by
    simpa only [show (20 : ℝ) + 1 = 21 by norm_num] using hdenominator_pos
  have hratio : 1 < ((27 / 20 : ℝ) * (20 + 1) *
      Real.exp (-(lambda * (1 + (20 : ℝ) * (20 + 1) / (2 * 100000)))) /
      (1 + (20 + 1) * lambda / 100000)) := by
    apply (lt_div_iff₀ hdenominator_pos').2
    linarith
  simpa [partitionFiniteRatio, lambda, Nat.cast_add] using hratio

/-- The selected recipe multiplicity passes its checks and is no larger than `100000`. -/
example :
    let multiplicity := rateMultiplicity (by norm_num) (by norm_num) (by norm_num) recipe_rate_gate
    0 < multiplicity ∧ 0 < partitionWeightBudget 1 2 20 multiplicity ∧
      1 < partitionFiniteRatio 1 2 20 multiplicity ∧ multiplicity ≤ 100000 := by
  have hspec := rateMultiplicity_spec (by norm_num) (by norm_num) (by norm_num) recipe_rate_gate
  refine ⟨hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  apply rateMultiplicity_minimal (by norm_num) (by norm_num) (by norm_num) recipe_rate_gate
  exact ⟨by norm_num, lt_of_lt_of_le (by norm_num) candidateWeightBudget,
    candidateFiniteRatio⟩

/-! ### Weighted-simplex moments -/

/-- On the segment `[0, 1]`, `⨍ (0 - 1 * u₀) ^ 2 = (harmonic 1 ^ 2 + 1) / (2 * 3) = 1 / 3`. -/
example : ⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) 1, (0 - 1 * ∑ i, u i) ^ 2 =
    1 / 3 := by
  rw [setAverage_weightedSimplex_succ_sub_mul_sum_sq 1 one_pos]
  norm_num [harmonic]

/-- The upper-tail bound at dimension `3` has nonzero values near a simplex vertex. -/
example : ⨍ u in weightedSimplex (fun i : Fin 3 ↦ (i : ℝ) + 1) 1,
    max ((3 : ℝ) * ∑ i, u i - Real.log 3 - Real.log 6) 0 ^ 2 ≤
      1 / 3 :=
  setAverage_weightedSimplex_succ_upperTail_sq_le 3

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
