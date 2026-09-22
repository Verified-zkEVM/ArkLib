/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.ClosedMultiplicity

/-!
# Closed-form multiplicity acceptance tests

The rounding loss at `R = a = 1`, `d = 1`, `m = 2`; cases showing that the scale and order
hypotheses of `add_two_le_closedMultiplicity` and the order thresholds of the two numerical loss
bounds are needed; and, for `R < a`, the floor bounds `λ ≤ (3/2) log(6d)` and
`λ - (R/a) log(6d) ≤ 2 log(6d) / (1000 d³)` at scale `1000`, and the ratio bounds with margins
`exp(-1/1000)` for `d ≥ 500` and `exp(-1677/10⁶)` for `d ≥ 519`.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

private theorem one_lt_log_six : 1 < Real.log 6 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [Real.exp_one_lt_d9]

private theorem log_six_lt_two : Real.log 6 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9]

/-! ### A concrete rounding loss: `R = a = 1`, `d = 1`, `m = 2` -/

private theorem test_weightBudget : partitionWeightBudget 1 1 1 2 = 1 := by
  have hlog := one_lt_log_six
  have hlog' := log_six_lt_two
  rw [partitionWeightBudget, Nat.floor_eq_iff (by norm_num; positivity)]
  norm_num
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- With `W = 1` the inverse radius is `λ = 2`, and the loss is
`(2 - log 6) + 2 · (1 · 2 / 4) + log(1 + 2 · 2 / 2) = 3 - log 6 + log 3`. -/
example : partitionRoundingLoss 1 1 1 2 = 3 - Real.log 6 + Real.log 3 := by
  have hlambda : partitionInverseRadius 1 1 1 2 = 2 := by
    rw [partitionInverseRadius_eq, test_weightBudget]
    norm_num
  simp only [partitionRoundingLoss, hlambda]
  norm_num
  ring

/-! ### Boundary hypotheses -/

/-- `add_two_le_closedMultiplicity` needs `3 ≤ C`: at `C = 1`, `d = 1` the multiplicity is
`⌈log 6⌉₊ = 2 < d + 2`. -/
example : closedMultiplicity 1 1 = 2 := by
  have hlog := one_lt_log_six
  have hlog' := log_six_lt_two
  rw [closedMultiplicity, Nat.ceil_eq_iff (by norm_num)]
  norm_num
  exact ⟨hlog, hlog'.le⟩

/-- `add_two_le_closedMultiplicity` needs `1 ≤ d`: at `d = 0` the multiplicity is `0`. -/
example : closedMultiplicity 1000 0 = 0 := by
  simp [closedMultiplicity]

/-- `closedMultiplicityLoss_thousand_lt` needs an order threshold: at `d = 3` the loss bound
`(log 18 + 30) / 26999` exceeds `1/1000`. -/
example : 1 / 1000 < closedMultiplicityLoss 1000 3 := by
  have hlog : 0 ≤ Real.log (6 * ((3 : ℕ) : ℝ)) := Real.log_nonneg (by norm_num)
  rw [closedMultiplicityLoss, lt_div_iff₀ (by norm_num)]
  norm_num at hlog ⊢
  linarith

/-- `closedMultiplicityLoss_three_hundred_lt` needs an order threshold: at `d = 400` the loss
bound exceeds `1677/10⁶`. -/
example : 1677 / 1000000 < closedMultiplicityLoss 300 400 := by
  have hlog : 0 ≤ Real.log (6 * ((400 : ℕ) : ℝ)) := Real.log_nonneg (by norm_num)
  rw [closedMultiplicityLoss, lt_div_iff₀ (by norm_num)]
  norm_num at hlog ⊢
  linarith

/-! ### Floor and ratio bounds under `R < a` -/

private theorem one_lt_scale_mul_cube {scale : ℝ} {order : ℕ} (hscale : 1 < scale)
    (horder : 1 ≤ order) : 1 < scale * (order : ℝ) ^ 3 := by
  have h : (1 : ℝ) ≤ (order : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast horder)
  nlinarith

/-- For `0 < R < a` and `d ≥ 500`, at `m = ⌈1000 d² log(6d)⌉₊` and `W` its weight budget, with
`L = log(6d)`: `0 < m`, `0 < W`, `d m / W ≤ (3/2) L` and `d m / W - R L / a ≤ 2 L / (1000 d³)`. -/
example {rate agreement : ℝ} {order : ℕ} (hrate : 0 < rate) (hlt : rate < agreement)
    (horder : 500 ≤ order) :
    0 < closedMultiplicity 1000 order ∧
      0 < partitionWeightBudget rate agreement order (closedMultiplicity 1000 order) ∧
      (order : ℝ) * closedMultiplicity 1000 order /
          partitionWeightBudget rate agreement order (closedMultiplicity 1000 order) ≤
        (3 / 2) * Real.log (6 * order) ∧
      (order : ℝ) * closedMultiplicity 1000 order /
            partitionWeightBudget rate agreement order (closedMultiplicity 1000 order) -
          rate * Real.log (6 * order) / agreement ≤
        2 * Real.log (6 * order) / (1000 * (order : ℝ) ^ 3) := by
  have hscale := one_lt_scale_mul_cube (scale := 1000) (by norm_num) (by omega : 1 ≤ order)
  have hd : (500 : ℝ) ≤ order := by exact_mod_cast horder
  have hagreement : 0 < agreement := hrate.trans hlt
  have hlambda := partitionInverseRadius_closedMultiplicity_le hrate hlt.le hscale
  rw [partitionInverseRadius_eq] at hlambda
  set L := Real.log (6 * (order : ℝ))
  set K := 1000 * (order : ℝ) ^ 3
  set lambda := (order : ℝ) * closedMultiplicity 1000 order /
    partitionWeightBudget rate agreement order (closedMultiplicity 1000 order)
  have hL : 0 < L := Real.log_pos (by linarith)
  have hK : 3 ≤ K := by
    have : (1 : ℝ) ≤ (order : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hlambda₀ : 0 ≤ rate / agreement * L := by positivity
  have hlambda₀L : rate / agreement * L ≤ L := by
    have : rate / agreement ≤ 1 := (div_le_one hagreement).mpr hlt.le
    nlinarith
  have hfactor : K / (K - 1) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine ⟨?_, partitionWeightBudget_closedMultiplicity_pos hrate hlt.le hscale, ?_, ?_⟩
  · have := add_two_le_closedMultiplicity (scale := 1000) (by norm_num) (by omega : 1 ≤ order)
    omega
  · calc lambda ≤ rate / agreement * L * (K / (K - 1)) := hlambda
      _ ≤ L * (3 / 2) := mul_le_mul hlambda₀L hfactor (by positivity) hL.le
      _ = 3 / 2 * L := by ring
  · have hexcess : rate / agreement * L * (K / (K - 1)) - rate / agreement * L =
        rate / agreement * L / (K - 1) := by
      have hK1 : K - 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp
      ring
    have hshift : L / (K - 1) ≤ 2 * L / K := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hdrop : rate / agreement * L / (K - 1) ≤ L / (K - 1) :=
      div_le_div_of_nonneg_right hlambda₀L (by linarith)
    rw [show rate * L / agreement = rate / agreement * L by ring]
    linarith

/-- For `0 < R < a` and `d ≥ 500`, the finite ratio at `m = ⌈1000 d² log(6d)⌉₊` exceeds
`(27/20) R (d + 1) exp(-(R/a) log(6d)) exp(-1/1000)`. -/
example {rate agreement : ℝ} {order : ℕ} (hrate : 0 < rate) (hlt : rate < agreement)
    (horder : 500 ≤ order) :
    (27 / 20 : ℝ) * rate * (order + 1) *
          Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) *
        Real.exp (-(1 / 1000 : ℝ)) <
      partitionFiniteRatio rate agreement order (closedMultiplicity 1000 order) :=
  partitionFiniteRatio_closedMultiplicity_gt hrate hlt.le
    (one_lt_scale_mul_cube (by norm_num) (by omega))
    (closedMultiplicityLoss_thousand_lt (by omega))

/-- For `0 < R < a` and `d ≥ 519`, the finite ratio at `m = ⌈300 d² log(6d)⌉₊` exceeds
`(27/20) R (d + 1) exp(-(R/a) log(6d)) exp(-1677/10⁶)`. -/
example {rate agreement : ℝ} {order : ℕ} (hrate : 0 < rate) (hlt : rate < agreement)
    (horder : 519 ≤ order) :
    (27 / 20 : ℝ) * rate * (order + 1) *
          Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) *
        Real.exp (-(1677 / 1000000 : ℝ)) <
      partitionFiniteRatio rate agreement order (closedMultiplicity 300 order) :=
  partitionFiniteRatio_closedMultiplicity_gt hrate hlt.le
    (one_lt_scale_mul_cube (by norm_num) (by omega))
    (closedMultiplicityLoss_three_hundred_lt (by omega))

end ReedSolomon.HiddenDerivative.RatePartition
