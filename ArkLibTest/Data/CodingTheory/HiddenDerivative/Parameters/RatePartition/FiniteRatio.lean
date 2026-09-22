/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite partition ratio acceptance tests

The weight budget, inverse radius and finite ratio at `R = a = 1`, `d = 1`, `m = 2`; the finite
ratio written with the triangular number `d (d + 1) / 2` divided by `m`; a case showing that
`0 < a` is needed for the limit of `W/m`; and the existence statement without the weight-budget
clause.
-/

open Filter Topology

namespace ReedSolomon.HiddenDerivative.RatePartition

private theorem one_lt_log_six : 1 < Real.log 6 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [Real.exp_one_lt_d9]

private theorem log_six_lt_two : Real.log 6 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9]

/-! ### A concrete parameter set: `R = a = 1`, `d = 1`, `m = 2` -/

/-- The weight budget is `⌊2 / log 6⌋₊ = 1`, since `1 < log 6 < 2`. -/
private theorem test_weightBudget : partitionWeightBudget 1 1 1 2 = 1 := by
  have hlog := one_lt_log_six
  have hlog' := log_six_lt_two
  rw [partitionWeightBudget, Nat.floor_eq_iff (by norm_num; positivity)]
  norm_num
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- The inverse radius is `d m / W = 2`. -/
example : partitionInverseRadius 1 1 1 2 = 2 := by
  rw [partitionInverseRadius_eq, test_weightBudget]
  norm_num

/-- The finite ratio is `(27/20) · 2 · exp(-3) / 3 = (9/10) exp(-3)`. -/
example : partitionFiniteRatio 1 1 1 2 = 9 / 10 * Real.exp (-3) := by
  rw [partitionFiniteRatio_eq_weightBudget (by norm_num) (by rw [test_weightBudget]; norm_num),
    test_weightBudget]
  norm_num
  ring

/-! ### The finite ratio with the triangular number -/

/-- The finite ratio, with `w = W/m`, `λ = d/w` and the triangular number `S = d (d + 1) / 2`, is
`(27/20) R (d + 1) exp(-λ (1 + S/m)) / (1 + (d + 1) λ / m)`. -/
example (rate agreement : ℝ) (order multiplicity : ℕ) :
    (let w := (partitionWeightBudget rate agreement order multiplicity : ℝ) / multiplicity
     let lam := (order : ℝ) / w
     let S := (order : ℝ) * (order + 1) / 2
     (27 / 20) * rate * (order + 1) * Real.exp (-lam * (1 + S / multiplicity)) /
       (1 + (order + 1) * lam / multiplicity)) =
      partitionFiniteRatio rate agreement order multiplicity := by
  simp only [partitionFiniteRatio, partitionInverseRadius, div_div]

/-! ### Boundary hypotheses -/

/-- `tendsto_partitionWeightBudget_div` needs `0 < a`: at `R = 1`, `a = -1`, `d = 1` every weight
budget is `0`, so `W/m` tends to `0`, not to `a d / (R log(6d)) = -1/log 6`. -/
example : ¬ Tendsto (fun multiplicity : ℕ ↦
    (partitionWeightBudget 1 (-1) 1 multiplicity : ℝ) / multiplicity) atTop
      (𝓝 ((-1) * ((1 : ℕ) : ℝ) / (1 * Real.log (6 * ((1 : ℕ) : ℝ))))) := by
  intro h
  have hlog : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hzero : (fun multiplicity : ℕ ↦
      (partitionWeightBudget 1 (-1) 1 multiplicity : ℝ) / multiplicity) = fun _ ↦ 0 := by
    funext multiplicity
    rw [partitionWeightBudget, Nat.floor_of_nonpos]
    · simp
    · norm_num
      rw [neg_div]
      exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) hlog.le)
  rw [hzero] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at this

/-! ### Existence without the weight-budget clause -/

/-- Every value below the limit `(27/20) R (d + 1) exp(-(R/a) log(6d))` is exceeded by the finite
ratio at some positive multiplicity. -/
example {rate agreement γ : ℝ} {order : ℕ} (hrate : 0 < rate) (hagreement : 0 < agreement)
    (horder : 0 < order)
    (hγ : γ < (27 / 20 : ℝ) * rate * (order + 1) *
      Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ))))) :
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      γ < partitionFiniteRatio rate agreement order multiplicity := by
  obtain ⟨m, hm, -, hratio⟩ := exists_partitionFiniteRatio_gt hrate hagreement horder hγ
  exact ⟨m, hm, hratio⟩

/-- When the limit exceeds `1`, a positive multiplicity with positive weight budget and finite
ratio above `1` exists. -/
example {rate agreement : ℝ} {order : ℕ} (hrate : 0 < rate) (hagreement : 0 < agreement)
    (horder : 0 < order)
    (hlimit : 1 < (27 / 20 : ℝ) * rate * (order + 1) *
      Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ))))) :
    ∃ multiplicity : ℕ, 0 < multiplicity ∧
      0 < partitionWeightBudget rate agreement order multiplicity ∧
      1 < partitionFiniteRatio rate agreement order multiplicity := by
  obtain ⟨p⟩ := PartitionFiniteParameters.nonempty hrate hagreement horder hlimit
  exact ⟨p.multiplicity, p.multiplicity_pos, p.weightBudget_pos, p.one_lt_finiteRatio⟩

end ReedSolomon.HiddenDerivative.RatePartition
