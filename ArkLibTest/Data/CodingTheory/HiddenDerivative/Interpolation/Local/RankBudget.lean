/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RankBudget

/-!
# Local rank budget acceptance tests

The linear-geometric and linear-exponential bounds with the ceiling error written as
`(j + 1) / d + 1` are derived from the general bounds at `a = 1 / d` and `b = 1`. At `d = 1`
the exponential envelope reduces to `N_1(W + r) ≤ 1`. The hypotheses of the budget bound are
needed: with `d = 1` or `W = 0` the right side is zero while the budget is one, and the ceiling
lemma fails at `d = 0`.
-/

open Finset ReedSolomon.HiddenDerivative

/-- For `0 ≤ q < 1`, `∑_{j<m} ((j + 1) / d + 1) q^(j+1) ≤ q / (d (1 - q)²) + q / (1 - q)`. -/
example (d m : ℕ) (hd : 0 < d) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ j ∈ range m, (((j + 1 : ℕ) : ℝ) / d + 1) * q ^ (j + 1)) ≤
      q / ((d : ℝ) * (1 - q) ^ 2) + q / (1 - q) := by
  have h := sum_range_linear_mul_pow_succ_le m (a := 1 / (d : ℝ)) (b := 1) (by positivity)
    zero_le_one hq0 hq1
  simp only [div_mul_eq_mul_div, one_mul, div_div] at h
  rwa [mul_comm ((1 - q) ^ 2)] at h

/-- The case `q = exp(-x)`: `∑_{j<m} ((j + 1) / d + 1) exp(-x)^(j+1) ≤ 1 / (d x²) + 1 / x`. -/
example (d m : ℕ) (hd : 0 < d) {x : ℝ} (hx : 0 < x) :
    (∑ j ∈ range m, (((j + 1 : ℕ) : ℝ) / d + 1) * Real.exp (-x) ^ (j + 1)) ≤
      1 / ((d : ℝ) * x ^ 2) + 1 / x := by
  have h := Real.sum_range_linear_mul_exp_neg_pow_succ_le m (a := 1 / (d : ℝ)) (b := 1)
    (by positivity) zero_le_one hx
  simp only [one_div_mul_eq_div, div_div] at h
  exact h

/-- `sum_contactThreshold_mul_exp_le` with the ceiling written out as `(m - r) ⌈/⌉ (d + 1)`. -/
example (d m : ℕ) (hd : 0 < d) {x B : ℝ} (hx : 0 < x) :
    (∑ r ∈ range m, ((m - r) ⌈/⌉ (d + 1) : ℕ) * Real.exp (x * (r + B))) ≤
      Real.exp (x * (m + B)) * (1 / ((d : ℝ) * x ^ 2) + 1 / x) :=
  sum_contactThreshold_mul_exp_le d m hd hx

/-- At `d = 1` there are no higher jets and the envelope gives `N_1(W + r) ≤ 1`. -/
example (W r : ℕ) (hW : 0 < W) : (weightedHigherJetCount 1 (W + r) : ℝ) ≤ 1 := by
  simpa using weightedHigherJetCount_le_exp 1 W r hW

/-- The ceiling lemma needs `0 < d`: at `d = 0`, `j = 2` it would read `2 ≤ 1`. -/
example : ¬ (((2 ⌈/⌉ (0 + 1) : ℕ) : ℝ) ≤ (2 : ℝ) / (0 : ℕ) + 1) := by
  norm_num [Nat.ceilDiv_eq_add_pred_div]

private theorem budget_one (W : ℕ) : localCoordinateBudget 1 1 W 1 = 1 := by
  simp [localCoordinateBudget, contactThreshold, Nat.ceilDiv_eq_add_pred_div,
    weightedHigherJetCount, Finset.natWeightedSimplex]

private theorem budget_two_zero : localCoordinateBudget 2 1 0 1 = 1 := by
  decide

/-- The budget bound needs `2 ≤ d`: at `d = 1` the right side is zero and the budget is one. -/
example (W : ℕ) : ¬ ((localCoordinateBudget 1 1 W 1 : ℝ) ≤
    (1 : ℕ) * ((W : ℝ) ^ (1 - 1) / ((1 - 1).factorial : ℝ) ^ 2) *
      Real.exp ((((1 - 1 : ℕ) : ℝ) / W) * ((1 : ℕ) + (1 : ℕ).choose 2)) *
        (1 / (((1 : ℕ) : ℝ) * (((1 - 1 : ℕ) : ℝ) / W) ^ 2) + 1 / (((1 - 1 : ℕ) : ℝ) / W))) := by
  rw [budget_one]
  norm_num

/-- The budget bound needs `0 < W`: at `W = 0`, `d = 2` the right side is zero and the budget is
one. -/
example : ¬ ((localCoordinateBudget 2 1 0 1 : ℝ) ≤
    (1 : ℕ) * (((0 : ℕ) : ℝ) ^ (2 - 1) / ((2 - 1).factorial : ℝ) ^ 2) *
      Real.exp ((((2 - 1 : ℕ) : ℝ) / (0 : ℕ)) * ((1 : ℕ) + (2 : ℕ).choose 2)) *
        (1 / (((2 : ℕ) : ℝ) * (((2 - 1 : ℕ) : ℝ) / (0 : ℕ)) ^ 2) +
          1 / (((2 - 1 : ℕ) : ℝ) / (0 : ℕ)))) := by
  rw [budget_two_zero]
  norm_num

/-- A concrete instance of the normalized bound at `d = 2`, `m = 1`, `W = 1`, where `κ = 1`,
`V = 1`, and the budget is `B` times the number of `z ≤ 1`, which is `2`. -/
example (Be : ℕ) : (localCoordinateBudget 2 1 1 Be : ℝ) ≤
    Be * Real.exp 2 * (3 / 2) := by
  have h := localCoordinateBudget_div_volume_mul_cube_le 2 1 1 Be le_rfl one_pos one_pos
  norm_num at h
  exact h

/-- The budget in the previous example, with `B = 1`, is `2`, below `exp 2 · 3/2 ≈ 11.1`. -/
example : localCoordinateBudget 2 1 1 1 = 2 := by
  decide
