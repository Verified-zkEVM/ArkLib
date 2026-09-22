/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Endpoints

/-!
# Acceptance cases for the endpoint comparison

The lower bounds specialized to `θ = 3 / 8`, `ξ = 27 / 10`, `δ ≤ 1 / 4` and `δ / 3 ≤ ρ`, derived
from the general ones; the case showing that the hypothesis on `θ` in
`highRate_denominator_sq_le_rate` is needed; the exact high-rate surplus and the fact that each
high-rate term alone falls below `543 / 500`; and the numerical constants `163 / 60 < e` and
`11 / 4 < exp (81 / 80)`.
-/

open ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-! ### The specialized lower bounds -/

/-- `highRate_denominator_sq_le_rate` with `θ = 3 / 8` and `δ ≤ 1 / 4`. -/
example (δ ρ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : δ ≤ ρ) (hρmax : ρ ≤ 1 - δ) :
    (ρ + theta * δ) ^ 2 ≤ ρ :=
  highRate_denominator_sq_le_rate hδ theta_pos.le (by norm_num [theta]; linarith) hρ hρmax

/-- `highRate_baseline_lower` at `θ = 3 / 8`, `ξ = 27 / 10`, with `(δ / ρ) ^ 2 H ^ 2` separated. -/
example (δ ρ H logd : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : δ ≤ ρ) (hρmax : ρ ≤ 1 - δ)
    (hH : xi / δ ≤ H) (hlog : xi / δ ≤ logd) :
    xi ^ 2 * Real.exp (theta * xi) ≤
      ρ * (δ / ρ) ^ 2 * H ^ 2 / (1 + theta * (δ / ρ)) ^ 2 *
        Real.exp (logd * ((theta * (δ / ρ)) / (1 + theta * (δ / ρ)))) := by
  have h := highRate_baseline_lower theta_pos.le xi_pos.le hδ hρ
    (highRate_denominator_sq_le_rate hδ theta_pos.le (by norm_num [theta]; linarith) hρ hρmax)
    hH hlog
  convert h using 2
  simp only [div_pow, mul_pow]
  ring

/-- `highRate_variance_lower` at `θ = 3 / 8`, `ξ = 27 / 10`. -/
example (δ ρ logd : ℝ) (hδ : 0 < δ) (hρ : δ ≤ ρ) (hlog : xi / δ ≤ logd) :
    Real.exp 1 * (theta * xi / (1 + theta)) ≤
      ρ * Real.exp (logd * ((theta * (δ / ρ)) / (1 + theta * (δ / ρ)))) :=
  highRate_variance_lower theta_pos.le xi_pos.le hδ hρ hlog

/-- `lowRate_baseline_lower` with `δ₀ = 1 / 4` and `c = 1 / 3`. -/
example (δ ρ H logd : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ)
    (hH : xi / δ ≤ H) (hlog : xi / δ ≤ logd) :
    (4 * xi ^ 2 / (3 * (1 + theta) ^ 2)) * Real.exp (4 * theta * xi / (1 + theta)) ≤
      ρ * H ^ 2 / (1 + theta) ^ 2 * Real.exp (logd * (theta / (1 + theta))) := by
  have h := lowRate_baseline_lower theta_pos.le xi_pos.le (by norm_num : (0 : ℝ) ≤ 1 / 3) hδ hδmax
    (by linarith : 1 / 3 * δ ≤ ρ) hH hlog
  have ht : (0 : ℝ) < 1 + theta := by have := theta_pos; linarith
  convert h using 2
  · field_simp
  · congr 1
    field_simp
  · rw [div_pow]
    ring

/-- `Real.exp_one_mul_le_mul_exp_div`, with an unused hypothesis `0 < c`. -/
example (c ρ : ℝ) (_hc : 0 < c) (hρ : 0 < ρ) : Real.exp 1 * c ≤ ρ * Real.exp (c / ρ) :=
  Real.exp_one_mul_le_mul_exp_div c hρ

/-- `163 / 60 < e`, from Mathlib's nine-digit bound. -/
example : (163 / 60 : ℝ) < Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  linarith

/-- `11 / 4 < exp (81 / 80)`. -/
example : (11 / 4 : ℝ) < Real.exp (81 / 80) := Real.elevenFourths_lt_exp_eightyOne_div_eighty

/-! ### The high-rate constants -/

/-- The exact high-rate surplus: the two high-rate lower bounds
`F > (729 / 100) (11 / 4)` and `J > (81 / 110) (163 / 60)` together give the exact value
`1862667945 / 1714356224 > 543 / 500`. -/
example : (((5 / 8 : ℝ) ^ 3 * (729 / 100) * (11 / 4) +
      (999 / 1000) * (4147 / 2160) * (81 / 110) * (163 / 60)) /
        (6 * (101 / 100) * (37 / 20) * (448 / 625))) = 1862667945 / 1714356224 ∧
    (543 / 500 : ℝ) < 1862667945 / 1714356224 := by
  norm_num

/-- Each high-rate term alone is not enough: the baseline bound alone gives less than
`543 / 500`, and so does the variance bound alone. -/
example : (5 / 8 : ℝ) ^ 3 * (729 / 100) * (11 / 4) / (6 * (101 / 100) * (37 / 20) * (448 / 625))
      < 543 / 500 ∧
    (999 / 1000 : ℝ) * (4147 / 2160) * (81 / 110) * (163 / 60) /
      (6 * (101 / 100) * (37 / 20) * (448 / 625)) < 543 / 500 := by
  norm_num

/-! ### Necessity of the hypothesis on `θ` -/

/-- The hypothesis `θ ^ 2 δ ≤ (1 - 2 θ) (1 - δ)` is needed in `highRate_denominator_sq_le_rate`:
at `θ = 1 / 2`, `δ = ρ = 1 / 2` the other hypotheses hold, the hypothesis reads `1 / 8 ≤ 0`, and
`(ρ + θ δ) ^ 2 = 9 / 16 > 1 / 2 = ρ`. -/
example : ¬ ((1 / 2 : ℝ) ^ 2 * (1 / 2) ≤ (1 - 2 * (1 / 2)) * (1 - 1 / 2)) ∧
    ¬ (((1 / 2 : ℝ) + 1 / 2 * (1 / 2)) ^ 2 ≤ 1 / 2) := by
  norm_num
