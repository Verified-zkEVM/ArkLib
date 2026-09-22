/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.WeightedSimplex.Variance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic

/-!
# Acceptance cases for the weighted mean and variance of the unit-weight simplex

These cases check a finite example with variance `5 / 12` against direct enumeration, the boundary
cases `S = 0` and an empty index type, the necessity of `0 ≤ t` in the tail bounds, and the
upper-tail count over the reals and `Fin r`.
-/

open Finset
open scoped BigOperators

/-- Weights `(1, 1/2)` on `Fin 2` at budget `2` have mean `1` and variance
`5 / 12`, not the continuous value `1 / 6`. The closed form gives the value. -/
example : 𝔼 c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 2,
    (∑ i, (![1, 1 / 2] : Fin 2 → ℚ) i * (c i : ℚ) - 1) ^ 2 = 5 / 12 := by
  have hMean : natSimplexWeightedMean 2 (![1, 1 / 2] : Fin 2 → ℚ) = 1 := by
    norm_num [natSimplexWeightedMean, Fin.sum_univ_succ]
  have h := expect_natWeightedSimplex_one_weighted_sub_sq (![1, 1 / 2] : Fin 2 → ℚ) 2
  rw [hMean] at h
  rw [h]
  norm_num [natSimplexWeightedVariance, Fin.sum_univ_succ]

/-- The same value by direct enumeration of the six simplex points, with the weights doubled to
stay in `ℤ`: the total squared deviation of `2 * c 0 + c 1` from `2` is
`10 = 2 ^ 2 * 6 * 5 / 12`. -/
example :
    ∑ c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 2, (2 * (c 0 : ℤ) + c 1 - 2) ^ 2 = 10 ∧
    (natWeightedSimplex (fun _ : Fin 2 ↦ 1) 2).card = 6 := by
  decide

/-- The mean from the closed form agrees with enumeration: weights `(1, 1/2)` at budget `2` have
mean `1`. -/
example : 𝔼 c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 2,
    ∑ i, (![1, 1 / 2] : Fin 2 → ℚ) i * (c i : ℚ) = 1 := by
  rw [expect_natWeightedSimplex_one_weighted]
  norm_num [natSimplexWeightedMean, Fin.sum_univ_succ]

/-- At budget zero the only point is the origin and the variance vanishes. -/
example (w : Bool → ℚ) : natSimplexWeightedVariance 0 w = 0 := by
  simp [natSimplexWeightedVariance]

/-- With no coordinates the statistic is identically zero; the closed form also gives zero. -/
example (S : ℕ) (w : Fin 0 → ℚ) : natSimplexWeightedVariance S w = 0 := by
  simp [natSimplexWeightedVariance]

/-- Nonnegativity of the variance gives Cauchy–Schwarz for the weights and the slack coordinate. -/
example (w : Fin 3 → ℝ) : (∑ i, w i) ^ 2 ≤ 4 * ∑ i, w i ^ 2 := by
  have h := natSimplexWeightedVariance_nonneg 1 w
  simp only [natSimplexWeightedVariance, Fintype.card_fin] at h
  norm_num at h
  have hpos : (0 : ℝ) < 5 / 80 := by norm_num
  nlinarith

/-- The upper-tail count over the reals and `Fin r`. -/
example (r S : ℕ) (w : Fin r → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * ((natWeightedSimplex (fun _ : Fin r ↦ 1) S).filter fun c ↦
        natSimplexWeightedMean S w + t ≤ ∑ i, w i * (c i : ℝ)).card ≤
      (S + r).choose r * natSimplexWeightedVariance S w := by
  have h := sq_mul_card_filter_mean_add_le_le_card_mul_variance w S ht
  rwa [card_natWeightedSimplex_one, Fintype.card_fin] at h

/-- The hypothesis `0 ≤ t` is necessary: at `S = 0` the variance is zero, but with `t = -1` the
single point lies in both tails. -/
example : ¬ ((-1 : ℚ) ^ 2 * ((natWeightedSimplex (fun _ : Fin 1 ↦ 1) 0).filter fun c ↦
        natSimplexWeightedMean 0 (fun _ : Fin 1 ↦ (1 : ℚ)) + -1 ≤
          ∑ i, (fun _ : Fin 1 ↦ (1 : ℚ)) i * (c i : ℚ)).card ≤
      (natWeightedSimplex (fun _ : Fin 1 ↦ 1) 0).card *
        natSimplexWeightedVariance 0 (fun _ : Fin 1 ↦ (1 : ℚ))) := by
  rw [filter_true_of_mem fun c _ ↦ by
    simp only [natSimplexWeightedMean, Nat.cast_zero, zero_div, zero_mul, zero_add, one_mul]
    exact le_trans (by norm_num) (sum_nonneg fun i _ ↦ Nat.cast_nonneg (c i))]
  simp [natSimplexWeightedVariance, card_natWeightedSimplex_one]

example : ¬ ((-1 : ℚ) ^ 2 * ((natWeightedSimplex (fun _ : Fin 1 ↦ 1) 0).filter fun c ↦
        -1 ≤ |∑ i, (fun _ : Fin 1 ↦ (1 : ℚ)) i * (c i : ℚ) -
          natSimplexWeightedMean 0 (fun _ : Fin 1 ↦ (1 : ℚ))|).card ≤
      (natWeightedSimplex (fun _ : Fin 1 ↦ 1) 0).card *
        natSimplexWeightedVariance 0 (fun _ : Fin 1 ↦ (1 : ℚ))) := by
  rw [filter_true_of_mem fun c _ ↦ le_trans (by norm_num) (abs_nonneg _)]
  simp [natSimplexWeightedVariance, card_natWeightedSimplex_one]

/-- Chebyshev on `Bool` at budget `2` with weights `(1, -1)`: the mean is `0` and the variance is
`2 * 5 / (9 * 4) * (3 * 2 - 0) = 5 / 3`, so `4 * k ≤ 6 * (5 / 3) = 10` for the number `k` of points
that deviate by at least `2`. Hence `k ≤ 2`, which is attained by `(2, 0)` and `(0, 2)`. -/
example : ((natWeightedSimplex (fun _ : Bool ↦ 1) 2).filter fun c ↦
    (2 : ℚ) ≤ |∑ b, (fun b : Bool ↦ if b then (1 : ℚ) else -1) b * (c b : ℚ) -
      natSimplexWeightedMean 2 (fun b : Bool ↦ if b then (1 : ℚ) else -1)|).card ≤ 2 := by
  have h := sq_mul_card_filter_le_abs_sub_le_card_mul_variance
    (fun b : Bool ↦ if b then (1 : ℚ) else -1) 2 (t := 2) (by norm_num)
  rw [card_natWeightedSimplex_one] at h
  norm_num [natSimplexWeightedVariance, Nat.choose] at h
  have h' : 4 * ((natWeightedSimplex (fun _ : Bool ↦ 1) 2).filter fun c ↦
      (2 : ℚ) ≤ |∑ b, (fun b : Bool ↦ if b then (1 : ℚ) else -1) b * (c b : ℚ) -
        natSimplexWeightedMean 2 (fun b : Bool ↦ if b then (1 : ℚ) else -1)|).card ≤ 10 := by
    simp only [Fintype.sum_bool]
    exact_mod_cast h
  omega
