/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Moment

/-!
# Acceptance cases for the squared tails of the weighted coordinate sum

The quadratic moment in one dimension, the upper-tail bound with no coordinates, the lower-tail
bound at `d = 500` and the necessity of `0 < W`, and the forms over the standard simplex in terms
of its largest coordinate, derived through the law of the largest coordinate.
-/

open MeasureTheory Set Finset ReedSolomon.HiddenDerivative.RatePartition

/-- On the segment `[0, 1]`, `⨍ (0 - 1 * u₀) ^ 2 = (harmonic 1 ^ 2 + 1) / (2 * 3) = 1 / 3`. -/
example : ⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) 1, (0 - 1 * ∑ i, u i) ^ 2 =
    1 / 3 := by
  rw [setAverage_weightedSimplex_succ_sub_mul_sum_sq 1 one_pos]
  norm_num [harmonic]

/-- With no coordinates the upper-tail integrand is `max (-log 6) 0 ^ 2 = 0`, and the bound holds
with no hypothesis on `d`. -/
example : ⨍ u in weightedSimplex (fun i : Fin 0 ↦ (i : ℝ) + 1) 1,
    max (((0 : ℕ) : ℝ) * ∑ i, u i - Real.log ((0 : ℕ) : ℝ) - Real.log 6) 0 ^ 2 ≤ 1 / 3 :=
  setAverage_weightedSimplex_succ_upperTail_sq_le 0

/-- The lower-tail bound at `d = 500` and budget `2`. -/
example : (27 / 10 : ℝ) < ⨍ u in weightedSimplex (fun i : Fin 500 ↦ (i : ℝ) + 1) 2,
    max (Real.log (6 * (500 : ℕ)) - (500 : ℕ) * (∑ i, u i) / 2) 0 ^ 2 :=
  setAverage_weightedSimplex_succ_lowerTail_sq_gt le_rfl (by norm_num)

/-- `0 < W` is needed in `setAverage_weightedSimplex_succ_lowerTail_sq_gt`: at `W = 0` the
weighted simplex is the null set `{0}`, so every average over it is `0`. -/
example : ¬ (27 / 10 : ℝ) < ⨍ u in weightedSimplex (fun i : Fin 500 ↦ (i : ℝ) + 1) 0,
    max (Real.log (6 * (500 : ℕ)) - (500 : ℕ) * (∑ i, u i) / 0) 0 ^ 2 := by
  rw [setAverage_eq, volume_real_weightedSimplex_succ 500 le_rfl]
  norm_num

/-- The upper-tail bound over the standard simplex, in terms of its largest coordinate: for
nonzero `d`, `⨍ x in standardSimplex (Fin d) 1, max (d * maxᵢ x i - log d - log 6) 0 ^ 2`
is at most `1 / 3`. -/
example {d : ℕ} [NeZero d] :
    ⨍ x in standardSimplex (Fin d) 1,
      max (d * Finset.univ.sup' Finset.univ_nonempty x - Real.log d - Real.log 6) 0 ^ 2 ≤
        1 / 3 := by
  have hlaw := setAverage_standardSimplex_comp_sup' (n := d) 1
    fun m ↦ max (d * m - Real.log d - Real.log 6) 0 ^ 2
  beta_reduce at hlaw
  rw [hlaw]
  exact setAverage_weightedSimplex_succ_upperTail_sq_le d

/-- The lower-tail bound over the standard simplex, in terms of its largest coordinate: for
`500 ≤ d`, `27 / 10 < ⨍ x in standardSimplex (Fin d) 1, max (log 6 - (d * maxᵢ x i - log d)) 0 ^ 2`.
-/
example {d : ℕ} [NeZero d] (hd : 500 ≤ d) :
    (27 / 10 : ℝ) < ⨍ x in standardSimplex (Fin d) 1,
      max (Real.log 6 - (d * Finset.univ.sup' Finset.univ_nonempty x - Real.log d)) 0 ^ 2 := by
  have hlaw := setAverage_standardSimplex_comp_sup' (n := d) 1
    fun m ↦ max (Real.log 6 - (d * m - Real.log d)) 0 ^ 2
  beta_reduce at hlaw
  rw [hlaw]
  have h := setAverage_weightedSimplex_succ_lowerTail_sq_gt hd one_pos
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hfun : (fun u : Fin d → ℝ ↦ max (Real.log (6 * d) - d * (∑ i, u i) / 1) 0 ^ 2) =
      fun u ↦ max (Real.log 6 - (d * ∑ i, u i - Real.log d)) 0 ^ 2 := by
    funext u
    rw [Real.log_mul (by norm_num) hd0, div_one]
    congr 2
    ring
  rw [hfun] at h
  exact h
