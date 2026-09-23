/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.Staircase
import ArkLib.Data.Finset.WeightedSimplex.FloorTransfer
import ArkLib.Data.Finset.WeightedSimplex.Moments
import ArkLib.Data.Finset.WeightedSimplex.RankIntegral
import ArkLib.Data.Finset.WeightedSimplex.Variance

/-!
# Acceptance tests for finite staircases and weighted simplices
-/

open Finset
open MeasureTheory
open scoped BigOperators

example : (1, 1) ∈ staircase 2 5 := by
  rw [mem_staircase_of_pos (by decide)]
  decide

example : #(staircase 2 5) = 9 := by
  rw [card_staircase]
  decide

example : Nat.card {p : ℕ × ℕ // p.1 + 2 * p.2 < 5} = 9 := by
  rw [Nat.card_staircasePairs (by decide)]
  decide

example : (fun _ : Fin 1 ↦ 0) ∈
    natWeightedSimplex (fun _ : Fin 1 ↦ 1) 1 := by
  simpa [Nat.floor_zero] using natFloor_mem_natWeightedSimplex
    (w := fun _ : Fin 1 ↦ 1) (W := (1 : ℝ)) (x := fun _ ↦ (0 : ℝ))
    (fun _ ↦ one_ne_zero)
    (Set.mem_weightedSimplex.mpr ⟨fun _ ↦ by norm_num, by norm_num⟩)

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true = 10 := by
  have h := card_add_one_mul_sum_natWeightedSimplex_one_apply (σ := Bool) true 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool] at h
  norm_num [Nat.choose] at h
  omega

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true * c false = 5 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_of_ne
    (show true ≠ false by decide) 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool] at h
  norm_num [Nat.choose] at h
  omega

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true * (c true - 1) = 10 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred true 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool] at h
  norm_num [Nat.choose] at h
  omega

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 2,
    ((c true : ℤ) - (c false : ℤ)) ^ 2 = 10 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_weighted_sq
    (fun b : Bool ↦ if b then (1 : ℤ) else -1) 2
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool, Fintype.sum_bool] at h
  norm_num [Nat.choose] at h
  simp only [← sub_eq_add_neg] at h
  omega

example : 𝔼 c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 2,
    ∑ i, (![1, 1 / 2] : Fin 2 → ℚ) i * (c i : ℚ) = 1 := by
  rw [expect_natWeightedSimplex_one_weighted]
  norm_num [natSimplexWeightedMean, Fin.sum_univ_succ]

example : 𝔼 c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 2,
    (∑ i, (![1, 1 / 2] : Fin 2 → ℚ) i * (c i : ℚ) - 1) ^ 2 = 5 / 12 := by
  have hMean : natSimplexWeightedMean 2 (![1, 1 / 2] : Fin 2 → ℚ) = 1 := by
    norm_num [natSimplexWeightedMean, Fin.sum_univ_succ]
  have h := expect_natWeightedSimplex_one_weighted_sub_sq (![1, 1 / 2] : Fin 2 → ℚ) 2
  rw [hMean] at h
  rw [h]
  norm_num [natSimplexWeightedVariance, Fin.sum_univ_succ]

example : (1 : ℝ) ≤ 19 / 12 := by
  have h := sum_natWeightedSimplex_max_sub_add_one_le (w := fun _ : Fin 1 ↦ 1)
    (fun _ ↦ one_ne_zero) 0 (a := 1) (fun _ ↦ zero_le_one) (T := 0) (by norm_num)
  have hset : natWeightedSimplex (fun _ : Fin 1 ↦ 1) 0 = {fun _ ↦ 0} := by decide
  rw [hset, volume_real_weightedSimplex (fun _ ↦ by norm_num) (by norm_num)] at h
  norm_num at h
  linarith
