/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Combinatorics.QuadraticStaircase
import ArkLib.Data.Finset.Staircase

/-!
# Acceptance cases for the quadratic real-cutoff staircase

A nonintegral cutoff evaluated by hand, the agreement with the natural-number staircase at an
integral cutoff, the slot count, the lower bound at those cutoffs, a nonpositive cutoff, and the
necessity of `0 ≤ L` in `square_div_two_le_sum`.
-/

open QuadraticStaircase

/-- At `D = 2` and `L = 3 / 2`: `u = 0` leaves `⌈3⌉₊ = 3` values and `u = 1` leaves `⌈1⌉₊ = 1`,
so the count is `4`. The lower bound `2 * (3 / 2) ^ 2 / 2 = 9 / 4` holds. -/
example : count 2 (3 / 2) = 4 := by
  have h1 : ⌈(3 / 2 : ℝ)⌉₊ = 2 := by norm_num [Nat.ceil_eq_iff]
  have h2 : ⌈((2 : ℕ) : ℝ) * (3 / 2 - ((0 : ℕ) : ℝ))⌉₊ = 3 := by norm_num
  have h3 : ⌈((2 : ℕ) : ℝ) * (3 / 2 - ((1 : ℕ) : ℝ))⌉₊ = 1 := by norm_num
  simp only [count, h1, Finset.sum_range_succ, Finset.sum_range_zero, h2, h3]

example : (9 / 4 : ℝ) ≤ count 2 (3 / 2) := by
  have h := count_ge_quadratic 2 (3 / 2)
  norm_num at h
  exact h

/-- At an integral cutoff the count agrees with the natural-number staircase: pairs `(x, u)` with
`x + 2 * u < 2 * 3` number `6 + 4 + 2 = 12` in both formulations. -/
example : count 2 3 = 12 ∧ Nat.staircaseCount 2 (2 * 3) = 12 := by
  refine ⟨?_, by decide⟩
  have h1 : ⌈(3 : ℝ)⌉₊ = 3 := by exact_mod_cast Nat.ceil_natCast 3
  simp only [count, h1, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- The slot type has `count D L` elements; at `D = 1`, `L = 2` these are the pairs
`(0, 0), (1, 0), (0, 1)`. -/
example : Fintype.card (Slot 1 2) = 3 := by
  rw [card_slot]
  have h1 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  simp only [count, h1, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- A nonpositive cutoff gives the empty count, matching the bound `0 ≤ 0`. -/
example (D : ℕ) : count D (-1) = 0 := by
  simp [count, Nat.ceil_eq_zero.mpr (by norm_num : (-1 : ℝ) ≤ 0)]

/-- `0 ≤ L` is needed in `square_div_two_le_sum`: at `L = -1` the sum is empty while
`L ^ 2 / 2 = 1 / 2`. -/
example : ¬ ((-1 : ℝ) ^ 2 / 2 ≤ ∑ u ∈ Finset.range ⌈(-1 : ℝ)⌉₊, (-1 - (u : ℝ))) := by
  rw [Nat.ceil_eq_zero.mpr (by norm_num)]
  norm_num
