/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Combinatorics.CubicStaircase
import ArkLib.ToMathlib.Combinatorics.QuadraticStaircase
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for real-cutoff staircase counts
-/

/-- The slots for weight `1` and cutoff `2` have the stated cubic count. -/
example : Fintype.card (CubicStaircase.Slot 1 2) = 4 := by
  rw [CubicStaircase.card_slot]
  have h : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  simp only [CubicStaircase.count, h, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- The cubic lower bound holds at weight `1` and cutoff `2`. -/
example : (1 : ℝ) * (max 2 0) ^ 3 / 6 ≤ CubicStaircase.count 1 2 :=
  by simpa using CubicStaircase.count_ge_cubic 1 2

/-- The slots for weight `1` and cutoff `2` have the stated quadratic count. -/
example : Fintype.card (QuadraticStaircase.Slot 1 2) = 3 := by
  rw [QuadraticStaircase.card_slot]
  have h : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  simp only [QuadraticStaircase.count, h, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- The quadratic lower bound holds at weight `2` and cutoff `3`. -/
example : (2 : ℝ) * (max 3 0) ^ 2 / 2 ≤ QuadraticStaircase.count 2 3 :=
  QuadraticStaircase.count_ge_quadratic 2 3

/-- At weight `2`, the cutoff `3`, the natural sum formula computes the count. -/
example :
    QuadraticStaircase.count 2 (((3 : ℕ) : ℝ) / 2 - (0 : ℕ)) =
      ∑ u ∈ Finset.range 3, (3 - 2 * (u + 0)) := by
  simpa using QuadraticStaircase.count_div_sub_eq_sum (D := 2) (by norm_num) 3 0
