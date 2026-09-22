/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Combinatorics.CubicStaircase

/-!
# Acceptance cases for the cubic real-cutoff staircase

A nonintegral cutoff evaluated by hand, the slot count and a decoded slot, the lower bound, the
closed form of the unrounded sum, and `cube_div_six_le_sum` at a negative cutoff, where the source
assumed `0 < L`.
-/

open CubicStaircase

/-- At `D = 2` and `L = 3 / 2`: total degree `0` has one pair and `⌈3⌉₊ = 3` values of `x`, total
degree `1` has two pairs and `⌈1⌉₊ = 1` value, so the count is `3 + 2 = 5`. -/
example : count 2 (3 / 2) = 5 := by
  have h1 : ⌈(3 / 2 : ℝ)⌉₊ = 2 := by norm_num [Nat.ceil_eq_iff]
  have h2 : ⌈((2 : ℕ) : ℝ) * (3 / 2 - ((0 : ℕ) : ℝ))⌉₊ = 3 := by norm_num
  have h3 : ⌈((2 : ℕ) : ℝ) * (3 / 2 - ((1 : ℕ) : ℝ))⌉₊ = 1 := by norm_num
  simp only [count, h1, Finset.sum_range_succ, Finset.sum_range_zero, h2, h3]

/-- The lower bound at the same cutoff: `2 * (3 / 2) ^ 3 / 6 = 9 / 8 ≤ 5`. -/
example : (9 / 8 : ℝ) ≤ count 2 (3 / 2) := by
  have h := count_ge_cubic 2 (3 / 2)
  norm_num at h
  exact h

/-- The slot type has `count D L` elements: at `D = 1`, `L = 2` the triples are `(0, 0, 0)`,
`(1, 0, 0)`, `(0, 1, 0)` and `(0, 0, 1)`. -/
example : Fintype.card (Slot 1 2) = 4 := by
  rw [card_slot]
  have h1 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  simp only [count, h1, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- The slot with total degree `1`, first exponent `0` and weighted exponent `0` decodes to
`(0, 0, 1)`, which satisfies `0 + 1 * (0 + 1) < 1 * 2`. -/
example : ∃ a : Slot 1 2, a.exponents = (0, 0, 1) := by
  have h1 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  have h2 : 0 < ⌈((1 : ℕ) : ℝ) * (2 - ((1 : ℕ) : ℝ))⌉₊ := by norm_num
  exact ⟨⟨⟨1, by omega⟩, ⟨0, by omega⟩, ⟨0, h2⟩⟩, rfl⟩

/-- The closed form at `n = 2`, `L = 2`: `2 * 1 + 1 * 2 = 4`, and `2 * 3 * 4 / 6 = 4`. -/
example : ∑ s ∈ Finset.range 2, ((s : ℝ) + 1) * (2 - s) = 4 := by
  have h := six_mul_sum 2 2
  norm_num at h
  linarith

/-- `cube_div_six_le_sum` holds at `L = -2`, outside the source's hypothesis `0 < L`: the sum is
empty and `(-2) ^ 3 / 6 = -4 / 3 ≤ 0`. -/
example : ((-2 : ℝ)) ^ 3 / 6 ≤ 0 := by
  have h := cube_div_six_le_sum (-2)
  rwa [Nat.ceil_eq_zero.mpr (by norm_num), Finset.sum_range_zero] at h
