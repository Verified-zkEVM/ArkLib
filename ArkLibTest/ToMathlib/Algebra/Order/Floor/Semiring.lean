/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for `⌈z⌉₊ - 1`

Concrete values over `ℚ`, and the boundary values showing that the hypotheses `0 < z` and
`1 < z` are needed.
-/

/-- At `z = 5/2`, `⌈z⌉₊ - 1 = 2 < 5/2`. -/
example : (((⌈(5 / 2 : ℚ)⌉₊ - 1 : ℕ) : ℚ)) < 5 / 2 :=
  Nat.cast_ceil_sub_one_lt (by norm_num)

example : ⌈(5 / 2 : ℚ)⌉₊ - 1 = 2 := by
  have : ⌈(5 / 2 : ℚ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  omega

/-- At `z = 3/2`, `⌈z⌉₊ - 1 = 1`, so the lower bound `1 ≤ ⌈z⌉₊ - 1` is attained. -/
example : 1 ≤ ⌈(3 / 2 : ℚ)⌉₊ - 1 := Nat.one_le_ceil_sub_one (by norm_num)

/-- `0 < z` is needed in `Nat.cast_ceil_sub_one_lt`: at `z = 0` the strict inequality fails. -/
example : ¬ (((⌈(0 : ℚ)⌉₊ - 1 : ℕ) : ℚ)) < 0 := by simp

/-- `1 < z` is needed in `Nat.one_le_ceil_sub_one`: at `z = 1` the value is `0`. -/
example : ¬ 1 ≤ ⌈(1 : ℚ)⌉₊ - 1 := by simp
