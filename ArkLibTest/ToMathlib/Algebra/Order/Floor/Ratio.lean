/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Algebra.Order.Floor.Ratio
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Floor

/-!
# Acceptance cases for the explicit floor and ceiling errors

Concrete instances over `ℚ`, the cases showing that the additive `1`, the hypothesis `0 < R` and
the factor `2` cannot be dropped, and `Nat.one_div_floor_le` and `Nat.div_floor_bounds` over `ℝ`
with the hypothesis `2 ≤ R`.
-/

/-- `⌈5 / 2⌉₊ = 3 ≤ 5 / 2 + 1`. -/
example : ((3 : ℕ) : ℚ) ≤ 7 / 2 := by
  have hc : ⌈(5 / 2 : ℚ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have h := Nat.cast_ceil_le_max_add_one (5 / 2 : ℚ)
  rw [hc] at h
  norm_num at h ⊢

/-- The additive `1` is needed: `⌈1 / 10⌉₊ = 1` exceeds `max (1 / 10) 0`. -/
example : ¬ ((⌈(1 / 10 : ℚ)⌉₊ : ℚ) ≤ max (1 / 10) 0) := by
  have hc : ⌈(1 / 10 : ℚ)⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [hc]
  norm_num

/-- Truncated subtraction: `⌈2⌉₊ - 5 = 0`, and the bound reads `0 ≤ 0 + 1`. For `s = 1` it reads
`⌈5 / 2⌉₊ - 1 = 2 ≤ 3 / 2 + 1`. -/
example : ((⌈(5 / 2 : ℚ)⌉₊ - 1 : ℕ) : ℚ) = 2 ∧ (2 : ℚ) ≤ max (5 / 2 - 1) 0 + 1 := by
  have hc : ⌈(5 / 2 : ℚ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have h := Nat.cast_ceil_sub_le_max_sub_add_one (5 / 2 : ℚ) 1
  rw [hc] at h ⊢
  norm_num at h ⊢

/-- `R = 3 / 2`: `1 / ⌊3 / 2⌋₊ = 1 ≤ (1 + 4 / 3) / (3 / 2) = 14 / 9`. This is in the range
`1 ≤ R < 2`, which the hypothesis `2 ≤ R` would exclude. -/
example : (1 : ℚ) ≤ 14 / 9 := by
  have hf : ⌊(3 / 2 : ℚ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have h := Nat.one_div_floor_le (by norm_num : (0 : ℚ) < 3 / 2)
  rw [hf] at h
  norm_num at h
  linarith

/-- The hypothesis `0 < R` is needed: at `R = -3` the left side is `0` and the right side is
`-1 / 9`. -/
example : ¬ (1 / (⌊(-3 : ℚ)⌋₊ : ℚ) ≤ (1 + 2 / (-3)) / (-3)) := by
  rw [Nat.floor_eq_zero.mpr (by norm_num)]
  norm_num

/-- The factor `2` cannot be lowered to `1`: at `R = 19 / 10` the floor is `1`, and
`1 ≤ (1 + 1 / R) / R = 290 / 361` is false. -/
example : ¬ (1 / (⌊(19 / 10 : ℚ)⌋₊ : ℚ) ≤ (1 + 1 / (19 / 10)) / (19 / 10)) := by
  have hf : ⌊(19 / 10 : ℚ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [hf]
  norm_num

/-- `R = 5 / 2`, `N = 5`: `2 ≤ 5 / ⌊5 / 2⌋₊ = 5 / 2 ≤ 2 (1 + 4 / 5)`. -/
example : (2 : ℚ) ≤ 5 / 2 ∧ (5 / 2 : ℚ) ≤ 18 / 5 := by
  have hf : ⌊(5 / 2 : ℚ)⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have h := Nat.div_floor_bounds (N := (5 : ℚ)) (by norm_num : (1 : ℚ) ≤ 5 / 2) (by norm_num)
  rw [hf] at h
  norm_num at h ⊢

/-- `Nat.one_div_floor_le` over `ℝ` with `2 ≤ R`. -/
example (R : ℝ) (hR : 2 ≤ R) : 1 / (Nat.floor R : ℝ) ≤ (1 + 2 / R) / R :=
  Nat.one_div_floor_le (by linarith)

/-- `Nat.div_floor_bounds` over `ℝ` with `2 ≤ R`. -/
example (R N : ℝ) (hR : 2 ≤ R) (hN : 0 ≤ N) :
    N / R ≤ N / (Nat.floor R : ℝ) ∧ N / (Nat.floor R : ℝ) ≤ N / R * (1 + 2 / R) :=
  Nat.div_floor_bounds (by linarith) hN
