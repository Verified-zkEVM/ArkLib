/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Algebra.Order.Floor.Ratio
import ArkLib.ToMathlib.Algebra.Order.Floor.RelativeError
import ArkLib.ToMathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum

/-!
# Concrete floor and ceiling bounds

Small rational instances exercise the ceiling, floor, relative-error, and rounded ceiling-minus-one
bounds.
-/

/-- `⌈5 / 2⌉₊ = 3 ≤ 5 / 2 + 1`. -/
example : ((3 : ℕ) : ℚ) ≤ 7 / 2 := by
  have hc : ⌈(5 / 2 : ℚ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have h := Nat.cast_ceil_le_max_add_one (5 / 2 : ℚ)
  rw [hc] at h
  norm_num at h ⊢

/-- Truncated subtraction: `⌈5 / 2⌉₊ - 1 = 2 ≤ max (5 / 2 - 1) 0 + 1`. -/
example :
    ((⌈(5 / 2 : ℚ)⌉₊ - 1 : ℕ) : ℚ) = 2 ∧ (2 : ℚ) ≤ max (5 / 2 - 1) 0 + 1 := by
  have hc : ⌈(5 / 2 : ℚ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have h := Nat.cast_ceil_sub_le_max_sub_add_one (5 / 2 : ℚ) 1
  rw [hc] at h ⊢
  norm_num at h ⊢

/-- `R = 3 / 2`: `1 / ⌊R⌋₊ = 1 ≤ (1 + 2 / R) / R`. -/
example : (1 : ℚ) ≤ 14 / 9 := by
  have hf : ⌊(3 / 2 : ℚ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have h := Nat.one_div_floor_le (by norm_num : (0 : ℚ) < 3 / 2)
  rw [hf] at h
  norm_num at h
  linarith

/-- `R = 5 / 2`, `N = 5`: `2 ≤ 5 / ⌊R⌋₊ ≤ 2 (1 + 2 / R)`. -/
example : (2 : ℚ) ≤ 5 / 2 ∧ (5 / 2 : ℚ) ≤ 18 / 5 := by
  have hf : ⌊(5 / 2 : ℚ)⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have h := Nat.div_floor_bounds (N := (5 : ℚ)) (by norm_num : (1 : ℚ) ≤ 5 / 2) (by norm_num)
  rw [hf] at h
  norm_num at h ⊢

/-- At `c = 2 ≤ x = 5/2`, the floor `⌊x⌋₊ = 2` is at least `(1 - 1/2) · 5/2 = 5/4`. -/
example : (1 - (2 : ℚ)⁻¹) * (5 / 2) ≤ ⌊(5 / 2 : ℚ)⌋₊ :=
  Nat.one_sub_inv_mul_le_floor (by norm_num) (by norm_num)

/-- At `c = 2 ≤ x = 5/2`, the ratio `x / ⌊x⌋₊ = 5/4` is at most `c / (c - 1) = 2`. -/
example : (5 / 2 : ℚ) / ⌊(5 / 2 : ℚ)⌋₊ ≤ 2 := by
  have h := Nat.div_floor_le_div_sub_one (c := (2 : ℚ)) (x := 5 / 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- At `z = 5/2`, `⌈z⌉₊ - 1 = 2 < 5/2`. -/
example : (((⌈(5 / 2 : ℚ)⌉₊ - 1 : ℕ) : ℚ)) < 5 / 2 :=
  Nat.cast_ceil_sub_one_lt (by norm_num)

/-- At `z = 3/2`, `⌈z⌉₊ - 1 = 1`, so the lower bound is attained. -/
example : 1 ≤ ⌈(3 / 2 : ℚ)⌉₊ - 1 := Nat.one_le_ceil_sub_one (by norm_num)
