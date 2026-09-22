/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Algebra.Order.Floor.RelativeError
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

/-!
# Relative floor error acceptance tests

Concrete instances over `ℚ` of the two relative floor bounds, and cases showing that each
hypothesis `0 < c`, `1 < c` and `c ≤ x` is needed.
-/

private theorem floor_five_halves : ⌊(5 / 2 : ℚ)⌋₊ = 2 := by
  rw [Nat.floor_eq_iff (by norm_num)]; norm_num

private theorem floor_nineteen_tenths : ⌊(19 / 10 : ℚ)⌋₊ = 1 := by
  rw [Nat.floor_eq_iff (by norm_num)]; norm_num

private theorem floor_half : ⌊(1 / 2 : ℚ)⌋₊ = 0 := by
  rw [Nat.floor_eq_zero]; norm_num

/-! ### Concrete instances -/

/-- At `c = 2 ≤ x = 5/2`, the floor `⌊x⌋₊ = 2` is at least `(1 - 1/2) · 5/2 = 5/4`. -/
example : (1 - (2 : ℚ)⁻¹) * (5 / 2) ≤ ⌊(5 / 2 : ℚ)⌋₊ :=
  Nat.one_sub_inv_mul_le_floor (by norm_num) (by norm_num)

/-- At `c = 2 ≤ x = 5/2`, the ratio `x / ⌊x⌋₊ = 5/4` is at most `c / (c - 1) = 2`. -/
example : (5 / 2 : ℚ) / ⌊(5 / 2 : ℚ)⌋₊ ≤ 2 := by
  have h := Nat.div_floor_le_div_sub_one (c := (2 : ℚ)) (x := 5 / 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-! ### Boundary hypotheses -/

/-- `one_sub_inv_mul_le_floor` needs `0 < c`: at `c = -1 ≤ x = 1/2`, `(1 - c⁻¹) x = 1` exceeds
`⌊x⌋₊ = 0`. -/
example : ¬ ((1 - (-1 : ℚ)⁻¹) * (1 / 2) ≤ ⌊(1 / 2 : ℚ)⌋₊) := by
  rw [floor_half]; norm_num

/-- `one_sub_inv_mul_le_floor` needs `c ≤ x`: at `c = 2`, `x = 1/2`, `(1 - c⁻¹) x = 1/4` exceeds
`⌊x⌋₊ = 0`. -/
example : ¬ ((1 - (2 : ℚ)⁻¹) * (1 / 2) ≤ ⌊(1 / 2 : ℚ)⌋₊) := by
  rw [floor_half]; norm_num

/-- `div_floor_le_div_sub_one` needs `c ≤ x`: at `c = 3`, `x = 19/10`, the ratio `19/10` exceeds
`c / (c - 1) = 3/2`. -/
example : ¬ ((19 / 10 : ℚ) / ⌊(19 / 10 : ℚ)⌋₊ ≤ 3 / (3 - 1)) := by
  rw [floor_nineteen_tenths]; norm_num

/-- `div_floor_le_div_sub_one` needs `1 < c`: at `c = 1/2 ≤ x = 5/2`, the ratio `5/4` exceeds
`c / (c - 1) = -1`. -/
example : ¬ ((5 / 2 : ℚ) / ⌊(5 / 2 : ℚ)⌋₊ ≤ (1 / 2) / (1 / 2 - 1)) := by
  rw [floor_five_halves]; norm_num
