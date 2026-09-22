/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.BigOperators.Intervals
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith

/-!
# Acceptance tests for the cast power sums

Concrete values of `Finset.sum_range_natCast_mul_two` and `Finset.sum_range_natCast_sq_mul_six`,
the empty sum where `n - 1` is a negative ring element, and a ring where `2` is not invertible.
-/

open Finset

/-- `0 + 1 + 2 + 3 = 6` in `ℚ`, from the doubled form. -/
example : (∑ i ∈ range 4, (i : ℚ)) = 6 := by
  have h := sum_range_natCast_mul_two (R := ℚ) 4
  norm_num at h
  linarith

/-- `0 + 1 + 4 + 9 + 16 = 30` in `ℚ`, from the form multiplied by `6`. -/
example : (∑ i ∈ range 5, (i : ℚ) ^ 2) = 30 := by
  have h := sum_range_natCast_sq_mul_six (R := ℚ) 5
  norm_num at h
  linarith

/-- At `n = 0` the right side is `0 * (0 - 1) = 0` with ring subtraction `0 - 1 = -1`. -/
example : (∑ i ∈ range 0, (i : ℤ)) * 2 = 0 * (0 - 1) :=
  sum_range_natCast_mul_two 0

/-- The statements hold in a ring where `2` and `6` are zero divisors: in `ZMod 6`,
`(0 + 1 + 2) * 2 = 3 * 2 = 0`. -/
example : (∑ i ∈ range 3, (i : ZMod 6)) * 2 = 3 * (3 - 1) :=
  sum_range_natCast_mul_two 3
