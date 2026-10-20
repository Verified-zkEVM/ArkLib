/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Order.FloorHalf
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Floor

/-!
# Concrete floor-of-half split

The four bounds at one rational instance.
-/

/-- The bounds at `x = 5`, `k = 3`, `A = 8`. -/
example :
    3 + ⌊(5 : ℚ) / 2⌋₊ ≤ 8 ∧
      (5 : ℚ) / 2 ≤ ((8 - (3 + ⌊(5 : ℚ) / 2⌋₊) + 1 : ℕ) : ℚ) := by
  obtain ⟨-, h, h', -⟩ := Nat.add_floor_half_bounds (K := ℚ) (x := 5) (k := 3) (A := 8)
    (by norm_num) (by norm_num)
  exact ⟨h, h'⟩
