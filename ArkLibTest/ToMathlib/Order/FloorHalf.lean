/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Order.FloorHalf
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Floor

/-!
# Acceptance tests for the floor-of-half split

For `x = 5` over `ℚ`, `k = 3` and `A = 8`, the split point is `3 + ⌊5 / 2⌋₊ = 5`, with gaps `4` and
`3`, both at least `5 / 2`. For `x = 1`, the floor is `0` and the gaps still exceed `1 / 2` because
of the `+ 1`. The hypothesis `0 ≤ x` is needed for the split point to stay below `A`.
-/

namespace FloorHalfTest

example : 3 + ⌊(5 : ℚ) / 2⌋₊ = 5 := by
  rw [(Nat.floor_eq_iff (by norm_num) : ⌊(5 : ℚ) / 2⌋₊ = 2 ↔ _).mpr ⟨by norm_num, by norm_num⟩]

/-- The bounds at `x = 5`, `k = 3`, `A = 8`. -/
example : 3 + ⌊(5 : ℚ) / 2⌋₊ ≤ 8 ∧ (5 : ℚ) / 2 ≤ ((8 - (3 + ⌊(5 : ℚ) / 2⌋₊) + 1 : ℕ) : ℚ) := by
  obtain ⟨-, h, h', -⟩ := Nat.add_floor_half_bounds (K := ℚ) (x := 5) (k := 3) (A := 8)
    (by norm_num) (by norm_num)
  exact ⟨h, h'⟩

/-- Subunit margin: at `x = 1` the split point is `k` and the gap `m - k + 1 = 1` covers `1 / 2`. -/
example : (1 : ℚ) / 2 ≤ ((3 + ⌊(1 : ℚ) / 2⌋₊ - 3 + 1 : ℕ) : ℚ) :=
  (Nat.add_floor_half_bounds (K := ℚ) (x := 1) (k := 3) (A := 4) (by norm_num)
    (by norm_num)).2.2.2

/-- `0 ≤ x` is needed: for `x = -2`, `k = 3`, `A = 1` the gap hypothesis `3 + x ≤ A` holds, but
the split point `3 + ⌊-1⌋₊ = 3` exceeds `A`. -/
example : ((3 : ℕ) : ℚ) + -2 ≤ ((1 : ℕ) : ℚ) ∧ ¬ 3 + ⌊(-2 : ℚ) / 2⌋₊ ≤ 1 := by
  refine ⟨by norm_num, ?_⟩
  rw [Nat.floor_eq_zero.mpr (by norm_num)]
  omega

end FloorHalfTest
