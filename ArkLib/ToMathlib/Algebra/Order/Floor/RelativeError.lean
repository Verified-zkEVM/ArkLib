/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Relative error of the natural floor

In a linearly ordered field, `⌊x⌋₊ > x - 1`. When `x` is at least some `c > 0`, this becomes a
relative bound: `⌊x⌋₊ ≥ (1 - 1/c) x`. Equivalently, for `c > 1` the ratio `x / ⌊x⌋₊` is at most
`c / (c - 1)`, so dividing by the floor instead of by `x` costs a factor at most `1 + 1/(c - 1)`.

## Main statements

* `Nat.one_sub_inv_mul_le_floor`: `(1 - c⁻¹) x ≤ ⌊x⌋₊` for `0 < c ≤ x`.
* `Nat.div_floor_le_div_sub_one`: `x / ⌊x⌋₊ ≤ c / (c - 1)` for `1 < c ≤ x`.
-/

@[expose] public section

namespace Nat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/-- For `0 < c ≤ x`, the natural floor loses at most the fraction `1 / c` of `x`:
`(1 - c⁻¹) x ≤ ⌊x⌋₊`. -/
theorem one_sub_inv_mul_le_floor {c x : K} (hc : 0 < c) (hcx : c ≤ x) :
    (1 - c⁻¹) * x ≤ ⌊x⌋₊ := by
  have hfloor := Nat.sub_one_lt_floor x
  have hone : 1 ≤ c⁻¹ * x := by
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  linarith [show (1 - c⁻¹) * x = x - c⁻¹ * x by ring]

/-- For `1 < c ≤ x`, the ratio `x / ⌊x⌋₊` is at most `c / (c - 1)`. -/
theorem div_floor_le_div_sub_one {c x : K} (hc : 1 < c) (hcx : c ≤ x) :
    x / ⌊x⌋₊ ≤ c / (c - 1) := by
  have hfloor := Nat.sub_one_lt_floor x
  have hpos : (0 : K) < ⌊x⌋₊ := by linarith
  rw [div_le_div_iff₀ hpos (by linarith)]
  nlinarith

end Nat
