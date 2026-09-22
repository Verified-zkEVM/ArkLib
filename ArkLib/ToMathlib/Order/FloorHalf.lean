/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith

/-!
# Splitting a gap at the floor of its half

Let `k ≤ A` be natural numbers whose gap is at least a nonnegative element `x` of an ordered field
with a floor, that is `k + x ≤ A`. The natural number `m = k + ⌊x / 2⌋₊` lies between `k` and `A`,
and both integer gaps, `A - m + 1` and `m - k + 1`, are at least `x / 2`. The `+ 1` absorbs the
rounding, so the conclusion holds also for `x < 2`, where `⌊x / 2⌋₊ = 0`.

## Main statements

* `Nat.add_floor_half_bounds`: the four bounds.

## References

This is the content of `ReedSolomon.correlatedMidpoint_bounds` in
`Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/Midpoint.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, where `x = δ * n` is real. Here `x` is an arbitrary
element of an ordered field with a floor, and the bound by the block length `n` is left to the
caller.
-/

@[expose] public section

namespace Nat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/-- **Floor-of-half split of a gap.** If `0 ≤ x` and `k + x ≤ A`, then `m = k + ⌊x / 2⌋₊`
satisfies `k ≤ m ≤ A`, `x / 2 ≤ A - m + 1` and `x / 2 ≤ m - k + 1`.

`0 ≤ x` is needed for `m ≤ A`: for `x < 0` the floor is `0`, so `m = k`, while `k + x ≤ A` allows
`A < k`. -/
theorem add_floor_half_bounds {x : K} {k A : ℕ} (hx : 0 ≤ x) (hgap : (k : K) + x ≤ A) :
    k ≤ k + ⌊x / 2⌋₊ ∧ k + ⌊x / 2⌋₊ ≤ A ∧
      x / 2 ≤ ((A - (k + ⌊x / 2⌋₊) + 1 : ℕ) : K) ∧
      x / 2 ≤ ((k + ⌊x / 2⌋₊ - k + 1 : ℕ) : K) := by
  have hfloor := Nat.floor_le (div_nonneg hx zero_le_two : (0 : K) ≤ x / 2)
  have hlt := Nat.lt_floor_add_one (x / 2)
  have hmA : k + ⌊x / 2⌋₊ ≤ A := by
    have : ((k + ⌊x / 2⌋₊ : ℕ) : K) ≤ A := by push_cast; linarith
    exact_mod_cast this
  refine ⟨Nat.le_add_right _ _, hmA, ?_, ?_⟩
  · rw [Nat.cast_add, Nat.cast_sub hmA]
    push_cast
    linarith
  · rw [Nat.add_sub_cancel_left]
    push_cast
    linarith

end Nat
