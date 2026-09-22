/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Explicit errors of the natural floor and ceiling

Rounding a real parameter to a natural number changes it by less than one. This file records the
explicit consequences of that fact used by parameter calculations, in a linearly ordered field `K`
with a `FloorSemiring` structure.

For the natural ceiling, `⌈t⌉₊ ≤ max t 0 + 1` for every `t`, and more generally
`⌈t⌉₊ - s ≤ max (t - s) 0 + 1` for natural `s`, with truncated subtraction on the left. This is
how a count of natural numbers below a real cutoff is compared with the positive part of the
cutoff.

For the natural floor of `R > 0`, `1 / ⌊R⌋₊ ≤ (1 + 2 / R) / R`: for `R ≥ 2` this follows from
`⌊R⌋₊ > R - 1` and `R ^ 2 ≤ (R + 2) (R - 1)`, and for `1 ≤ R < 2` from `R ^ 2 ≤ R + 2`. Dividing a
nonnegative numerator by `⌊R⌋₊` instead of `R ≥ 1` therefore costs at most the factor `1 + 2 / R`.

## Main statements

* `Nat.cast_ceil_le_max_add_one`, `Nat.cast_ceil_sub_le_max_sub_add_one`
* `Nat.one_div_floor_le`, `Nat.div_floor_bounds`

## References

These generalize declarations of ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `ReedSolomon.HiddenDerivative.ceil_residual_le` of
  `Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/RankBound.lean` is
  `Nat.cast_ceil_le_max_add_one`, stated in `K` instead of `ℝ`.
  `Nat.cast_ceil_sub_le_max_sub_add_one` is new; it is the form needed after the local residual
  budget switched to the natural cutoff `⌈T⌉₊`.
* `ReedSolomon.HiddenDerivative.InterpolationRounding.floor_reciprocal_le` and
  `floor_ratio_bounds` of `Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/`
  `RankRounding.lean` are `Nat.one_div_floor_le` and `Nat.div_floor_bounds`, stated in `K`, with
  the source's hypothesis `2 ≤ R` weakened to `0 < R` and `1 ≤ R` respectively.
  The source's `floor_pos` is Mathlib's `Nat.floor_pos`.
-/

@[expose] public section

namespace Nat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/-- The natural ceiling exceeds the positive part by at most one: `⌈t⌉₊ ≤ max t 0 + 1`. For
`t ≤ 0` the ceiling is `0`; for `t > 0` it is below `t + 1`. -/
theorem cast_ceil_le_max_add_one (t : K) : (⌈t⌉₊ : K) ≤ max t 0 + 1 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [Nat.ceil_eq_zero.mpr ht, Nat.cast_zero]
    have := le_max_right t 0
    linarith
  · have := Nat.ceil_lt_add_one ht.le
    have := le_max_left t 0
    linarith

/-- The number `⌈t⌉₊ - s` of naturals `u` with `s ≤ u < t` (truncated subtraction) is at most
`max (t - s) 0 + 1`. When `s < ⌈t⌉₊` the cutoff `t` is positive and `⌈t⌉₊ < t + 1`; otherwise the
left side is `0`. -/
theorem cast_ceil_sub_le_max_sub_add_one (t : K) (s : ℕ) :
    ((⌈t⌉₊ - s : ℕ) : K) ≤ max (t - s) 0 + 1 := by
  rcases le_or_gt ⌈t⌉₊ s with hs | hs
  · rw [Nat.sub_eq_zero_of_le hs, Nat.cast_zero]
    have := le_max_right (t - s) 0
    linarith
  · have ht : 0 < t := Nat.ceil_pos.mp (lt_of_le_of_lt (Nat.zero_le s) hs)
    rw [Nat.cast_sub hs.le]
    have := Nat.ceil_lt_add_one ht.le
    have := le_max_left (t - s) 0
    linarith

/-- For `R > 0`, replacing `R` by its floor in a reciprocal costs at most the factor
`1 + 2 / R`: `1 / ⌊R⌋₊ ≤ (1 + 2 / R) / R`. For `R < 1` the floor is `0` and the left side is `0`
by the convention `1 / 0 = 0`. For `⌊R⌋₊ = k ≥ 1` the inequality is `R ^ 2 ≤ k (R + 2)`, which
holds on `[k, k + 1)` because `(k + 1) ^ 2 ≤ k (k + 3)`; the factor `2` cannot be lowered to
`1`, since at `R = 2 - ε` it would require `(2 - ε) ^ 2 ≤ 3 - ε`. The hypothesis `0 < R` is
needed: at `R = -3` the right side is `-1 / 9`. -/
theorem one_div_floor_le {R : K} (hR : 0 < R) :
    1 / (⌊R⌋₊ : K) ≤ (1 + 2 / R) / R := by
  rcases lt_or_ge R 1 with hR1 | hR1
  · rw [Nat.floor_eq_zero.mpr hR1, Nat.cast_zero, div_zero]
    positivity
  have hF : (1 : K) ≤ ⌊R⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hR1)
  have hfloor : R - 1 < ⌊R⌋₊ := Nat.sub_one_lt_floor R
  have key : R ^ 2 ≤ ⌊R⌋₊ * (R + 2) := by
    rcases le_or_gt 2 R with h2 | h2
    · nlinarith [mul_le_mul_of_nonneg_right hfloor.le (by linarith : (0 : K) ≤ R + 2)]
    · nlinarith [mul_le_mul_of_nonneg_right hF (by linarith : (0 : K) ≤ R + 2)]
  rw [div_le_div_iff₀ (by linarith) hR, one_mul,
    show (1 + 2 / R) * (⌊R⌋₊ : K) = ⌊R⌋₊ * (R + 2) / R by field_simp, le_div_iff₀ hR]
  nlinarith

/-- Dividing a nonnegative `N` by `⌊R⌋₊` instead of `R ≥ 1` increases the quotient by at most the
factor `1 + 2 / R`: `N / R ≤ N / ⌊R⌋₊ ≤ N / R * (1 + 2 / R)`. The hypothesis `1 ≤ R` is needed for
the lower bound: for `0 < R < 1` the floor is `0` and `N / 0 = 0 < N / R` when `N > 0`. -/
theorem div_floor_bounds {R N : K} (hR : 1 ≤ R) (hN : 0 ≤ N) :
    N / R ≤ N / (⌊R⌋₊ : K) ∧ N / (⌊R⌋₊ : K) ≤ N / R * (1 + 2 / R) := by
  have hRp : 0 < R := by linarith
  have hFp : (0 : K) < ⌊R⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hR
  refine ⟨div_le_div_of_nonneg_left hN hFp (Nat.floor_le hRp.le), ?_⟩
  have h := mul_le_mul_of_nonneg_left (one_div_floor_le hRp) hN
  calc N / (⌊R⌋₊ : K) = N * (1 / (⌊R⌋₊ : K)) := by ring
    _ ≤ N * ((1 + 2 / R) / R) := h
    _ = N / R * (1 + 2 / R) := by ring

end Nat
