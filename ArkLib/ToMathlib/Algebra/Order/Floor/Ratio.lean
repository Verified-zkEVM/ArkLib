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
* `Nat.one_sub_one_div_mul_lt_floor`: `(1 - 1 / N) R < ⌊R⌋₊` for `0 < N ≤ R`
* `Nat.cast_ceil_mul_div_le_inv_slack` bounds a natural ceiling from a multiplicity bound.
* `Nat.cast_max_one_floor_mul_div_le_inv_slack_sq` bounds a floored quotient from rank and gap
  bounds.
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

/-- Once `R ≥ N > 0`, the floor of `R` loses less than the fraction `1 / N` of `R`:
`(1 - 1 / N) R < ⌊R⌋₊`. The absolute error of the floor is below `1`, and `1 ≤ R / N`. The
hypothesis `N ≤ R` is needed: at `N = 2`, `R = 1 / 2` the left side is `1 / 4` and the floor is
`0`. -/
theorem one_sub_one_div_mul_lt_floor {N R : K} (hN : 0 < N) (hNR : N ≤ R) :
    (1 - 1 / N) * R < ⌊R⌋₊ := by
  have h1 : 1 ≤ R / N := (one_le_div hN).mpr hNR
  have h := Nat.sub_one_lt_floor R
  have heq : (1 - 1 / N) * R = R - R / N := by ring
  linarith

/-- The ceiling of a multiplicity-scaled agreement has inverse-slack size. -/
theorem cast_ceil_mul_div_le_inv_slack
    {rho slack agreement rate C : K} {m : ℕ}
    (hrho : 0 < rho) (hslack : 0 < slack) (hslackOne : slack ≤ 1)
    (hagreement : 0 ≤ agreement) (hagreementOne : agreement ≤ 1)
    (hrate : 0 < rate) (hrateLower : rho / 2 ≤ rate)
    (hm : (m : K) ≤ C / slack) :
    (Nat.ceil ((m : K) * agreement / rate) : K) ≤
      (2 * C / rho + 1) / slack := by
  have hm0 : (0 : K) ≤ m := Nat.cast_nonneg _
  have hma : (m : K) * agreement ≤ m := by
    nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hagreementOne)]
  have hratio : (m : K) / rate ≤ 2 * (m : K) / rho := by
    rw [div_le_iff₀ hrate, div_eq_mul_inv]
    field_simp [ne_of_gt hrho]
    nlinarith
  have harg : (m : K) * agreement / rate ≤ 2 * C / (rho * slack) := by
    calc
      (m : K) * agreement / rate ≤ (m : K) / rate :=
        div_le_div_of_nonneg_right hma hrate.le
      _ ≤ 2 * (m : K) / rho := hratio
      _ ≤ 2 * (C / slack) / rho := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm (by norm_num)) hrho.le
      _ = 2 * C / (rho * slack) := by ring
  have hceil : (Nat.ceil ((m : K) * agreement / rate) : K) <
      (m : K) * agreement / rate + 1 := by
    apply Nat.ceil_lt_add_one
    exact div_nonneg (mul_nonneg hm0 hagreement) hrate.le
  calc
    (Nat.ceil ((m : K) * agreement / rate) : K) ≤
        2 * C / (rho * slack) + 1 :=
      (hceil.trans_le (by simpa [add_comm] using add_le_add_right harg 1)).le
    _ = (2 * C / rho + slack) / slack := by
      field_simp [ne_of_gt hrho, ne_of_gt hslack]
    _ ≤ (2 * C / rho + 1) / slack := by gcongr
    _ = _ := by ring

/-- A rank and jet bound with a cubic count gap bounds the floored challenge quotient. -/
theorem cast_max_one_floor_mul_div_le_inv_slack_sq
    {m rank jet : ℕ} {slack slope rankConstant jetConstant gap : K}
    (hm : 0 < (m : K)) (hslack : 0 < slack) (hslackOne : slack ≤ 1)
    (hslope : 0 < slope) (hrankConstant : 0 ≤ rankConstant)
    (hjetConstant : 0 ≤ jetConstant)
    (hrank : (rank : K) ≤ rankConstant * (m : K) ^ 3)
    (hjet : (jet : K) ≤ jetConstant / slack)
    (hgap : 3 * (m : K) ^ 3 * (slope * slack) / 4 ≤ gap) :
    ((Nat.max 1 ⌊(rank : K) * jet / gap⌋₊ : ℕ) : K) ≤
      (1 + 4 * rankConstant * jetConstant / (3 * slope)) / slack ^ 2 := by
  have hgapPos : 0 < gap := by
    exact (by positivity : 0 < 3 * (m : K) ^ 3 * (slope * slack) / 4).trans_le hgap
  have hnum : (rank : K) * jet ≤
      rankConstant * (m : K) ^ 3 * (jetConstant / slack) := by
    gcongr
  have hquot : (rank : K) * jet / gap ≤
      4 * rankConstant * jetConstant / (3 * slope * slack ^ 2) := by
    calc
      (rank : K) * jet / gap ≤
          (rankConstant * (m : K) ^ 3 * (jetConstant / slack)) / gap :=
        div_le_div_of_nonneg_right hnum hgapPos.le
      _ ≤ (rankConstant * (m : K) ^ 3 * (jetConstant / slack)) /
          (3 * (m : K) ^ 3 * (slope * slack) / 4) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hgap
      _ = 4 * rankConstant * jetConstant / (3 * slope * slack ^ 2) := by
        field_simp [ne_of_gt hm, ne_of_gt hslope, ne_of_gt hslack]
  have hquot0 : 0 ≤ (rank : K) * jet / gap := by positivity
  have hheight : ((Nat.max 1 ⌊(rank : K) * jet / gap⌋₊ : ℕ) : K) ≤
      1 + (rank : K) * jet / gap := by
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith
    · exact (Nat.floor_le hquot0).trans (by linarith)
  calc
    ((Nat.max 1 ⌊(rank : K) * jet / gap⌋₊ : ℕ) : K) ≤
        1 + 4 * rankConstant * jetConstant / (3 * slope * slack ^ 2) := by
      linarith
    _ = 1 + (4 * rankConstant * jetConstant / (3 * slope)) / slack ^ 2 := by
      ring
    _ ≤ (1 + 4 * rankConstant * jetConstant / (3 * slope)) / slack ^ 2 := by
      have hslackSq : slack ^ 2 ≤ 1 := pow_le_one₀ hslack.le hslackOne
      have hK : 0 ≤ 4 * rankConstant * jetConstant / (3 * slope) := by positivity
      rw [le_div_iff₀ (sq_pos_of_pos hslack)]
      calc
        (1 + 4 * rankConstant * jetConstant / (3 * slope) / slack ^ 2) * slack ^ 2 =
            slack ^ 2 + 4 * rankConstant * jetConstant / (3 * slope) := by
          field_simp [ne_of_gt hslack]
        _ ≤ 1 + 4 * rankConstant * jetConstant / (3 * slope) := by
          simpa [add_comm] using
            add_le_add_right hslackSq (4 * rankConstant * jetConstant / (3 * slope))
    _ = _ := by ring_nf

end Nat
