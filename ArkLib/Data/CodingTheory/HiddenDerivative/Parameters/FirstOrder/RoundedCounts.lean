/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Counting
public import ArkLib.ToMathlib.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Rounded source and rank counts for first-order interpolation

First-order interpolation at multiplicity `m` uses jet monomials of total degree `t ≤ μ` in
`Y₀, Y₁` with `Y₁`-degree at most `M`; there are `min t M + 1` of them at each `t`. For a code of
degree `D ≤ R n` and agreement `A ≥ a n`, the `X`-degree budget `m A - D t` left at total degree
`t` is at least `n (m a - R t)` (`mul_max_rateResidual_le_max_residual`). Summing gives the real
source count per unit of block length

```text
N₀(R, a, m, M, μ) = ∑_{t ≤ μ} (min t M + 1) · max (m a - R t) 0.
```

The local constraints at one agreement point have rank at most

```text
r(m, M) = ∑_{s < m} ((s + 1)(M + 1) - (2s + 1 - m)(s + M + 1 - m)),
```

the first-order case of `certifiedEnlargedRankBound`. The interpolation argument needs
`r(m, M) < N₀(R, a, m, M, μ)`.

This file compares both counts with their continuous densities at the rounded caps
`M = ⌊β m⌋₊` and `μ ≥ ⌊m a / R⌋₊`, for a derivative-degree ratio `β`:

* the source count loses nothing to rounding,
  `m³ (β a²/(2R) - a β²/2 + R β³/6) ≤ N₀`, for `0 < R ≤ a` and `0 ≤ β ≤ a / R`;
* the rank count loses at most `3 m²` against the cubic envelope,
  `r ≤ m³ (β/2 - β²/2 + β³/3) + 3 m²`, for `0 ≤ β ≤ 3/4`.

Hence a positive gap `S` between the two densities gives a finite surplus `N₀ - r ≥ m³ S - 3m²`,
which is positive once `m S > 3`. The file also contains the two comparisons that consume a
surplus: each real source residual is below the corresponding residual of a code with degree
`D ≤ R n` and agreement `A ≥ a n`, and the scaled kernel-height quotient
`n r μ / (N - n r)` is at most `⌊r μ / (N₀ - r)⌋₊` whenever `n N₀ ≤ N`.

## Main statements

* `certifiedEnlargedRankBound_one_eq_firstOrderRankCount`: the certified rank bound at derivative
  order one is `firstOrderRankCount`.
* `firstOrderRankCount_le_cubicUpperCount`: `r(m, M)` is below a signed cubic count.
* `firstOrderRankCount_floor_le`: the rank rounding estimate with loss `3 m²`.
* `cube_mul_sourceDensity_le_firstOrderSourceCount`: the source rounding estimate with no loss.
* `cube_mul_densityGap_sub_le_sourceCount_sub_rankCount`: the combined finite surplus.
* `mul_max_rateResidual_le_max_residual`: comparison of source residuals with code residuals.
* `scaledKernelHeight_le_floor`: the uniform bound on the scaled kernel-height quotient.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open Finset

noncomputable section

/-! ## The two counts -/

/-- The real first-order source count
`N₀(R, a, m, M, μ) = ∑_{t ≤ μ} (min t M + 1) · max (m a - R t) 0` at code rate `R`, agreement
fraction `a`, multiplicity `m`, `Y₁`-degree cap `M`, and total jet-degree cap `μ`. -/
def firstOrderSourceCount (rate agreement : ℝ) (m M mu : ℕ) : ℝ :=
  ∑ t ∈ range (mu + 1), (min t M + 1 : ℕ) * max (m * agreement - rate * t) 0

/-- The first-order local rank count
`r(m, M) = ∑_{s < m} ((s + 1)(M + 1) - (2s + 1 - m)(s + M + 1 - m))` at multiplicity `m` and
`Y₁`-degree cap `M`, with truncated natural subtraction. -/
def firstOrderRankCount (m M : ℕ) : ℕ :=
  ∑ s ∈ range m, ((s + 1) * (M + 1) - (2 * s + 1 - m) * (s + M + 1 - m))

/-- At derivative order one the certified rank bound is `firstOrderRankCount`, at every
higher-jet weight budget `W`. -/
theorem certifiedEnlargedRankBound_one_eq_firstOrderRankCount (m M W : ℕ) :
    certifiedEnlargedRankBound 1 m M W = firstOrderRankCount m M := by
  rw [certifiedEnlargedRankBound, firstOrderRankCount]
  refine sum_congr rfl fun s hs => ?_
  have hs : s < m := mem_range.mp hs
  rw [weightedHigherJetCount_of_le_one le_rfl, one_mul, certifiedContactRankBudget,
    contactThreshold, exhibitedKernelResidualCount, ambientContactCount,
    exhibitedKernelContactCount, ceilDiv_one, show s + 1 - (m - s) = 2 * s + 1 - m by omega,
    show M + 1 - (m - s) = s + M + 1 - m by omega]

/-- The signed cubic count
`∑_{s < m} (s + 1)(M + 1) - ∑_{m - M ≤ s < m} (2s + 1 - m)(s + M + 1 - m)` in `ℝ`. The
subtracted factor `2s + 1 - m` is negative for `s < (m - 1) / 2`, which makes this one polynomial
expression an upper bound for `firstOrderRankCount m M` at every cap `M`. -/
def firstOrderRankCubicUpperCount (m M : ℕ) : ℝ :=
  (∑ s ∈ range m, ((s + 1 : ℕ) : ℝ) * (M + 1)) -
    ∑ s ∈ Ico (m - M) m, (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)

private theorem rank_correction_le_ambient {m M s : ℕ} (hs : s < m) :
    (2 * s + 1 - m) * (s + M + 1 - m) ≤ (s + 1) * (M + 1) := by
  apply Nat.mul_le_mul <;> omega

/-- The first-order rank count is at most its signed cubic count. -/
theorem firstOrderRankCount_le_cubicUpperCount (m M : ℕ) :
    (firstOrderRankCount m M : ℝ) ≤ firstOrderRankCubicUpperCount m M := by
  rw [firstOrderRankCount, firstOrderRankCubicUpperCount, Nat.cast_sum]
  have hrank :
      (∑ s ∈ range m,
          (((s + 1) * (M + 1) - (2 * s + 1 - m) * (s + M + 1 - m) : ℕ) : ℝ)) =
        (∑ s ∈ range m, ((s + 1 : ℕ) : ℝ) * (M + 1)) -
          ∑ s ∈ range m, (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun s hs => ?_
    rw [Nat.cast_sub (rank_correction_le_ambient (mem_range.mp hs))]
    push_cast
    rfl
  rw [hrank]
  gcongr
  calc
    (∑ s ∈ Ico (m - M) m, (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)) ≤
        ∑ s ∈ Ico (m - M) m, (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
      refine sum_le_sum fun s hs => ?_
      have hsecond : m ≤ s + M + 1 := by
        have := (mem_Ico.mp hs).1
        omega
      by_cases hfirst : m ≤ 2 * s + 1
      · rw [Nat.cast_sub hfirst, Nat.cast_sub hsecond]
      · have hsigned : ((2 * s + 1 : ℕ) : ℝ) - m < 0 :=
          sub_neg.mpr (Nat.cast_lt.mpr (by omega))
        have hnonneg : 0 ≤ ((s + M + 1 : ℕ) : ℝ) - m :=
          sub_nonneg.mpr (Nat.cast_le.mpr hsecond)
        exact (mul_nonpos_of_nonpos_of_nonneg hsigned.le hnonneg).trans (by positivity)
    _ ≤ ∑ s ∈ range m, (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun s hs => mem_range.mpr (mem_Ico.mp hs).2
      · exact fun s _ _ => by positivity

/-! ## Closed forms of the power sums -/

private def linearSum (x : ℝ) : ℝ := x * (x - 1) / 2

private def squareSum (x : ℝ) : ℝ := x * (x - 1) * (2 * x - 1) / 6

private theorem sum_range_natCast_eq_linearSum (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ)) = linearSum n := by
  rw [linearSum, eq_div_iff two_ne_zero, sum_range_natCast_mul_two]

private theorem sum_range_natCast_sq_eq_squareSum (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ) ^ 2) = squareSum n := by
  rw [squareSum, eq_div_iff (by norm_num : (6 : ℝ) ≠ 0), sum_range_natCast_sq_mul_six]

/-! ## The rank rounding estimate -/

/-- The signed cubic count divided by `m³`, written in `u = M / m` and `v = 1 / m`. -/
private def rankRoundingModel (u v : ℝ) : ℝ :=
  (u + v) * ((1 - v) / 2 + v) -
    (2 * ((1 - v) * (2 - v) / 6 - (1 - u) * (1 - u - v) * (2 * (1 - u) - v) / 6) +
      (2 * u + 3 * v - 3) * ((1 - v) / 2 - (1 - u) * (1 - u - v) / 2) +
      u * (v - 1) * (u + v - 1))

private theorem rankRoundingModel_le {u v beta : ℝ} (hu0 : 0 ≤ u) (hub : u ≤ beta)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hb1 : beta ≤ 3 / 4) :
    rankRoundingModel u v ≤ beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 + 3 * v := by
  have hu34 : u ≤ 3 / 4 := hub.trans hb1
  have hq_eq :
      1 / 2 - (beta + u) / 2 + (beta ^ 2 + beta * u + u ^ 2) / 3 =
        1 / 4 + ((beta - 1 / 2 + (u - 1 / 2)) ^ 2 + (beta - 1 / 2) ^ 2 +
          (u - 1 / 2) ^ 2) / 6 := by ring
  have hq : 0 ≤ 1 / 2 - (beta + u) / 2 + (beta ^ 2 + beta * u + u ^ 2) / 3 := by
    rw [hq_eq]
    exact add_nonneg (by norm_num)
      (div_nonneg (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
        (by norm_num))
  have hP : u / 2 - u ^ 2 / 2 + u ^ 3 / 3 ≤ beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 := by
    have hdiff :
        (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3) - (u / 2 - u ^ 2 / 2 + u ^ 3 / 3) =
          (beta - u) * (1 / 2 - (beta + u) / 2 + (beta ^ 2 + beta * u + u ^ 2) / 3) := by
      ring
    rw [← sub_nonneg, hdiff]
    exact mul_nonneg (sub_nonneg.mpr hub) hq
  have hvSq : v ^ 2 ≤ v := by
    calc
      v ^ 2 = v * v := by ring
      _ ≤ v * 1 := mul_le_mul_of_nonneg_left hv1 hv0
      _ = v := by ring
  have huSq : u ^ 2 ≤ (9 / 16 : ℝ) := by
    calc
      u ^ 2 = u * u := by ring
      _ ≤ u * (3 / 4) := mul_le_mul_of_nonneg_left hu34 hu0
      _ ≤ (3 / 4) * (3 / 4) := mul_le_mul_of_nonneg_right hu34 (by norm_num)
      _ = 9 / 16 := by norm_num
  have hmodel :
      rankRoundingModel u v =
        (u / 2 - u ^ 2 / 2 + u ^ 3 / 3) + v * (u ^ 2 / 2 + 1 / 2) +
          v ^ 2 * (u / 6 + 1 / 2) := by
    unfold rankRoundingModel
    ring
  rw [hmodel]
  have hcoef1 : u ^ 2 / 2 + 1 / 2 ≤ 25 / 32 := by
    calc
      u ^ 2 / 2 + 1 / 2 ≤ (9 / 16 : ℝ) / 2 + 1 / 2 := by gcongr
      _ = 25 / 32 := by norm_num
  have hcoef2 : u / 6 + 1 / 2 ≤ 5 / 8 := by
    calc
      u / 6 + 1 / 2 ≤ (3 / 4 : ℝ) / 6 + 1 / 2 := by gcongr
      _ = 5 / 8 := by norm_num
  have hround : v * (u ^ 2 / 2 + 1 / 2) + v ^ 2 * (u / 6 + 1 / 2) ≤ 3 * v := by
    calc
      v * (u ^ 2 / 2 + 1 / 2) + v ^ 2 * (u / 6 + 1 / 2) ≤
          v * (25 / 32) + v ^ 2 * (5 / 8) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hcoef1 hv0)
          (mul_le_mul_of_nonneg_left hcoef2 (sq_nonneg v))
      _ ≤ v * (25 / 32) + v * (5 / 8) := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hvSq
          (by norm_num : (0 : ℝ) ≤ 5 / 8))
      _ = (45 / 32 : ℝ) * v := by ring
      _ ≤ 3 * v := mul_le_mul_of_nonneg_right (by norm_num) hv0
  calc
    (u / 2 - u ^ 2 / 2 + u ^ 3 / 3) + v * (u ^ 2 / 2 + 1 / 2) +
        v ^ 2 * (u / 6 + 1 / 2) =
      (u / 2 - u ^ 2 / 2 + u ^ 3 / 3) +
        (v * (u ^ 2 / 2 + 1 / 2) + v ^ 2 * (u / 6 + 1 / 2)) := by ring
    _ ≤ beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 + 3 * v := add_le_add hP hround

private theorem cubicUpperCount_div_cube_eq_model {m M : ℕ} (hm : 0 < m) (hM : M ≤ m) :
    firstOrderRankCubicUpperCount m M / (m : ℝ) ^ 3 =
      rankRoundingModel ((M : ℝ) / m) ((m : ℝ)⁻¹) := by
  have hamb (n : ℕ) :
      (∑ s ∈ range n, ((s + 1 : ℕ) : ℝ) * (M + 1)) = (M + 1) * (linearSum n + n) := by
    rw [← sum_range_natCast_eq_linearSum, ← sum_mul]
    simp only [Nat.cast_add, Nat.cast_one, sum_add_distrib, sum_const, card_range,
      nsmul_eq_mul, mul_one]
    ring
  have hcorrection (n : ℕ) :
      (∑ s ∈ range n, (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)) =
        2 * squareSum n + (2 * M + 3 - 3 * m) * linearSum n + n * (1 - m) * (M + 1 - m) := by
    calc
      _ = ∑ s ∈ range n,
          (2 * (s : ℝ) ^ 2 + (2 * M + 3 - 3 * m) * s + (1 - m) * (M + 1 - m)) := by
        refine sum_congr rfl fun s _ => ?_
        push_cast
        ring
      _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
          sum_range_natCast_eq_linearSum, sum_range_natCast_sq_eq_squareSum]
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
  rw [firstOrderRankCubicUpperCount, sum_Ico_eq_sub _ (Nat.sub_le m M), hamb, hcorrection,
    hcorrection, Nat.cast_sub hM]
  simp only [linearSum, squareSum, rankRoundingModel]
  field_simp
  ring

/-- Rounding the `Y₁`-degree cap to `M = ⌊β m⌋₊` costs at most `3 m²` against the cubic envelope:
`r(m, ⌊β m⌋₊) ≤ m³ (β/2 - β²/2 + β³/3) + 3 m²` for `0 ≤ β ≤ 3/4`. -/
theorem firstOrderRankCount_floor_le {beta : ℝ} (m : ℕ) (hb0 : 0 ≤ beta)
    (hb34 : beta ≤ 3 / 4) :
    (firstOrderRankCount m ⌊beta * m⌋₊ : ℝ) ≤
      m ^ 3 * (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3) + 3 * m ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [firstOrderRankCount]
  set M := ⌊beta * m⌋₊ with hMdef
  set u : ℝ := M / m with hu
  set v : ℝ := (m : ℝ)⁻¹ with hv
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hMReal : (M : ℝ) ≤ beta * m := Nat.floor_le (by positivity)
  have hMlt : beta * m < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMNat : M ≤ m := by
    have : (M : ℝ) ≤ m := by nlinarith
    exact_mod_cast this
  have hu0 : 0 ≤ u := by positivity
  have hub : u ≤ beta := (div_le_iff₀ hmR).2 hMReal
  have hbu : beta ≤ u + v := by
    rw [hu, hv, show (M : ℝ) / m + (m : ℝ)⁻¹ = ((M : ℝ) + 1) / m by field_simp]
    exact (le_div_iff₀ hmR).2 hMlt.le
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hm)
  have hmodel := rankRoundingModel_le hu0 hub hv0 hv1 hb34
  rw [← cubicUpperCount_div_cube_eq_model hm hMNat, div_le_iff₀ (by positivity)] at hmodel
  calc
    (firstOrderRankCount m M : ℝ) ≤ firstOrderRankCubicUpperCount m M :=
      firstOrderRankCount_le_cubicUpperCount m M
    _ ≤ (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 + 3 * v) * m ^ 3 := hmodel
    _ = m ^ 3 * (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3) + 3 * m ^ 2 := by
      rw [hv]
      field_simp

/-! ## The source rounding estimate -/

/-- The sum `∑_{t < L} (min t M) (m a - R t)`, without positive parts. -/
private def sourcePolynomialCount (rate agreement : ℝ) (m M L : ℕ) : ℝ :=
  ∑ t ∈ range L, (min t M : ℕ) * (m * agreement - rate * t)

/-- `sourcePolynomialCount` divided by `m³` at agreement `R (z + 1/m)`, written in `u = M / m`,
`c = L / m`, and `v = 1 / m`. -/
private def sourceRoundingModel (z u c v : ℝ) : ℝ :=
  (z + v) * u * (u - v) / 2 - u * (u - v) * (2 * u - v) / 6 +
    u * ((z + v) * (c - u) - (c * (c - v) - u * (u - v)) / 2)

private theorem sourceRoundingModel_ge {z u c v beta : ℝ} (hz1 : 1 ≤ z) (hbz : beta ≤ z)
    (hbu : beta ≤ u) (hub : u ≤ beta + v) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hzc : z + v ≤ c) (hcz : c ≤ z + 2 * v) :
    beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤ sourceRoundingModel z u c v := by
  have hconcave : sourceRoundingModel z u (z + v) v ≤ sourceRoundingModel z u c v := by
    have hid : sourceRoundingModel z u c v - sourceRoundingModel z u (z + v) v =
        u / 2 * (c - (z + v)) * (z + 2 * v - c) := by
      unfold sourceRoundingModel
      ring
    rw [← sub_nonneg, hid]
    have : 0 ≤ c - (z + v) := by linarith
    have : 0 ≤ z + 2 * v - c := by linarith
    positivity
  have hquad : 0 ≤ (u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2 := by
    have hquad_eq :
        (u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2 =
          ((u - z) + (beta - z)) ^ 2 / 2 + (u - z) ^ 2 / 2 + (beta - z) ^ 2 / 2 := by ring
    rw [hquad_eq]
    positivity
  have hbase : beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
      u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6 := by
    have hid :
        (u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6) -
            (beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6) =
          (u - beta) / 6 * ((u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2) := by
      ring
    have hfac : 0 ≤ (u - beta) / 6 := div_nonneg (sub_nonneg.mpr hbu) (by norm_num)
    rw [← sub_nonneg, hid]
    exact mul_nonneg hfac hquad
  have hbracket : 0 ≤ z - u / 2 + v / 3 := by nlinarith
  have hround : 0 ≤ v * u * (z - u / 2 + v / 3) := by positivity
  have hid : sourceRoundingModel z u (z + v) v =
      (u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6) + v * u * (z - u / 2 + v / 3) := by
    unfold sourceRoundingModel
    ring
  linarith

private theorem sourcePolynomialCount_div_cube_eq_model {rate z : ℝ} {m M L : ℕ} (hm : 0 < m)
    (hML : M ≤ L) :
    sourcePolynomialCount rate (rate * (z + (m : ℝ)⁻¹)) m M L / (m : ℝ) ^ 3 =
      rate * sourceRoundingModel z ((M : ℝ) / m) ((L : ℝ) / m) ((m : ℝ)⁻¹) := by
  set a := rate * (z + (m : ℝ)⁻¹)
  have hsum (n : ℕ) :
      (∑ t ∈ range n, ((m : ℝ) * a - rate * t)) = n * (m * a) - rate * linearSum n := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum,
      sum_range_natCast_eq_linearSum]
  have hsplit : sourcePolynomialCount rate a m M L =
      a * m * linearSum M - rate * squareSum M +
        M * (a * m * (L - M) - rate * (linearSum L - linearSum M)) := by
    rw [sourcePolynomialCount, ← sum_range_add_sum_Ico _ hML]
    have hfirst : (∑ t ∈ range M, (min t M : ℕ) * (m * a - rate * t)) =
        a * m * linearSum M - rate * squareSum M := by
      calc
        _ = ∑ t ∈ range M, (a * m * (t : ℝ) - rate * (t : ℝ) ^ 2) := by
          refine sum_congr rfl fun t ht => ?_
          rw [min_eq_left (mem_range.mp ht).le]
          ring
        _ = _ := by
          rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_range_natCast_eq_linearSum,
            sum_range_natCast_sq_eq_squareSum]
    have htail : (∑ t ∈ Ico M L, (min t M : ℕ) * (m * a - rate * t)) =
        M * (a * m * (L - M) - rate * (linearSum L - linearSum M)) := by
      calc
        _ = ∑ t ∈ Ico M L, ((M : ℝ) * (m * a - rate * t)) := by
          refine sum_congr rfl fun t ht => ?_
          rw [min_eq_right (mem_Ico.mp ht).1]
        _ = _ := by
          rw [← mul_sum, sum_Ico_eq_sub _ hML, hsum, hsum]
          ring
    rw [hfirst, htail]
  rw [hsplit]
  simp only [a, linearSum, squareSum, sourceRoundingModel]
  field_simp

private theorem sourcePolynomialCount_shift_eq {rate a : ℝ} {m M L : ℕ} (hm : 0 < m) :
    sourcePolynomialCount rate (a + rate / m) m (M + 1) (L + 2) =
      ∑ t ∈ range (L + 1), (min t M + 1 : ℕ) * (m * a - rate * t) := by
  rw [sourcePolynomialCount, sum_range_succ']
  rw [show min 0 (M + 1) = 0 by omega]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine sum_congr rfl fun t _ => ?_
  rw [show min (t + 1) (M + 1) = min t M + 1 by omega]
  have : (m : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Rounding the caps to `M = ⌊β m⌋₊` and `μ ≥ ⌊m a / R⌋₊` loses nothing against the source
density: `m³ (β a²/(2R) - a β²/2 + R β³/6) ≤ N₀(R, a, m, M, μ)` for `0 < R ≤ a`
and `0 ≤ β ≤ a / R`. -/
theorem cube_mul_sourceDensity_le_firstOrderSourceCount {rate a beta : ℝ} {m mu : ℕ}
    (hrate : 0 < rate) (hra : rate ≤ a) (hb0 : 0 ≤ beta) (hba : beta ≤ a / rate)
    (hmu : ⌊m * a / rate⌋₊ ≤ mu) :
    (m : ℝ) ^ 3 * (beta * a ^ 2 / (2 * rate) - a * beta ^ 2 / 2 + rate * beta ^ 3 / 6) ≤
      firstOrderSourceCount rate a m ⌊beta * m⌋₊ mu := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero, zero_pow three_ne_zero, zero_mul]
    exact sum_nonneg fun t _ => by positivity
  set M := ⌊beta * m⌋₊ with hMdef
  set L := ⌊m * a / rate⌋₊ with hLdef
  set z := a / rate with hz
  set u : ℝ := ((M + 1 : ℕ) : ℝ) / m with hu
  set c : ℝ := ((L + 2 : ℕ) : ℝ) / m with hc
  set v : ℝ := (m : ℝ)⁻¹ with hv
  set Q : ℝ := ∑ t ∈ range (L + 1), (min t M + 1 : ℕ) * (m * a - rate * t) with hQ
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  have ha0 : 0 < a := hrate.trans_le hra
  have hMReal : (M : ℝ) ≤ beta * m := Nat.floor_le (by positivity)
  have hMlt : beta * m < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcut : beta * m ≤ m * a / rate := by
    calc
      beta * m ≤ a / rate * m := mul_le_mul_of_nonneg_right hba hmR.le
      _ = m * a / rate := by ring
  have hML : M ≤ L := Nat.floor_le_floor hcut
  have hLReal : (L : ℝ) ≤ m * a / rate := Nat.floor_le (by positivity)
  have hLlt : (m : ℝ) * a / rate < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hQle : Q ≤ firstOrderSourceCount rate a m M mu := by
    rw [firstOrderSourceCount]
    calc
      Q = ∑ t ∈ range (L + 1), (min t M + 1 : ℕ) * max (m * a - rate * t) 0 := by
        refine sum_congr rfl fun t ht => ?_
        rw [max_eq_left]
        have htL : (t : ℝ) ≤ L := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp ht)
        have h1 : (t : ℝ) ≤ m * a / rate := htL.trans hLReal
        rw [le_div_iff₀ hrate] at h1
        linarith
      _ ≤ ∑ t ∈ range (mu + 1), (min t M + 1 : ℕ) * max (m * a - rate * t) 0 := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact range_subset_range.mpr (by omega)
        · exact fun t _ _ => by positivity
  have harg : rate * (z + (m : ℝ)⁻¹) = a + rate / m := by
    rw [hz]
    field_simp
  have hnormalized : Q / (m : ℝ) ^ 3 = rate * sourceRoundingModel z u c v := by
    have h := sourcePolynomialCount_div_cube_eq_model (rate := rate) (z := z) (M := M + 1)
      (L := L + 2) hm (by omega)
    rw [harg, sourcePolynomialCount_shift_eq hm] at h
    rw [← hQ] at h
    rw [h, hu, hc, hv]
  have hz1 : 1 ≤ z := (le_div_iff₀ hrate).2 (by linarith)
  have hbu : beta ≤ u := by
    rw [hu, le_div_iff₀ hmR]
    push_cast
    linarith
  have hub : u ≤ beta + v := by
    rw [hu, hv, show beta + (m : ℝ)⁻¹ = (beta * m + 1) / m by field_simp,
      div_le_div_iff_of_pos_right hmR]
    push_cast
    linarith
  have hu0 : 0 ≤ u := by positivity
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hm)
  have hzc : z + v ≤ c := by
    rw [hz, hv, hc, le_div_iff₀ hmR,
      show (a / rate + (m : ℝ)⁻¹) * m = m * a / rate + 1 by field_simp]
    push_cast
    linarith
  have hcz : c ≤ z + 2 * v := by
    rw [hz, hv, hc, div_le_iff₀ hmR,
      show (a / rate + 2 * (m : ℝ)⁻¹) * m = m * a / rate + 2 by field_simp]
    push_cast
    linarith
  have hmodel := sourceRoundingModel_ge hz1 hba hbu hub hu0 hv0 hv1 hzc hcz
  have hdensity : beta * a ^ 2 / (2 * rate) - a * beta ^ 2 / 2 + rate * beta ^ 3 / 6 =
      rate * (beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6) := by
    rw [hz]
    field_simp
  have hnorm : beta * a ^ 2 / (2 * rate) - a * beta ^ 2 / 2 + rate * beta ^ 3 / 6 ≤
      Q / (m : ℝ) ^ 3 := by
    rw [hdensity, hnormalized]
    exact mul_le_mul_of_nonneg_left hmodel hrate.le
  rw [le_div_iff₀ (by positivity)] at hnorm
  linarith

/-- The finite source-minus-rank surplus at the rounded caps `M = ⌊β m⌋₊` and
`μ ≥ ⌊m a / R⌋₊` is at least `m³ S - 3 m²`, where
`S = (β a²/(2R) - a β²/2 + R β³/6) - (β/2 - β²/2 + β³/3)` is the continuous density gap. -/
theorem cube_mul_densityGap_sub_le_sourceCount_sub_rankCount {rate a beta : ℝ} {m mu : ℕ}
    (hrate : 0 < rate) (hra : rate ≤ a) (hb0 : 0 ≤ beta) (hb34 : beta ≤ 3 / 4)
    (hba : beta ≤ a / rate) (hmu : ⌊m * a / rate⌋₊ ≤ mu) :
    (m : ℝ) ^ 3 * ((beta * a ^ 2 / (2 * rate) - a * beta ^ 2 / 2 + rate * beta ^ 3 / 6) -
        (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3)) - 3 * m ^ 2 ≤
      firstOrderSourceCount rate a m ⌊beta * m⌋₊ mu -
        firstOrderRankCount m ⌊beta * m⌋₊ := by
  have hsource := cube_mul_sourceDensity_le_firstOrderSourceCount hrate hra hb0 hba hmu
  have hrank := firstOrderRankCount_floor_le m hb0 hb34
  linarith

/-! ## Consumers of a finite surplus -/

/-- A real source residual is dominated by the residual of a code of degree `D` and agreement
`A`: if `D ≤ R n` and `a n ≤ A`, then `n · max (m a - R t) 0 ≤ max (m A - D t) 0`. -/
theorem mul_max_rateResidual_le_max_residual {rate a : ℝ} {n D A m t : ℕ}
    (hD : (D : ℝ) ≤ rate * n) (hA : a * n ≤ A) :
    n * max (m * a - rate * t) 0 ≤ max ((m : ℝ) * A - D * t) 0 := by
  rcases le_total 0 ((m : ℝ) * a - rate * t) with hx | hx
  · rw [max_eq_left hx]
    refine le_trans ?_ (le_max_left _ _)
    have hm : 0 ≤ (m : ℝ) * ((A : ℝ) - a * n) :=
      mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr hA)
    have ht : 0 ≤ (t : ℝ) * (rate * n - D) :=
      mul_nonneg (Nat.cast_nonneg t) (sub_nonneg.mpr hD)
    nlinarith
  · rw [max_eq_right hx, mul_zero]
    exact le_max_right _ _

/-- The scaled kernel-height quotient is bounded uniformly in the scale: if `r < N₀` and
`n N₀ ≤ N`, then `n r μ / (N - n r) ≤ ⌊r μ / (N₀ - r)⌋₊` (natural division on the left). -/
theorem scaledKernelHeight_le_floor {n N r mu : ℕ} {N₀ : ℝ} (hsurplus : (r : ℝ) < N₀)
    (hN : n * N₀ ≤ N) :
    n * r * mu / (N - n * r) ≤ ⌊(r : ℝ) * mu / (N₀ - r)⌋₊ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnrN : n * r < N := by
    have : ((n * r : ℕ) : ℝ) < N := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hgap : 0 < N₀ - r := sub_pos.mpr hsurplus
  have hden : (n : ℝ) * (N₀ - r) ≤ ((N - n * r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnrN.le]
    push_cast
    nlinarith
  have hfrac : ((n * r * mu : ℕ) : ℝ) / ((N - n * r : ℕ) : ℝ) ≤ (r : ℝ) * mu / (N₀ - r) :=
    calc
      ((n * r * mu : ℕ) : ℝ) / ((N - n * r : ℕ) : ℝ) ≤
          ((n : ℝ) * ((r : ℝ) * mu)) / ((n : ℝ) * (N₀ - r)) := by
        rw [show ((n * r * mu : ℕ) : ℝ) = (n : ℝ) * (r * mu) by push_cast; ring]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = (r : ℝ) * mu / (N₀ - r) := mul_div_mul_left _ _ hnR.ne'
  exact Nat.le_floor ((Nat.cast_div_le).trans hfrac)

end

end ReedSolomon.HiddenDerivative
