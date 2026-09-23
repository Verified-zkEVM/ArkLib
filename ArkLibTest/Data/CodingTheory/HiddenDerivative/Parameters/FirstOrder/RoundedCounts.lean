/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts

/-!
# Acceptance tests for the rounded first-order counts

Concrete values of the source and rank counts, the identification with the certified rank bound
at derivative order one, the rounding estimates at a concrete parameter set, cases showing that
the remaining hypotheses are needed, and the forms of the finite-surplus consumers with a
`max 1` height and a degree `D = k - 1`.
-/

open Finset

namespace ReedSolomon.HiddenDerivative

/-! ### Concrete counts -/

/-- `r(2, 1) = 2 + 3 = 5`. -/
private theorem test_rankCount_two_one : firstOrderRankCount 2 1 = 5 := by
  decide

/-- The certified rank bound at order one and multiplicity `2`, cap `1`, is `5` at every weight. -/
example (W : ℕ) : certifiedEnlargedRankBound 1 2 1 W = 5 := by
  rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount, test_rankCount_two_one]

/-- `r(4, 2) = 3 + 6 + 8 + 6 = 23`. -/
private theorem test_rankCount_four_two : firstOrderRankCount 4 2 = 23 := by
  decide

/-- `N₀(1/2, 1, 2, 1, 4) = 2 + 3 + 2 + 1 + 0 = 8`. -/
private theorem test_sourceCount : firstOrderSourceCount (1 / 2) 1 2 1 4 = 8 := by
  norm_num [firstOrderSourceCount, sum_range_succ]

/-! ### The rounding estimates at a concrete parameter set -/

/-- At `m = 4` and `β = 1/2` the cap is `M = 2`, and the rank estimate reads
`23 ≤ 64 · (1/4 - 1/8 + 1/24) + 48`. -/
example : ((23 : ℕ) : ℝ) ≤ (4 : ℕ) ^ 3 * ((1 / 2 : ℝ) / 2 - (1 / 2) ^ 2 / 2 + (1 / 2) ^ 3 / 3) +
    3 * (4 : ℕ) ^ 2 := by
  have h := firstOrderRankCount_floor_le (beta := 1 / 2) 4 (by norm_num) (by norm_num)
  have hM : ⌊(1 / 2 : ℝ) * (4 : ℕ)⌋₊ = 2 := by norm_num
  rwa [hM, test_rankCount_four_two] at h

/-- The exact-density estimate uses the linear density branch above `β = 1/2`. -/
example : ((35 : ℕ) : ℝ) ≤
    (4 : ℕ) ^ 3 * firstOrderRankDensity 1 + (2 * 1 + 3) * (4 : ℕ) ^ 2 := by
  have h := firstOrderRankCount_floor_le_density_add_rounding_upper
    (beta := 1) (by norm_num) 4
  have hM : ⌊(1 : ℝ) * (4 : ℕ)⌋₊ = 4 := by norm_num
  have hcount : firstOrderRankCount 4 4 = 35 := by decide
  rw [hM, hcount] at h
  norm_num [firstOrderRankDensity] at h ⊢

/-- At the branch boundary, the uniform estimate uses the cubic density and exact cap `M = 2`. -/
example : ((23 : ℕ) : ℝ) ≤
    (4 : ℕ) ^ 3 * firstOrderRankDensity (1 / 2) + (2 * (1 / 2) + 3) * (4 : ℕ) ^ 2 := by
  have h := firstOrderRankCount_floor_le_density_add_rounding
    (beta := 1 / 2) (by norm_num) 4
  have hM : ⌊(1 / 2 : ℝ) * (4 : ℕ)⌋₊ = 2 := by norm_num
  rw [hM, test_rankCount_four_two] at h
  norm_num [firstOrderRankDensity] at h ⊢

/-- At `R = 1/2`, `a = 1`, `m = 2`, `β = 1/2` the caps are `M = 1` and `μ = ⌊4⌋₊ = 4`, and the
source estimate reads `8 · (1/4 - 1/8 + 1/96) ≤ 8`. -/
example : ((2 : ℕ) : ℝ) ^ 3 * ((1 / 2) * 1 ^ 2 / (2 * (1 / 2)) - 1 * (1 / 2) ^ 2 / 2 +
    (1 / 2) * (1 / 2) ^ 3 / 6) ≤ 8 := by
  have h := cube_mul_sourceDensity_le_firstOrderSourceCount (rate := 1 / 2) (a := 1)
    (beta := 1 / 2) (m := 2) (mu := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hM : ⌊(1 / 2 : ℝ) * (2 : ℕ)⌋₊ = 1 := by norm_num
  rwa [hM, test_sourceCount] at h

/-- The density estimate at the rounded ceiling total-degree cap. -/
private theorem density_bound_at_ceiling {rate agreement beta : ℝ} {m : ℕ}
    (hrate : 0 < rate) (hAgreement : rate ≤ agreement) (hbeta0 : 0 ≤ beta)
    (hbeta : beta < agreement / rate) :
    (m : ℝ) ^ 3 * firstOrderSourceDensity rate agreement beta ≤
      firstOrderSourceCount rate agreement m (Nat.floor (beta * m))
        (Nat.ceil (m * agreement / rate)) := by
  have h := cube_mul_sourceDensity_le_firstOrderSourceCount (rate := rate)
    (a := agreement) (beta := beta) (m := m)
    (mu := Nat.ceil (m * agreement / rate)) hrate hAgreement hbeta0 hbeta.le
    (Nat.floor_le_ceil _)
  simpa [firstOrderSourceDensity] using h

/-! ### Boundary hypotheses -/

/-- `firstOrderRankCount_floor_le` needs `0 ≤ β`: at `β = -3`, `m = 1` the cap is `0`, the rank
count is `1`, and the right side is `-3/2 - 9/2 - 9 + 3 = -12`. -/
example : ⌊(-3 : ℝ) * (1 : ℕ)⌋₊ = 0 ∧ firstOrderRankCount 1 0 = 1 ∧
    ¬ ((1 : ℝ) ≤ (1 : ℕ) ^ 3 * ((-3 : ℝ) / 2 - (-3) ^ 2 / 2 + (-3) ^ 3 / 3) + 3 * (1 : ℕ) ^ 2) := by
  refine ⟨by norm_num, by decide, by norm_num⟩

/-- The exact-density estimate needs `0 ≤ β`: at `β = -3`, the count is `1` and its bound is
negative. -/
example : ⌊(-3 : ℝ) * (1 : ℕ)⌋₊ = 0 ∧ firstOrderRankCount 1 0 = 1 ∧
    ¬ ((1 : ℝ) ≤ (1 : ℕ) ^ 3 * firstOrderRankDensity (-3) +
      (2 * (-3) + 3) * (1 : ℕ) ^ 2) := by
  refine ⟨by norm_num, by decide, ?_⟩
  norm_num [firstOrderRankDensity]

/-- `cube_mul_sourceDensity_le_firstOrderSourceCount` needs `β ≤ a / R`: at `R = a = 1`,
`β = 10`, `m = 1`, `μ = 1` the source count is `1` and the left side is `5 - 50 + 1000/6`. -/
example : firstOrderSourceCount 1 1 1 ⌊(10 : ℝ) * (1 : ℕ)⌋₊ 1 = 1 ∧
    ¬ (((1 : ℕ) : ℝ) ^ 3 * (10 * 1 ^ 2 / (2 * 1) - 1 * 10 ^ 2 / 2 + 1 * 10 ^ 3 / 6) ≤ 1) := by
  refine ⟨?_, by norm_num⟩
  norm_num [firstOrderSourceCount, sum_range_succ]

/-- `cube_mul_sourceDensity_le_firstOrderSourceCount` needs `⌊m a / R⌋₊ ≤ μ`: at `R = a = β = 1`,
`m = 4`, `μ = 0` the source count is `4` and the left side is `64 / 6`. -/
example : firstOrderSourceCount 1 1 4 ⌊(1 : ℝ) * (4 : ℕ)⌋₊ 0 = 4 ∧
    ¬ (((4 : ℕ) : ℝ) ^ 3 * (1 * 1 ^ 2 / (2 * 1) - 1 * 1 ^ 2 / 2 + 1 * 1 ^ 3 / 6) ≤ 4) := by
  refine ⟨?_, by norm_num⟩
  norm_num [firstOrderSourceCount]

/-- `scaledKernelHeight_le_floor` needs `r < N₀`: at `n = r = μ = 1`, `N₀ = 1`, `N = 2` the left
side is `1 / 1 = 1` and the right side is `⌊1 / 0⌋₊ = 0`. -/
example : 1 * 1 * 1 / (2 - 1 * 1) = 1 ∧ ⌊((1 : ℕ) : ℝ) * (1 : ℕ) / (1 - (1 : ℕ))⌋₊ = 0 := by
  norm_num

/-! ### Forms used by the parameter recipes -/

/-- The height bound with the challenge height `max 1 ⌊r μ / (N₀ - r)⌋₊` on the right. -/
example {n N r mu : ℕ} {N₀ : ℝ} (hsurplus : (r : ℝ) < N₀) (hN : n * N₀ ≤ N) :
    n * r * mu / (N - n * r) ≤ max 1 ⌊(r : ℝ) * mu / (N₀ - r)⌋₊ :=
  (scaledKernelHeight_le_floor hsurplus hN).trans (le_max_right _ _)

/-- The residual comparison for a Reed–Solomon code of dimension `k ≤ R n`, whose degree is
`D = k - 1`. -/
example {rate a : ℝ} {n k D A m t : ℕ} (hD : D = k - 1) (hk : (k : ℝ) ≤ rate * n)
    (hA : a * n ≤ A) :
    n * max (m * a - rate * t) 0 ≤ max ((m : ℝ) * A - D * t) 0 :=
  mul_max_rateResidual_le_max_residual
    (hD ▸ (Nat.cast_le.mpr (Nat.sub_le k 1)).trans hk) hA

/-- The finite surplus is positive once `m S > 3` for the density gap `S`. -/
example {rate a beta : ℝ} {m mu : ℕ} (hrate : 0 < rate) (hra : rate ≤ a) (hb0 : 0 ≤ beta)
    (hb34 : beta ≤ 3 / 4) (hba : beta ≤ a / rate) (hmu : ⌊m * a / rate⌋₊ ≤ mu)
    (hS : 3 < m * ((beta * a ^ 2 / (2 * rate) - a * beta ^ 2 / 2 + rate * beta ^ 3 / 6) -
      (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3))) :
    (firstOrderRankCount m ⌊beta * m⌋₊ : ℝ) < firstOrderSourceCount rate a m ⌊beta * m⌋₊ mu := by
  have h := cube_mul_densityGap_sub_le_sourceCount_sub_rankCount hrate hra hb0 hb34 hba hmu
  have hm : (0 : ℝ) < m := by
    by_contra h0
    have : (m : ℝ) = 0 := le_antisymm (not_lt.mp h0) (Nat.cast_nonneg m)
    rw [this, zero_mul] at hS
    norm_num at hS
  have hpos : 0 < (m : ℝ) ^ 3 * ((beta * a ^ 2 / (2 * rate) - a * beta ^ 2 / 2 +
      rate * beta ^ 3 / 6) - (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3)) - 3 * m ^ 2 := by
    have : (m : ℝ) ^ 2 * 3 < (m : ℝ) ^ 2 * (m * ((beta * a ^ 2 / (2 * rate) -
        a * beta ^ 2 / 2 + rate * beta ^ 3 / 6) - (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3))) :=
      mul_lt_mul_of_pos_left hS (by positivity)
    nlinarith
  linarith

end ReedSolomon.HiddenDerivative
