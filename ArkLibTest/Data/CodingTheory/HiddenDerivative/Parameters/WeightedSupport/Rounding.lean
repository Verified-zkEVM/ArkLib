/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Rounding

/-!
# Acceptance cases for the weighted-support rounding parameters

A concrete instance of `Nat.one_sub_one_div_mul_lt_floor` and the cases showing that `N ≤ R` is
needed there, that `0 ≤ a` is needed in `floorRadius_mul_div_le`, and that `1 ≤ N` is needed in
`floorRadius_sq_ge`; and `floorRadius_sq_ge`, `remainingDegree_lower`,
`remainingDegree_upper`, `enlargedRadius_upper`, `enlargedRadius_normalized` and
`residualVariance_le` at the prescribed constants, derived from the general statements.
-/

open ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-! ### The relative floor error -/

/-- At `N = 2`, `R = 5 / 2`: `(1 - 1 / 2) (5 / 2) = 5 / 4 < 2 = ⌊5 / 2⌋₊`. -/
example : (1 - 1 / 2 : ℝ) * (5 / 2) < ⌊(5 / 2 : ℝ)⌋₊ :=
  Nat.one_sub_one_div_mul_lt_floor (by norm_num) (by norm_num)

/-- `N ≤ R` is needed: at `N = 2`, `R = 1 / 2` the floor is `0` and `(1 - 1 / 2) (1 / 2) > 0`. -/
example : ¬ ((1 - 1 / 2 : ℝ) * (1 / 2) < ⌊(1 / 2 : ℝ)⌋₊) := by
  rw [Nat.floor_eq_zero.mpr (by norm_num)]
  norm_num

/-! ### The hypotheses of the floor bounds are needed -/

/-- `0 ≤ a` is needed in `floorRadius_mul_div_le`: at `a = -1`, `H = d = m = 1` the floor is `0`
while `a m = -1`. -/
example : ¬ ((⌊(-1 : ℝ) * (1 : ℕ) * (1 : ℕ) / 1⌋₊ : ℝ) * 1 / (1 : ℕ) ≤ -1 * (1 : ℕ)) := by
  rw [Nat.floor_eq_zero.mpr (by norm_num)]
  norm_num

/-- `1 ≤ N` is needed in `floorRadius_sq_ge`: at `N = 1 / 10`, `a = g = 1`, `H = 10`,
`d = m = 1` the unrounded radius is `1 / 10 = N`, its floor is `0`, but
`(1 - 10) ^ 2 (1 / 10) ^ 2 = 81 / 100 > 0`. -/
example : ¬ ((1 - 1 / (1 / 10)) ^ 2 * ((1 : ℝ) / (1 * 10)) ^ 2 ≤
    ((⌊(1 : ℝ) * (1 : ℕ) * (1 : ℕ) / 10⌋₊ : ℝ) / ((1 : ℕ) * 1 * (1 : ℕ))) ^ 2) := by
  rw [Nat.floor_eq_zero.mpr (by norm_num)]
  norm_num

/-! ### Specializations at the prescribed constants -/

/-- `floorRadius_sq_ge` at `N = 2000`, weakened by `(1999 / 2000) ^ 2 ≥ 999 / 1000`, with an
unused hypothesis `0 < a`. -/
example (a g H : ℝ) (d m : ℕ)
    (_ha : 0 < a) (hg : 0 < g) (hH : 0 < H) (hd : 0 < d) (hm : 0 < m)
    (hR : 2000 ≤ a * d * m / H) :
    (999 / 1000) * (a / (g * H)) ^ 2 ≤
      ((Nat.floor (a * d * m / H) : ℝ) / (d * g * m)) ^ 2 := by
  have h := floorRadius_sq_ge 2000 a g H d m (by norm_num) hg hH hd hm hR
  have hc : (999 / 1000 : ℝ) ≤ (1 - 1 / 2000) ^ 2 := by norm_num
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans h

/-- `remainingDegree_lower` at `θ = 3 / 8` and `ε = 2 / 1000`. -/
example (d m r W : ℕ) (g H : ℝ)
    (_hd : 0 < d) (_hm : 0 < m) (hr : r < m) (hg : 0 < g) (hH : 0 < H)
    (hW : W = Nat.floor ((1 + theta * g) * d * m / H))
    (herror : (m : ℝ) * H / d + d.choose 2 * H / d ≤
      (2 / 1000) * residualFraction * g * m) :
    residualFraction * g * m * (998 / 1000) ≤
      (m : ℝ) * (1 + g) + (d - 1 : ℕ) -
        (W + r + d.choose 2 : ℕ) * H / d := by
  have h := remainingDegree_lower theta (2 / 1000) g H d m r W hr
    (add_nonneg zero_le_one (mul_nonneg theta_pos.le hg.le)) hH.le hW herror
  have e : residualFraction * g * m * (998 / 1000) = (1 - theta) * g * m * (1 - 2 / 1000) := by
    rw [residualFraction]
    ring
  rw [e]
  exact h

/-- `remainingDegree_upper` at `θ = 3 / 8` and `ε = 1 / 1000`. -/
example (d m r W : ℕ) (g H : ℝ)
    (hd : 0 < d) (_hm : 0 < m) (_hg : 0 < g) (hH : 0 < H)
    (hW : W = Nat.floor ((1 + theta * g) * d * m / H))
    (herror : (d : ℝ) + H / d ≤
      (1 / 1000) * residualFraction * g * m) :
    (m : ℝ) * (1 + g) + (d - 1 : ℕ) -
        (W + r + d.choose 2 : ℕ) * H / d ≤
      residualFraction * g * m * (1001 / 1000) := by
  have h := remainingDegree_upper theta (1 / 1000) g H d m r W hd hH hW herror
  have e : residualFraction * g * m * (1001 / 1000) = (1 - theta) * g * m * (1 + 1 / 1000) := by
    rw [residualFraction]
    ring
  rw [e]
  exact h

/-- `enlargedRadius_upper` at `θ = 3 / 8` and `ε = 1 / 1000`. -/
example (d m r W : ℕ) (g H : ℝ)
    (hd : 0 < d) (_hm : 0 < m) (hr : r < m) (hg : 0 < g) (hH : 0 < H)
    (hW : W = Nat.floor ((1 + theta * g) * d * m / H))
    (herror : (m : ℝ) + d.choose 2 ≤
      (1 / 1000) * ((1 + theta * g) * d * m / H)) :
    ((W + r + d.choose 2 : ℕ) : ℝ) / d ≤
      ((1 + theta * g) * m / H) * (1001 / 1000) := by
  have h := enlargedRadius_upper theta (1 / 1000) g H d m r W hd hr
    (add_nonneg zero_le_one (mul_nonneg theta_pos.le hg.le)) hH hW herror
  norm_num at h ⊢
  exact h

/-- `enlargedRadius_normalized` at `a = 1 + θ g`, `ξ = 27 / 10`, `c = 1001 / 1000`. -/
example (d m W' : ℝ) (g H : ℝ)
    (_hd : 0 < d) (hm : 0 ≤ m) (hg : 0 < g) (hH : 0 < H)
    (hradius : W' / d ≤ ((1 + theta * g) * m / H) * (1001 / 1000))
    (ha : (1 + theta * g) / (g * H) ≤ 1 / xi) :
    W' / d ≤ g * m / xi * (1001 / 1000) :=
  enlargedRadius_normalized d m W' _ g H xi _ hm hg hH (by norm_num) hradius ha

/-- `residualVariance_le` at `ξ = 27 / 10`, `c = 1001 / 1000`, `h = 329 / 200`, with an unused
hypothesis `0 ≤ q`. -/
example (d W' H2 q : ℝ)
    (hd : 0 < d) (hW' : 0 ≤ W') (hH2 : 0 ≤ H2) (_hq : 0 ≤ q)
    (hradius : W' / d ≤ q / xi * (1001 / 1000))
    (hH2max : H2 ≤ 329 / 200) :
    W' ^ 2 * H2 / (d * (d + 1)) ≤
      q ^ 2 * (1001 / 1000) ^ 2 / xi ^ 2 * (329 / 200) :=
  residualVariance_le d W' H2 q xi _ _ hd hW' hH2 hradius hH2max
