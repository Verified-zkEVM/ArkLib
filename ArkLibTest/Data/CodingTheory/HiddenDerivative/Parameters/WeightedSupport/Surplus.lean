/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Surplus

/-!
# Acceptance cases for the multiplicative margin

The source's `rankPower_eq_inverse_exp`, derived from `Real.rpow_one_div_div_self`; a concrete
instance of that identity; the case showing that `a ≠ 0` is needed in it; and the edge case
`R = 0` of `multiplicative_margin_from_bounds`, where the conclusion is `0 < N`.
-/

open ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The source's `rankPower_eq_inverse_exp`, with `a = 1 + θ g` and `0 ≤ g`. -/
example (d g : ℝ) (hd : 0 < d) (hg : 0 ≤ g) :
    d ^ (1 / (1 + theta * g)) / d = (Real.exp (Real.log d * (theta * g / (1 + theta * g))))⁻¹ := by
  have ha : 0 < 1 + theta * g := by have := theta_pos; positivity
  rw [Real.rpow_one_div_div_self hd ha.ne', add_sub_cancel_left]

/-- At `x = 4`, `a = 2`: `4 ^ (1 / 2) / 4 = 1 / 2 = (exp (log 4 / 2))⁻¹`. -/
example : (4 : ℝ) ^ ((1 : ℝ) / 2) / 4 = 1 / 2 ∧
    (4 : ℝ) ^ ((1 : ℝ) / 2) / 4 = (Real.exp (Real.log 4 * ((2 - 1) / 2)))⁻¹ := by
  have hsqrt : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact ⟨by rw [hsqrt]; norm_num, Real.rpow_one_div_div_self (by norm_num) (by norm_num)⟩

/-- `a ≠ 0` is needed in `Real.rpow_one_div_div_self`: at `a = 0`, `x = 2` the left side is
`2 ^ 0 / 2 = 1 / 2` (Lean's `1 / 0 = 0`) and the right side is `exp 0⁻¹ = 1`. -/
example : (2 : ℝ) ^ ((1 : ℝ) / 0) / 2 ≠ (Real.exp (Real.log 2 * ((0 - 1) / 0)))⁻¹ := by
  norm_num

/-- With `R = 0` the margin says only that the dimension bound `N` is positive; the rank
hypothesis is used as `R ≤ V m ^ 3 B` and needs no division by `R`. -/
example (δ ρ H d g a s V m n D N : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρlo : δ / 3 ≤ ρ) (hρhi : ρ ≤ 1 - δ)
    (hHlo : xi / δ ≤ H) (hlog : xi / δ ≤ Real.log d)
    (hd : 0 < d) (hg : g = rateGap δ ρ) (ha : a = 1 + theta * g)
    (hV : 0 < V) (hm : 0 < m) (hn : 0 < n) (hD : D = n * ρ)
    (hs : (999 / 1000) * (a / (g * H)) ^ 2 ≤ s ^ 2)
    (hN : V * D / 6 * (g * m) ^ 3 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2) ≤ N) :
    0 < N := by
  have hH : 0 < H := (div_pos xi_pos hδ).trans_le hHlo
  have hg0 : 0 < g := hg ▸ rateGap_pos hδ (by linarith)
  have ha0 : 0 < a := by rw [ha]; have := theta_pos; positivity
  have h := multiplicative_margin_from_bounds δ ρ H d g a s V m n D N 0 hδ hδmax hρlo hρhi hHlo
    hlog hd hg ha hV hm hn hD hs hN (by rw [zero_div]; positivity)
  simpa using h
