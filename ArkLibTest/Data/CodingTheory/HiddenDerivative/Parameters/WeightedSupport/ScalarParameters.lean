/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters

/-!
# Acceptance cases for the weighted-support scalar parameters

The specializations written with `min 1 (δ / ρ)` and the hypotheses `δ ≤ 1 / 4`, `ρ ≤ 1 - δ`,
derived from the general statements; the values of the rate gap on both sides of `δ = ρ`; the
cases showing that `δ, ρ ≤ 1` are needed in `le_rateGap_mul` and that `max δ ρ + θ δ ≤ 1` is
needed in `one_add_mul_rateGap_div_le`; and the bounds `H ^ 2 ≤ d / 100` and
`H ≤ (19 / 365) √d` for `H ≤ log d + 3 / 5`.
-/

open ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-! ### Values of the rate gap -/

/-- Below the diagonal the gap is `1`: `rateGap (1 / 4) (1 / 8) = 1`. -/
example : rateGap (1 / 4) (1 / 8) = 1 := by norm_num [rateGap]

/-- Above the diagonal the gap is `δ / ρ`: `rateGap (1 / 4) (1 / 2) = 1 / 2`. -/
example : rateGap (1 / 4) (1 / 2) = 1 / 2 := by
  rw [rateGap_eq_div_max (by norm_num) (by norm_num)]
  norm_num

/-- At `δ = 1 / 4`, `ρ = 1 / 2`, `θ = 3 / 8` the closed form gives
`(1 + θ g) / g = (1 / 2 + 3 / 32) / (1 / 4) = 19 / 8 ≤ 4 = 1 / δ`. -/
example : (1 + theta * rateGap (1 / 4) (1 / 2)) / rateGap (1 / 4) (1 / 2) = 19 / 8 := by
  rw [one_add_mul_rateGap_div theta (by norm_num) (by norm_num)]
  norm_num [theta]

/-! ### Specializations with `min 1 (δ / ρ)` -/

/-- `0 < min 1 (δ / ρ) ≤ 1`, from `rateGap_pos` and `rateGap_le_one`. -/
example (δ ρ : ℝ) (hδ : 0 < δ) (hρ : 0 < ρ) : 0 < min 1 (δ / ρ) ∧ min 1 (δ / ρ) ≤ 1 :=
  ⟨rateGap_pos hδ hρ, rateGap_le_one δ ρ⟩

/-- `xi_le_rateGap_mul` with `rateGap` unfolded. -/
example (δ ρ H : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ)
    (hH : xi / δ ≤ H) : xi ≤ min 1 (δ / ρ) * H :=
  xi_le_rateGap_mul hδ hδmax hρ hρmax hH

/-- `one_add_mul_rateGap_div_le` at `θ = 3 / 8`, for `δ ≤ 1 / 4` and `ρ ≤ 1 - δ`. -/
example (δ ρ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ) :
    (1 + theta * min 1 (δ / ρ)) / min 1 (δ / ρ) ≤ 1 / δ :=
  one_add_mul_rateGap_div_le theta hδ hρ (max_add_theta_mul_le_one hδ hδmax hρmax)

/-- `normalizedRadius_le_ten_twentySeven` with `rateGap` unfolded. -/
example (δ ρ H s : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ)
    (hH : xi / δ ≤ H) (hs : s ≤ (1 + theta * min 1 (δ / ρ)) / (min 1 (δ / ρ) * H)) :
    s ≤ 10 / 27 :=
  normalizedRadius_le_ten_twentySeven hδ hδmax hρ hρmax hH hs

/-- `H ^ 2 ≤ d / 100` for `d ≥ 10000` and `0 ≤ H ≤ log d + 3 / 5`. -/
example (d H : ℝ) (hd : 10000 ≤ d) (hH0 : 0 ≤ H) (hH : H ≤ Real.log d + 3 / 5) :
    H ^ 2 ≤ d / 100 :=
  Real.sq_le_div_hundred_of_le_log_add_three_fifths hd hH0 hH

/-- `H ≤ (19 / 365) √d` for `d ≥ 48000` and `H ≤ log d + 3 / 5`. -/
example (d H : ℝ) (hd : 48000 ≤ d) (hH : H ≤ Real.log d + 3 / 5) :
    H ≤ (19 / 365) * Real.sqrt d :=
  hH.trans (Real.log_add_three_fifths_le_nineteen_div_365_mul_sqrt hd)

/-- At the largest radius `δ = 1 / 4` the prescribed order is at least `48000`. -/
example : 48000 ≤ ⌈Real.exp (xi / (1 / 4))⌉₊ :=
  (prescribed_order_lower (1 / 4) (by norm_num) le_rfl).1

/-! ### Necessity of the hypotheses -/

/-- `δ ≤ 1` is needed in `le_rateGap_mul`: at `ξ = 2`, `δ = ρ = 2`, `H = 1` the hypothesis
`ξ / δ ≤ H` holds, `g = 1`, and `ξ ≤ g H` fails. -/
example : (2 : ℝ) / 2 ≤ 1 ∧ ¬ ((2 : ℝ) ≤ rateGap 2 2 * 1) := by
  norm_num [rateGap]

/-- `ρ ≤ 1` is needed in `le_rateGap_mul`: at `ξ = δ = H = 1`, `ρ = 2`, the gap is `1 / 2` and
`ξ ≤ g H` fails. -/
example : (1 : ℝ) / 1 ≤ 1 ∧ ¬ ((1 : ℝ) ≤ rateGap 1 2 * 1) := by
  norm_num [rateGap]

/-- `max δ ρ + θ δ ≤ 1` is needed in `one_add_mul_rateGap_div_le`: at `δ = 1 / 4`,
`ρ = 15 / 16`, `θ = 3 / 8` it reads `33 / 32 ≤ 1`, which fails, and so does the conclusion
`33 / 8 ≤ 4`. -/
example :
    ¬ ((1 + theta * rateGap (1 / 4) (15 / 16)) / rateGap (1 / 4) (15 / 16) ≤ 1 / (1 / 4)) := by
  rw [one_add_mul_rateGap_div theta (by norm_num) (by norm_num)]
  norm_num [theta]
