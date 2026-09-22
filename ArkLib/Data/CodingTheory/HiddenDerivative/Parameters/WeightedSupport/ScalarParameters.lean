/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds

/-!
# Scalar parameters of the no-band weighted support

The weighted-support interpolation of the hidden-derivative list decoder is parametrized by a
radius `δ` and a rate `ρ`. It fixes the exponential constant `ξ = 27 / 10`, the support tilt
`θ = 3 / 8` and the residual fraction `1 - θ = 5 / 8`, clips the rate to the gap
`g = min 1 (δ / ρ)`, and takes the derivative order `d = ⌈exp (ξ / δ)⌉₊`. This file proves the
dimension-free facts about these choices.

For `δ, ρ > 0` the gap is `g = δ / max δ ρ`, so `(1 + θ g) / g = (max δ ρ + θ δ) / δ` exactly. From
this, a harmonic-type quantity `H ≥ ξ / δ` gives `g H ≥ ξ` when `δ, ρ ≤ 1`, and
`(1 + θ g) / (g H) ≤ 1 / ξ` when `max δ ρ + θ δ ≤ 1`. These hold for every `θ` and every
`ξ > 0`; the source's statements, with `δ ≤ 1 / 4` and `ρ ≤ 1 - δ`, are their specializations.

## Main statements

* `rateGap_eq_div_max`, `one_add_mul_rateGap_div`: the closed forms of `g` and `(1 + θ g) / g`.
* `le_rateGap_mul`, `one_add_mul_rateGap_div_le`, `le_inv_of_le_one_add_mul_rateGap_div`: the
  three inequalities above, for general `θ` and `ξ`.
* `prescribed_order_lower`: `48000 ≤ d`, `ξ / δ ≤ log d` and `ξ / δ ≤ harmonic (d - 1)` for
  `d = ⌈exp (ξ / δ)⌉₊` and `0 < δ ≤ 1 / 4`.
* `xi_le_rateGap_mul`, `normalizedRadius_le_ten_twentySeven`: the specializations to
  `ξ = 27 / 10` and `θ = 3 / 8`.

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/WeightedSupport/`
`ScalarParameters.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The
definition `rateGap` comes from `EndpointComparison.lean` in the same directory; the source's
`ScalarParameters.lean` wrote its body `min 1 (δ / ρ)` inline.

* `xi`, `theta`, `xi_pos`, `theta_pos` are unchanged. `residualFraction` is defined as
  `1 - theta` instead of the literal `5 / 8`; `residualFraction_eq` recovers the literal.
* `clippedGap_mem_unit` is `rateGap_pos` together with `rateGap_le_one`.
* `clippedGap_mul_harmonic_ge_xi` is the case `ξ = xi` of `le_rateGap_mul`, which needs only
  `0 ≤ ξ`, `δ ≤ 1` and `ρ ≤ 1`; the specialization `xi_le_rateGap_mul` keeps the source's
  hypotheses.
* `one_add_theta_mul_clippedGap_div_le` is the case `θ = theta` of `one_add_mul_rateGap_div_le`,
  whose single hypothesis `max δ ρ + θ δ ≤ 1` is necessary and sufficient by
  `one_add_mul_rateGap_div`. `max_add_theta_mul_le_one` derives it from `δ ≤ 1 / 4` and
  `ρ ≤ 1 - δ`.
* `normalizedRadius_le_ten_twentySeven` is the case `θ = theta`, `ξ = xi` of
  `le_inv_of_le_one_add_mul_rateGap_div`.
* `prescribed_order_lower` is unchanged; its harmonic part is `Real.log_le_harmonic_pred`.
* `exp_fifty_four_fifths_gt` is `Real.fortyEightThousand_lt_exp_fiftyFour_div_five` in
  `ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow`; `harmonic_square_bound` is
  `Real.sq_le_div_hundred_of_le_log_add_three_fifths`, and
  `log_add_three_fifths_le_nineteen_over_365_sqrt` is
  `Real.log_add_three_fifths_le_nineteen_div_365_mul_sqrt`, both in
  `ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds`. `harmonic_le_nineteen_over_365_sqrt` is the
  composition of the last with its hypothesis and is not restated.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The exponential constant `ξ = 27 / 10` of the prescribed no-band support. The derivative order
is `⌈exp (ξ / δ)⌉₊`. -/
noncomputable def xi : ℝ := 27 / 10

/-- The support tilt `θ = 3 / 8`. -/
noncomputable def theta : ℝ := 3 / 8

/-- The residual fraction `1 - θ`. -/
noncomputable def residualFraction : ℝ := 1 - theta

@[simp] theorem xi_pos : 0 < xi := by norm_num [xi]

@[simp] theorem theta_pos : 0 < theta := by norm_num [theta]

/-- The residual fraction is `5 / 8`. -/
theorem residualFraction_eq : residualFraction = 5 / 8 := by norm_num [residualFraction, theta]

/-- The clipped rate gap `g = min 1 (δ / ρ)`: it is `1` for `ρ ≤ δ` and `δ / ρ` for `δ ≤ ρ`. -/
noncomputable def rateGap (δ ρ : ℝ) : ℝ := min 1 (δ / ρ)

/-- For `δ, ρ > 0`, `rateGap δ ρ = δ / max δ ρ`. -/
theorem rateGap_eq_div_max {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    rateGap δ ρ = δ / max δ ρ := by
  rcases le_total ρ δ with h | h
  · rw [rateGap, max_eq_left h, div_self hδ.ne', min_eq_left ((one_le_div hρ).mpr h)]
  · rw [rateGap, max_eq_right h, min_eq_right ((div_le_one hρ).mpr h)]

/-- For `δ, ρ > 0` the rate gap is positive. -/
theorem rateGap_pos {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) : 0 < rateGap δ ρ :=
  lt_min one_pos (div_pos hδ hρ)

/-- The rate gap is at most `1`. -/
theorem rateGap_le_one (δ ρ : ℝ) : rateGap δ ρ ≤ 1 := min_le_left _ _

/-- For `δ, ρ > 0`, `(1 + θ g) / g = (max δ ρ + θ δ) / δ` where `g = rateGap δ ρ`, for every `θ`.
-/
theorem one_add_mul_rateGap_div (θ : ℝ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (1 + θ * rateGap δ ρ) / rateGap δ ρ = (max δ ρ + θ * δ) / δ := by
  have hm : 0 < max δ ρ := lt_max_of_lt_left hδ
  rw [rateGap_eq_div_max hδ hρ]
  field_simp

/-- If `0 ≤ ξ`, `0 < δ ≤ 1`, `0 < ρ ≤ 1` and `ξ / δ ≤ H`, then `ξ ≤ g H` for `g = rateGap δ ρ`.
Since `max δ ρ ≤ 1`, `g = δ / max δ ρ ≥ δ`, and `δ H ≥ ξ`. The bounds `δ, ρ ≤ 1` are needed for
`g ≥ δ`. -/
theorem le_rateGap_mul {ξ δ ρ H : ℝ} (hξ : 0 ≤ ξ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hH : ξ / δ ≤ H) : ξ ≤ rateGap δ ρ * H := by
  have hH0 : 0 ≤ H := (div_nonneg hξ hδ.le).trans hH
  have hδH : ξ ≤ δ * H := by rwa [div_le_iff₀ hδ, mul_comm] at hH
  have hg : δ ≤ rateGap δ ρ := by
    rw [rateGap_eq_div_max hδ hρ]
    rw [le_div_iff₀ (lt_max_of_lt_left hδ)]
    exact mul_le_of_le_one_right hδ.le (max_le hδ1 hρ1)
  exact hδH.trans (mul_le_mul_of_nonneg_right hg hH0)

/-- If `max δ ρ + θ δ ≤ 1`, then `(1 + θ g) / g ≤ 1 / δ` for `g = rateGap δ ρ`. By
`one_add_mul_rateGap_div` the hypothesis is also necessary. -/
theorem one_add_mul_rateGap_div_le (θ : ℝ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (h : max δ ρ + θ * δ ≤ 1) : (1 + θ * rateGap δ ρ) / rateGap δ ρ ≤ 1 / δ := by
  rw [one_add_mul_rateGap_div θ hδ hρ]
  exact div_le_div_of_nonneg_right h hδ.le

/-- If `0 < ξ`, `max δ ρ + θ δ ≤ 1`, `ξ / δ ≤ H` and `s ≤ (1 + θ g) / (g H)` for
`g = rateGap δ ρ`, then `s ≤ 1 / ξ`: the quotient is at most `(1 / δ) / H` by
`one_add_mul_rateGap_div_le`, and `δ H ≥ ξ`. The hypothesis `0 < ξ` makes `H` positive. -/
theorem le_inv_of_le_one_add_mul_rateGap_div {θ ξ δ ρ H s : ℝ} (hξ : 0 < ξ) (hδ : 0 < δ)
    (hρ : 0 < ρ) (h : max δ ρ + θ * δ ≤ 1) (hH : ξ / δ ≤ H)
    (hs : s ≤ (1 + θ * rateGap δ ρ) / (rateGap δ ρ * H)) : s ≤ 1 / ξ := by
  have hH0 : 0 < H := (div_pos hξ hδ).trans_le hH
  have hδH : ξ ≤ δ * H := by rwa [div_le_iff₀ hδ, mul_comm] at hH
  have hq : (1 + θ * rateGap δ ρ) / (rateGap δ ρ * H) ≤ 1 / δ / H := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right (one_add_mul_rateGap_div_le θ hδ hρ h) hH0.le
  refine hs.trans (hq.trans ?_)
  rw [div_div]
  exact one_div_le_one_div_of_le hξ hδH

/-- For `0 < δ ≤ 1 / 4` and `ρ ≤ 1 - δ`, `max δ ρ + θ δ ≤ 1` with `θ = 3 / 8`. -/
theorem max_add_theta_mul_le_one {δ ρ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρmax : ρ ≤ 1 - δ) :
    max δ ρ + theta * δ ≤ 1 := by
  rcases le_total δ ρ with h | h
  · rw [max_eq_right h]; norm_num [theta]; linarith
  · rw [max_eq_left h]; norm_num [theta]; linarith

/-- For `0 < δ ≤ 1 / 4` and `d = ⌈exp (ξ / δ)⌉₊`: `48000 ≤ d`, `ξ / δ ≤ log d` and
`ξ / δ ≤ harmonic (d - 1)`. The bound `δ ≤ 1 / 4` gives `ξ / δ ≥ 54 / 5`, and
`exp (54 / 5) > 48000`. -/
theorem prescribed_order_lower (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) :
    let d := ⌈Real.exp (xi / δ)⌉₊
    48000 ≤ d ∧ xi / δ ≤ Real.log d ∧ xi / δ ≤ (harmonic (d - 1) : ℝ) := by
  intro d
  have hceil : Real.exp (xi / δ) ≤ d := Nat.le_ceil _
  have hlog : xi / δ ≤ Real.log d :=
    (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hceil)).mpr hceil
  have he : (54 / 5 : ℝ) ≤ xi / δ := by
    rw [le_div_iff₀ hδ]
    norm_num [xi]
    linarith
  have hd : (48000 : ℝ) ≤ d :=
    (Real.fortyEightThousand_lt_exp_fiftyFour_div_five.trans_le
      ((Real.exp_le_exp.mpr he).trans hceil)).le
  exact ⟨by exact_mod_cast hd, hlog, hlog.trans (Real.log_le_harmonic_pred d)⟩

/-- For `0 < δ ≤ 1 / 4`, `0 < ρ ≤ 1 - δ` and `ξ / δ ≤ H` with `ξ = 27 / 10`: `ξ ≤ g H`. -/
theorem xi_le_rateGap_mul {δ ρ H : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : 0 < ρ)
    (hρmax : ρ ≤ 1 - δ) (hH : xi / δ ≤ H) : xi ≤ rateGap δ ρ * H :=
  le_rateGap_mul xi_pos.le hδ (by linarith) hρ (by linarith) hH

/-- For `0 < δ ≤ 1 / 4`, `0 < ρ ≤ 1 - δ` and `ξ / δ ≤ H`, a radius
`s ≤ (1 + θ g) / (g H)` is at most `1 / ξ = 10 / 27`. -/
theorem normalizedRadius_le_ten_twentySeven {δ ρ H s : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : 0 < ρ) (hρmax : ρ ≤ 1 - δ) (hH : xi / δ ≤ H)
    (hs : s ≤ (1 + theta * rateGap δ ρ) / (rateGap δ ρ * H)) : s ≤ 10 / 27 := by
  have h := le_inv_of_le_one_add_mul_rateGap_div xi_pos hδ hρ
    (max_add_theta_mul_le_one hδ hδmax hρmax) hH hs
  norm_num [xi] at h
  linarith

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
