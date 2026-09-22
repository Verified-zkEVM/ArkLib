/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters

/-!
# Endpoint comparison for the no-band weighted support

After cancelling the common simplex volume, the dimension of the weighted support divided by the
normalized local rank is a scalar `normalizedDimensionRankSurplus δ ρ H logd`. Its numerator has
two terms: the cubic baseline `F = ρ (g H / (1 + θ g)) ^ 2 exp (logd θ g / (1 + θ g))` and the
centered-variance correction `J = ρ exp (logd θ g / (1 + θ g))`, where `g = rateGap δ ρ`. This file
proves that the scalar exceeds `543 / 500` for every `0 < δ ≤ 1 / 4` and `δ / 3 ≤ ρ ≤ 1 - δ`,
given `ξ / δ ≤ H` and `ξ / δ ≤ logd`.

At high rates (`δ ≤ ρ`, so `g = δ / ρ`), `F ≥ ξ ^ 2 exp (θ ξ)` and `J ≥ e θ ξ / (1 + θ)`. The
proof uses both bounds: either one alone gives a lower bound on the scalar below `543 / 500`. At
low rates (`ρ < δ`, so `g = 1`), `F` alone gives more than `29 / 10`, with an eighth-degree Taylor
polynomial for `exp (162 / 55)`.

The lower bounds on `F` and `J` are proved for an arbitrary tilt `θ ≥ 0` and constant `ξ ≥ 0`, and
the low-rate bound for arbitrary endpoints `δ ≤ δ₀` and `c δ ≤ ρ`. Only the final comparison fixes
`θ = 3 / 8`, `ξ = 27 / 10`, `δ₀ = 1 / 4` and `c = 1 / 3`.

## Main statements

* `highRate_denominator_sq_le_rate`: `(ρ + θ δ) ^ 2 ≤ ρ` for `δ ≤ ρ ≤ 1 - δ` and
  `θ ^ 2 δ ≤ (1 - 2 θ) (1 - δ)`.
* `highRate_F_lower`, `highRate_J_lower`, `lowRate_F_lower`: lower bounds on the two terms.
* `normalizedDimensionRankSurplus_gt`: the scalar exceeds `543 / 500`.

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/WeightedSupport/`
`EndpointComparison.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `rateGap` moved to `ScalarParameters.lean`. `dimensionBaselineFactor`,
  `dimensionVarianceFactor` and `normalizedDimensionRankSurplus` are unchanged, with the source's
  `let g := rateGap δ ρ` written out.
* `highRate_denominator_sq_le_rate` fixed `θ = 3 / 8` and `δ ≤ 1 / 4`; here `θ ≥ 0` is arbitrary
  subject to `θ ^ 2 δ ≤ (1 - 2 θ) (1 - δ)`, which for `θ = 3 / 8` is `δ ≤ 16 / 25`.
* `highRate_F_lower` fixed `θ` and `ξ` and assumed `δ ≤ 1 / 4` and `ρ ≤ 1 - δ`; here it assumes
  `(ρ + θ δ) ^ 2 ≤ ρ` directly, for any `θ, ξ ≥ 0`.
* `highRate_J_lower` holds for any `θ, ξ ≥ 0`. Its step `exp_reciprocal_product_lower` is
  `Real.exp_one_mul_le_mul_exp_div` in `ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow`,
  which drops `0 < c`.
* `lowRate_F_lower` fixed `δ₀ = 1 / 4` and `c = 1 / 3`; its conclusion
  `(4 ξ ^ 2 / (3 (1 + θ) ^ 2)) exp (4 θ ξ / (1 + θ))` is the case of
  `c ξ ^ 2 / δ₀ (1 / (1 + θ)) ^ 2 exp (ξ / δ₀ (θ / (1 + θ)))`.
* `normalizedDimensionRankSurplus_gt` is unchanged.
* `exp_eightyOne_eightieth_gt` is `Real.elevenFourths_lt_exp_eightyOne_div_eighty` and
  `endpoint_exp_upper` is `Real.exp_sixtyOne_div_hundred_lt`, both in
  `ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow`; `exp_one_gt` (`163 / 60 < e`) is
  replaced by Mathlib's `Real.exp_one_gt_d9`; `lowRate_taylorEight_le_exp` is Mathlib's
  `Real.sum_le_exp_of_nonneg`.
* Not ported, because they are `norm_num` facts with no consumer at the source revision:
  `lowRate_taylorEight_ratio_gt`, `exact_surplus_identity`, `exact_surplus_gt`,
  `exact_surplus_challenge_ratio_lt`, `targetSurplus_challenge_ratio_eq` and
  `challenge_ratio_lt_twelve`. The first three appear as `norm_num` steps of
  `normalizedDimensionRankSurplus_gt`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The normalized cubic-baseline factor
`F = ρ (g H / (1 + θ g)) ^ 2 exp (logd θ g / (1 + θ g))`, with `g = rateGap δ ρ` and `θ = 3 / 8`,
after cancelling the common simplex volume. -/
noncomputable def dimensionBaselineFactor (δ ρ H logd : ℝ) : ℝ :=
  ρ * (rateGap δ ρ * H / (1 + theta * rateGap δ ρ)) ^ 2 *
    Real.exp (logd * (theta * rateGap δ ρ / (1 + theta * rateGap δ ρ)))

/-- The normalized centered-variance factor `J = ρ exp (logd θ g / (1 + θ g))`, with
`g = rateGap δ ρ` and `θ = 3 / 8`, after cancelling the common simplex volume. -/
noncomputable def dimensionVarianceFactor (δ ρ logd : ℝ) : ℝ :=
  ρ * Real.exp (logd * (theta * rateGap δ ρ / (1 + theta * rateGap δ ρ)))

/-- The ratio of the dimension lower bound to the normalized rank upper bound: the cubic baseline
`(5 / 8) ^ 3 F` plus the variance term `(999 / 1000) (4147 / 2160) J`, divided by the rank
constant `6 (101 / 100) (37 / 20) (448 / 625)`. -/
noncomputable def normalizedDimensionRankSurplus (δ ρ H logd : ℝ) : ℝ :=
  (residualFraction ^ 3 * dimensionBaselineFactor δ ρ H logd +
      (999 / 1000) * (4147 / 2160) * dimensionVarianceFactor δ ρ logd) /
    (6 * (101 / 100) * (37 / 20) * (448 / 625))

/-- For `0 < δ ≤ ρ ≤ 1 - δ`, `θ ≥ 0` and `θ ^ 2 δ ≤ (1 - 2 θ) (1 - δ)`, `(ρ + θ δ) ^ 2 ≤ ρ`. The
proof adds `(ρ - δ) (1 - ρ - δ) ≥ 0`, `2 θ δ ρ ≤ 2 θ δ (1 - δ)` and `δ` times the hypothesis on
`θ`. For `θ = 3 / 8` that hypothesis is `δ ≤ 16 / 25`. -/
theorem highRate_denominator_sq_le_rate {θ δ ρ : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ)
    (hθδ : θ ^ 2 * δ ≤ (1 - 2 * θ) * (1 - δ)) (hρ : δ ≤ ρ) (hρmax : ρ ≤ 1 - δ) :
    (ρ + θ * δ) ^ 2 ≤ ρ := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (show 0 ≤ 1 - ρ - δ by linarith),
    mul_le_mul_of_nonneg_left hρmax (by positivity : 0 ≤ 2 * θ * δ),
    mul_le_mul_of_nonneg_left hθδ hδ.le]

/-- High-rate lower bound on the cubic baseline: for `θ, ξ ≥ 0`, `0 < δ ≤ ρ`,
`(ρ + θ δ) ^ 2 ≤ ρ`, `ξ / δ ≤ H` and `ξ / δ ≤ logd`,
`ξ ^ 2 exp (θ ξ) ≤ ρ (g H / (1 + θ g)) ^ 2 exp (logd θ g / (1 + θ g))` with `g = δ / ρ`. Writing
`t = ρ + θ δ`, the two factors are `ρ (δ H) ^ 2 / t ^ 2 ≥ (δ H) ^ 2 ≥ ξ ^ 2` and
`θ δ logd / t ≥ θ ξ`; the second uses `t ≤ 1`, which follows from `t ^ 2 ≤ ρ ≤ t`. -/
theorem highRate_F_lower {θ ξ δ ρ H logd : ℝ} (hθ : 0 ≤ θ) (hξ : 0 ≤ ξ) (hδ : 0 < δ)
    (hρ : δ ≤ ρ) (hden : (ρ + θ * δ) ^ 2 ≤ ρ) (hH : ξ / δ ≤ H) (hlog : ξ / δ ≤ logd) :
    ξ ^ 2 * Real.exp (θ * ξ) ≤
      ρ * (δ / ρ * H / (1 + θ * (δ / ρ))) ^ 2 *
        Real.exp (logd * (θ * (δ / ρ) / (1 + θ * (δ / ρ)))) := by
  have hρ0 : 0 < ρ := hδ.trans_le hρ
  have ht : 0 < ρ + θ * δ := by positivity
  have ht1 : ρ + θ * δ ≤ 1 := by nlinarith
  have e1 : δ / ρ * H / (1 + θ * (δ / ρ)) = δ * H / (ρ + θ * δ) := by field_simp
  have e2 : θ * (δ / ρ) / (1 + θ * (δ / ρ)) = θ * δ / (ρ + θ * δ) := by field_simp
  have hδH : ξ ≤ δ * H := by rwa [div_le_iff₀ hδ, mul_comm] at hH
  have hδL : ξ ≤ δ * logd := by rwa [div_le_iff₀ hδ, mul_comm] at hlog
  rw [e1, e2]
  refine mul_le_mul ?_ (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
  · rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have hsq : ξ ^ 2 ≤ (δ * H) ^ 2 := pow_le_pow_left₀ hξ hδH 2
    calc ξ ^ 2 * (ρ + θ * δ) ^ 2 ≤ (δ * H) ^ 2 * ρ :=
          mul_le_mul hsq hden (by positivity) (by positivity)
      _ = ρ * (δ * H) ^ 2 := mul_comm _ _
  · rw [← mul_div_assoc, le_div_iff₀ ht]
    nlinarith [mul_le_mul_of_nonneg_left ht1 (mul_nonneg hθ hξ),
      mul_le_mul_of_nonneg_left hδL hθ]

/-- High-rate lower bound on the variance term: for `θ, ξ ≥ 0`, `0 < δ ≤ ρ` and `ξ / δ ≤ logd`,
`e θ ξ / (1 + θ) ≤ ρ exp (logd θ g / (1 + θ g))` with `g = δ / ρ`. The exponent is at least
`θ ξ / (ρ + θ δ) ≥ c / ρ` for `c = θ ξ / (1 + θ)`, since `ρ + θ δ ≤ (1 + θ) ρ`, and
`ρ exp (c / ρ) ≥ e c` by `Real.exp_one_mul_le_mul_exp_div`. -/
theorem highRate_J_lower {θ ξ δ ρ logd : ℝ} (hθ : 0 ≤ θ) (hξ : 0 ≤ ξ) (hδ : 0 < δ)
    (hρ : δ ≤ ρ) (hlog : ξ / δ ≤ logd) :
    Real.exp 1 * (θ * ξ / (1 + θ)) ≤
      ρ * Real.exp (logd * (θ * (δ / ρ) / (1 + θ * (δ / ρ)))) := by
  have hρ0 : 0 < ρ := hδ.trans_le hρ
  have ht : 0 < ρ + θ * δ := by positivity
  have e2 : θ * (δ / ρ) / (1 + θ * (δ / ρ)) = θ * δ / (ρ + θ * δ) := by field_simp
  have hδL : ξ ≤ δ * logd := by rwa [div_le_iff₀ hδ, mul_comm] at hlog
  refine (Real.exp_one_mul_le_mul_exp_div _ hρ0).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hρ0.le)
  rw [e2]
  calc θ * ξ / (1 + θ) / ρ = θ * ξ / ((1 + θ) * ρ) := by rw [div_div]
    _ ≤ θ * ξ / (ρ + θ * δ) :=
      div_le_div_of_nonneg_left (by positivity) ht (by nlinarith [mul_le_mul_of_nonneg_left hρ hθ])
    _ ≤ logd * (θ * δ) / (ρ + θ * δ) :=
      div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hδL hθ]) ht.le
    _ = logd * (θ * δ / (ρ + θ * δ)) := mul_div_assoc _ _ _

/-- Low-rate lower bound on the cubic baseline, where `g = 1`: for `θ, ξ, c ≥ 0`,
`0 < δ ≤ δ₀`, `c δ ≤ ρ`, `ξ / δ ≤ H` and `ξ / δ ≤ logd`,
`(c ξ ^ 2 / δ₀) (1 / (1 + θ)) ^ 2 exp ((ξ / δ₀) θ / (1 + θ)) ≤
ρ (H / (1 + θ)) ^ 2 exp (logd θ / (1 + θ))`. The factor bound is
`ρ H ^ 2 ≥ c δ (ξ / δ) ^ 2 = c ξ ^ 2 / δ ≥ c ξ ^ 2 / δ₀`, and the exponent uses
`logd ≥ ξ / δ ≥ ξ / δ₀`. -/
theorem lowRate_F_lower {θ ξ δ₀ c δ ρ H logd : ℝ} (hθ : 0 ≤ θ) (hξ : 0 ≤ ξ) (hc : 0 ≤ c)
    (hδ : 0 < δ) (hδ₀ : δ ≤ δ₀) (hρ : c * δ ≤ ρ) (hH : ξ / δ ≤ H) (hlog : ξ / δ ≤ logd) :
    c * ξ ^ 2 / δ₀ * (1 / (1 + θ)) ^ 2 * Real.exp (ξ / δ₀ * (θ / (1 + θ))) ≤
      ρ * (H / (1 + θ)) ^ 2 * Real.exp (logd * (θ / (1 + θ))) := by
  have hρ0 : 0 ≤ ρ := (mul_nonneg hc hδ.le).trans hρ
  have hH0 : 0 ≤ ξ / δ := div_nonneg hξ hδ.le
  rw [show ρ * (H / (1 + θ)) ^ 2 = ρ * H ^ 2 * (1 / (1 + θ)) ^ 2 by ring]
  refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ (by positivity))
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (by positivity)))
    (Real.exp_pos _).le (by positivity)
  · calc c * ξ ^ 2 / δ₀ ≤ c * ξ ^ 2 / δ := div_le_div_of_nonneg_left (by positivity) hδ hδ₀
      _ = c * δ * (ξ / δ) ^ 2 := by field_simp
      _ ≤ ρ * H ^ 2 := mul_le_mul hρ (pow_le_pow_left₀ hH0 hH 2) (by positivity) hρ0
  · exact (div_le_div_of_nonneg_left hξ hδ hδ₀).trans hlog

/-- For `0 < δ ≤ 1 / 4`, `δ / 3 ≤ ρ ≤ 1 - δ`, `ξ / δ ≤ H` and `ξ / δ ≤ logd`, the
normalized dimension-to-rank ratio exceeds `543 / 500`. For `δ ≤ ρ` it combines
`highRate_F_lower` and `highRate_J_lower`; for `ρ < δ`, `lowRate_F_lower` with an
eighth-degree Taylor polynomial of `exp (162 / 55)` gives more than `29 / 10` from `F` alone. -/
theorem normalizedDimensionRankSurplus_gt (δ ρ H logd : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : δ / 3 ≤ ρ) (hρmax : ρ ≤ 1 - δ) (hH : xi / δ ≤ H) (hlog : xi / δ ≤ logd) :
    (543 / 500 : ℝ) < normalizedDimensionRankSurplus δ ρ H logd := by
  have hρ0 : 0 < ρ := by linarith
  have hJ0 : 0 ≤ dimensionVarianceFactor δ ρ logd := by
    rw [dimensionVarianceFactor]
    positivity
  rw [normalizedDimensionRankSurplus, residualFraction_eq, lt_div_iff₀ (by norm_num)]
  rcases le_or_gt δ ρ with hhigh | hlow
  · have hg : rateGap δ ρ = δ / ρ := by rw [rateGap_eq_div_max hδ hρ0, max_eq_right hhigh]
    have hF : (729 / 100 : ℝ) * (11 / 4) < dimensionBaselineFactor δ ρ H logd := by
      rw [dimensionBaselineFactor, hg]
      refine lt_of_lt_of_le ?_ (highRate_F_lower theta_pos.le xi_pos.le hδ hhigh
        (highRate_denominator_sq_le_rate hδ theta_pos.le
          (by norm_num [theta]; linarith) hhigh hρmax) hH hlog)
      have he := Real.elevenFourths_lt_exp_eightyOne_div_eighty
      norm_num [theta, xi]
      linarith
    have hJ : (81 / 110 : ℝ) * (163 / 60) < dimensionVarianceFactor δ ρ logd := by
      rw [dimensionVarianceFactor, hg]
      refine lt_of_lt_of_le ?_ (highRate_J_lower theta_pos.le xi_pos.le hδ hhigh hlog)
      have he := Real.exp_one_gt_d9
      norm_num [theta, xi]
      linarith
    linarith
  · have hg : rateGap δ ρ = 1 := by
      rw [rateGap_eq_div_max hδ hρ0, max_eq_left hlow.le, div_self hδ.ne']
    have hF : 1 / 3 * xi ^ 2 / (1 / 4) * (1 / (1 + theta)) ^ 2 *
        Real.exp (xi / (1 / 4) * (theta / (1 + theta))) ≤ dimensionBaselineFactor δ ρ H logd := by
      rw [dimensionBaselineFactor, hg]
      simpa only [mul_one, one_mul] using lowRate_F_lower theta_pos.le xi_pos.le
        (by norm_num : (0 : ℝ) ≤ 1 / 3) hδ hδmax (by linarith) hH hlog
    have hexp : xi / (1 / 4) * (theta / (1 + theta)) = 162 / 55 := by norm_num [xi, theta]
    rw [hexp] at hF
    norm_num [xi, theta] at hF
    have hT := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 162 / 55) 9
    norm_num [Finset.sum_range_succ, Nat.factorial] at hT
    linarith

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
