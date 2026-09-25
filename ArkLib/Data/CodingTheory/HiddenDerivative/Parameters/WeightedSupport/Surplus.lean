/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Endpoints

/-!
# The multiplicative margin from the dimension and rank bounds

The normalized local rank bound has the factor `d ^ (1 / a) / d` with `a = 1 + θ g`, and the
endpoint comparison has the factor `exp (log d · θ g / (1 + θ g))`. They are reciprocal
(`Real.rpow_one_div_div_self`), so the product of the normalized rank bound `B` and the scalar
`normalizedDimensionRankSurplus` is exactly the normalized dimension bound, with both its cubic
baseline and its variance term. Combined with `normalizedDimensionRankSurplus_gt`, an absolute
dimension lower bound `N` and a rank upper bound `R` then satisfy `(543 / 500) n R < N`.

## Main statements

* `normalized_surplus_product`: `B · normalizedDimensionRankSurplus = ρ g ^ 3 / 6 · (…)`.
* `multiplicative_margin_from_bounds`: `(543 / 500) n R < N`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- For `d, H > 0` and `g = rateGap δ ρ > 0`, with `a = 1 + θ g` and the normalized rank bound
`B = g (448 / 625) (101 / 100) (37 / 20) a ^ 2 / H ^ 2 · d ^ (1 / a) / d`,
`B · normalizedDimensionRankSurplus δ ρ H (log d) =
ρ g ^ 3 / 6 · ((5 / 8) ^ 3 + (4147 / 2160) (999 / 1000) (a / (g H)) ^ 2)`. The right side is the
normalized dimension lower bound; the identity rests on `d ^ (1 / a) / d` being the reciprocal of
the exponential factor of `dimensionBaselineFactor` and `dimensionVarianceFactor`. -/
theorem normalized_surplus_product (δ ρ H d : ℝ) (hd : 0 < d) (hg : 0 < rateGap δ ρ)
    (hH : 0 < H) :
    let g := rateGap δ ρ
    let a := 1 + theta * g
    let B := g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 * d ^ (1 / a) / d
    B * normalizedDimensionRankSurplus δ ρ H (Real.log d) =
      ρ * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (999 / 1000) * (a / (g * H)) ^ 2) := by
  dsimp only
  have ha : 0 < 1 + theta * rateGap δ ρ := by have := theta_pos; positivity
  have he : d ^ (1 / (1 + theta * rateGap δ ρ)) / d =
      (Real.exp (Real.log d * (theta * rateGap δ ρ / (1 + theta * rateGap δ ρ))))⁻¹ := by
    rw [Real.rpow_one_div_div_self hd ha.ne', add_sub_cancel_left]
  rw [show rateGap δ ρ * (448 / 625) * (101 / 100) * (37 / 20) *
      (1 + theta * rateGap δ ρ) ^ 2 / H ^ 2 * d ^ (1 / (1 + theta * rateGap δ ρ)) / d =
      (rateGap δ ρ * (448 / 625) * (101 / 100) * (37 / 20) *
        (1 + theta * rateGap δ ρ) ^ 2 / H ^ 2) *
          (d ^ (1 / (1 + theta * rateGap δ ρ)) / d) by ring, he,
    normalizedDimensionRankSurplus, dimensionBaselineFactor, dimensionVarianceFactor,
    residualFraction_eq]
  have ha' : 1 + rateGap δ ρ * theta ≠ 0 := by rw [mul_comm]; exact ha.ne'
  field_simp

/-- Absolute bounds imply the strict multiplicative margin `(543 / 500) n R < N`. The hypotheses
are those of `normalizedDimensionRankSurplus_gt` for `logd = log d`; a dimension lower bound
`V D / 6 (g m) ^ 3 ((5 / 8) ^ 3 + (4147 / 2160) s ^ 2) ≤ N` with `D = n ρ` and
`(999 / 1000) (a / (g H)) ^ 2 ≤ s ^ 2`; and a normalized rank bound `R / (V m ^ 3) ≤ B` with `B` as
in `normalized_surplus_product`. The rank bound is used as `R ≤ V m ^ 3 B`, without dividing by
`R`, so `R = 0` is allowed. -/
theorem multiplicative_margin_from_bounds (δ ρ H d g a s V m n D N R : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρlo : δ / 3 ≤ ρ) (hρhi : ρ ≤ 1 - δ)
    (hHlo : xi / δ ≤ H) (hlog : xi / δ ≤ Real.log d)
    (hd : 0 < d) (hg : g = rateGap δ ρ) (ha : a = 1 + theta * g)
    (hV : 0 < V) (hm : 0 < m) (hn : 0 < n) (hD : D = n * ρ)
    (hs : (999 / 1000) * (a / (g * H)) ^ 2 ≤ s ^ 2)
    (hN : V * D / 6 * (g * m) ^ 3 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2) ≤ N)
    (hR : R / (V * m ^ 3) ≤
      g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 * d ^ (1 / a) / d) :
    (543 / 500 : ℝ) * n * R < N := by
  have hρ : 0 < ρ := (div_pos hδ (by norm_num)).trans_le hρlo
  have hg0 : 0 < g := hg ▸ rateGap_pos hδ hρ
  have hH : 0 < H := (div_pos xi_pos hδ).trans_le hHlo
  have ht := theta_pos
  have ha0 : 0 < a := by rw [ha]; positivity
  let B := g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 * d ^ (1 / a) / d
  have hB : 0 < B := by positivity
  have hsur := normalizedDimensionRankSurplus_gt δ ρ H (Real.log d) hδ hδmax hρlo hρhi hHlo hlog
  have hprod : B * normalizedDimensionRankSurplus δ ρ H (Real.log d) =
      ρ * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (999 / 1000) * (a / (g * H)) ^ 2) := by
    simpa only [B, ha, hg] using
      normalized_surplus_product δ ρ H d hd (hg ▸ hg0) hH
  have hsmall : (543 / 500 : ℝ) * B <
      ρ * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2) := by
    have hvariance : (4147 / 2160 : ℝ) * ((999 / 1000) * (a / (g * H)) ^ 2) ≤
        (4147 / 2160) * s ^ 2 := mul_le_mul_of_nonneg_left hs (by norm_num)
    calc
      (543 / 500 : ℝ) * B = B * (543 / 500) := by ring
      _ < B * normalizedDimensionRankSurplus δ ρ H (Real.log d) :=
        mul_lt_mul_of_pos_left hsur hB
      _ = _ := hprod
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        calc
          (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (999 / 1000) * (a / (g * H)) ^ 2 =
              (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * ((999 / 1000) * (a / (g * H)) ^ 2) := by ring
          _ ≤ _ := add_le_add_right hvariance _
      ) (by positivity)
  have hVm : 0 < V * m ^ 3 := by positivity
  have hRR : R ≤ V * m ^ 3 * B := by
    simpa only [B, mul_comm] using (div_le_iff₀ hVm).mp hR
  have hlast := mul_lt_mul_of_pos_left hsmall (show 0 < V * m ^ 3 * n by positivity)
  have heq : V * m ^ 3 * n * (ρ * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2)) =
      V * D / 6 * (g * m) ^ 3 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2) := by
    rw [hD]
    ring
  rw [heq] at hlast
  calc
    (543 / 500 : ℝ) * n * R ≤ (543 / 500) * n * (V * m ^ 3 * B) := by gcongr
    _ = V * m ^ 3 * n * ((543 / 500) * B) := by ring
    _ < _ := hlast
    _ ≤ N := hN

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
