/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.EndpointComparison
/-!
# Cancelling the common dimension and rank scales

The rank estimate uses a real power of the derivative order. The endpoint comparison uses
an exponential. These identities connect the two expressions exactly and preserve both the
cubic baseline and the centered-variance contribution.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The reciprocal rank power equals the exponential factor used by the endpoint comparison. -/
theorem rankPower_eq_inverse_exp (d g : ℝ) (hd : 0 < d) (hg : 0 ≤ g) :
    d ^ (1 / (1 + theta * g)) / d =
      (Real.exp (Real.log d * (theta * g / (1 + theta * g))))⁻¹ := by
  have ht := theta_pos
  have ha : 1 + theta * g ≠ 0 := ne_of_gt (by positivity)
  rw [Real.rpow_def_of_pos hd, ← Real.exp_log hd, ← Real.exp_sub, ← Real.exp_neg]
  simp only [Real.log_exp]
  congr 1
  field_simp
  ring

/-- Multiplying the normalized rank factor by the scalar surplus recovers the dimension terms. -/
theorem normalized_surplus_product (δ ρ H d : ℝ) (hd : 0 < d)
    (hg : 0 < rateGap δ ρ) (hH : 0 < H) :
    let g := rateGap δ ρ
    let a := 1 + theta * g
    let B := g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 *
      d ^ (1 / a) / d
    B * normalizedDimensionRankSurplus δ ρ H (Real.log d) =
      ρ * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 +
        (4147 / 2160) * (999 / 1000) * (a / (g * H)) ^ 2) := by
  dsimp only
  have ht := theta_pos
  have ha : 1 + theta * rateGap δ ρ ≠ 0 := ne_of_gt (by positivity)
  have he := rankPower_eq_inverse_exp d (rateGap δ ρ) hd hg.le
  rw [show rateGap δ ρ * (448 / 625) * (101 / 100) * (37 / 20) *
      (1 + theta * rateGap δ ρ) ^ 2 / H ^ 2 * d ^ (1 / (1 + theta * rateGap δ ρ)) / d =
      (rateGap δ ρ * (448 / 625) * (101 / 100) * (37 / 20) *
        (1 + theta * rateGap δ ρ) ^ 2 / H ^ 2) *
          (d ^ (1 / (1 + theta * rateGap δ ρ)) / d) by ring, he]
  unfold normalizedDimensionRankSurplus dimensionBaselineFactor dimensionVarianceFactor
    residualFraction
  dsimp only
  field_simp
/-- Absolute dimension and normalized rank estimates imply the strict multiplicative margin.
No division by the rank is used, so zero rank is included. -/
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
  have hg0 : 0 < g := by rw [hg, rateGap]; exact (clippedGap_mem_unit δ ρ hδ hρ).1
  have hH : 0 < H := (div_pos xi_pos hδ).trans_le hHlo
  have ht := theta_pos
  have ha0 : 0 < a := by rw [ha]; positivity
  let B := g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 * d ^ (1 / a) / d
  have hB : 0 < B := by dsimp [B]; positivity
  have hsur := normalizedDimensionRankSurplus_gt δ ρ H (Real.log d)
    hδ hδmax hρlo hρhi hHlo hlog
  have hprod := normalized_surplus_product δ ρ H d hd (by simpa [hg] using hg0) hH
  have hprod' : B * normalizedDimensionRankSurplus δ ρ H (Real.log d) =
      ρ * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (999 / 1000) *
        (a / (g * H)) ^ 2) := by
    simpa only [B, ha, hg] using hprod
  have hsmall : (543 / 500 : ℝ) * B <
      ρ * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2) := by
    calc
      _ < B * normalizedDimensionRankSurplus δ ρ H (Real.log d) := by nlinarith
      _ = _ := hprod'
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [hs]) (by positivity)
  have hVm : 0 < V * m ^ 3 := by positivity
  have hRR : R ≤ (V * m ^ 3) * B := by
    have hh := (div_le_iff₀ hVm).mp hR
    simpa only [B, mul_comm] using hh
  have hfirst : (543 / 500 : ℝ) * n * R ≤
      (V * m ^ 3 * n) * ((543 / 500 : ℝ) * B) := by nlinarith
  have hlast := mul_lt_mul_of_pos_left hsmall (show 0 < V * m ^ 3 * n by positivity)
  have heq : (V * m ^ 3 * n) *
      (ρ * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2)) =
      V * D / 6 * (g * m) ^ 3 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2) := by
    rw [hD]
    ring
  rw [heq] at hlast
  exact (hfirst.trans_lt hlast).trans_le hN

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
