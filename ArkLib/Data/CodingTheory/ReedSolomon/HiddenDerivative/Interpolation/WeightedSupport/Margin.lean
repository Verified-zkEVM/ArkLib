/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Surplus
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Estimate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.NormalizedRank
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
/-!
# Strict surplus for the actual weighted support

The actual support dimension and actual local-map rank are compared after cancelling the
common positive simplex volume and multiplicity cube. The resulting margin is multiplicative:
it includes zero local rank and never divides by that rank.
-/

@[expose] public section

open SimplexIntegration
namespace ReedSolomon.HiddenDerivative
open WeightedSupportParameters

/-- The actual dimension and normalized local-rank bounds give the required strict surplus. -/
theorem weightedSupport_margin_of_normalized_rank {F : Type*} [Field F]
    (δ : ℝ) (n D d m W : ℕ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hn : 0 < n) (hD : 0 < D) (hd : 48000 ≤ d) (hm : 0 < m) (hW : 0 < W)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ)
    (hHlo : xi / δ ≤ harmonicPowerSum (d - 1) 1)
    (hlog : xi / δ ≤ Real.log d)
    (hmean : let g := rateGap δ ((D : ℝ) / n)
      W * harmonicPowerSum (d - 1) 1 / d ≤ (1 + 3 * g / 8) * m)
    (hs : let g := rateGap δ ((D : ℝ) / n)
      W / ((d : ℝ) * (g * m)) ≤ 10 / 27)
    (hfloor : let g := rateGap δ ((D : ℝ) / n)
      (999 / 1000) * ((1 + theta * g) / (g * harmonicPowerSum (d - 1) 1)) ^ 2 ≤
        (W / ((d : ℝ) * (g * m))) ^ 2)
    (hrank : let g := rateGap δ ((D : ℝ) / n)
      let a := 1 + theta * g
      let H := harmonicPowerSum (d - 1) 1
      let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
      (Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) : ℝ) / (V * m ^ 3) ≤
        g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 *
          (d : ℝ) ^ (1 / a) / d) :
    let g := rateGap δ ((D : ℝ) / n)
    (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g)) hD) := by
  let g := rateGap δ ((D : ℝ) / n)
  have hρ : 0 < (D : ℝ) / n := div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hn)
  have hg : 0 < g := (clippedGap_mem_unit δ _ hδ hρ).1
  have ht : 0 < g * (m : ℝ) := mul_pos hg (Nat.cast_pos.mpr hm)
  have hdim := weighted_dimension_lower F d D W hd hD hW g m ht hmean hs
  apply multiplicative_margin_from_bounds δ ((D : ℝ) / n) (harmonicPowerSum (d - 1) 1)
    d g (1 + theta * g) (W / ((d : ℝ) * (g * m)))
    ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) m n D _ _
    hδ hδmax hρlo hρhi hHlo hlog (by positivity) rfl rfl (by positivity)
    (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn) _ hfloor hdim hrank
  field_simp
/-- The prescribed exponential order and rounded support have the strict actual-rank surplus.
Only the outer rate interval remains; no dimension, rank, or moment premise is assumed. -/
theorem prescribed_weightedSupport_margin {F : Type*} [Field F]
    (δ : ℝ) (n D : ℕ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hn : 0 < n) (hD : 0 < D)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let H := harmonicPowerSum (d - 1) 1
    let g := rateGap δ ((D : ℝ) / n)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor ((1 + theta * g) * d * m / H)
    (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g)) hD) := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let H := harmonicPowerSum (d - 1) 1
  let g := rateGap δ ((D : ℝ) / n)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor ((1 + theta * g) * d * m / H)
  have ho := prescribed_order_lower δ hδ hδmax
  have hd : 48000 ≤ d := ho.1
  have hdR : (48000 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ : 0 < (D : ℝ) / n := div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hn)
  have hg : 0 < g := (clippedGap_mem_unit δ _ hδ hρ).1
  have hHlo : xi / δ ≤ H := by simpa only [H, harmonicPowerSum_one] using ho.2.2
  have hH : 0 < H := (div_pos xi_pos hδ).trans_le hHlo
  have hHlog : H ≤ Real.log d + 3 / 5 := by
    simpa only [H, harmonicPowerSum_one] using
      Real.harmonic_pred_le_log_add_three_fifths d (by omega)
  have hHlower : 54 / 5 ≤ H := by
    have hx : 54 / 5 ≤ xi / δ := by
      apply (le_div_iff₀ hδ).mpr
      norm_num [xi]
      linarith
    exact hx.trans hHlo
  have hgH : xi ≤ g * H := clippedGap_mul_harmonic_ge_xi δ _ H hδ hδmax hρ hρhi hHlo
  have hnorm : (1 + theta * g) / (g * H) ≤ 1 / xi := by
    have h := normalizedRadius_le_ten_twentySeven δ _ H ((1 + theta * g) / (g * H))
      hδ hδmax hρ hρhi hHlo le_rfl
    simpa [xi] using h
  obtain ⟨hm, hW, hmean, hs, hf⟩ :=
    prescribed_dimension_inputs δ _ H d hδ hδmax hρ hρhi hd hHlo
  have hHsq := harmonic_square_bound (d : ℝ) H (by linarith) hH.le hHlog
  have hHd : H ≤ d := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hgm : 270 * d * H ≤ g * m := by
    have h1 := mul_le_mul_of_nonneg_left hsize hg.le
    have h2 := mul_le_mul_of_nonneg_left hgH (show 0 ≤ 100 * (d : ℝ) ^ 2 by positivity)
    have h3 := mul_le_mul_of_nonneg_left hHd (show 0 ≤ 270 * (d : ℝ) by positivity)
    norm_num [xi] at h2
    nlinarith
  have hrank := finrank_weightedSupportLocalConstraint_lt_prescribed
    g d D hg hd hD hHlower hHlog hgH hnorm hgm (0 : F) 0
  exact weightedSupport_margin_of_normalized_rank δ n D d m W hδ hδmax hn hD hd hm hW
    hρlo hρhi hHlo ho.2.1 hmean hs hf hrank.le

end ReedSolomon.HiddenDerivative
