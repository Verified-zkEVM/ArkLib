/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Ratio
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.SharpRatio
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.SharpMoment

/-!
# The sharpened finite partition ratio

The `d ≥ 1000` moment replaces `27/10` by `273/100`, hence replaces the normalized
source-to-rank coefficient `27/20` by `273/200`.  The floor and cube-covering losses are
unchanged, so the existing 300-based logarithmic rounding theorem transfers by the exact factor
`91/90`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MeasureTheory SimplexIntegration

/-- The sharpened analytic moment gives the actual `273/200` finite source-to-rank estimate. -/
theorem ratePartition_dimension_gt_sharpRatio_of_moment
    {D d m n A : ℕ} {R a : ℝ}
    (hD : 0 < D) (hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (hR : 0 < R) (ha : 0 < a) (hW : 0 < ratePartitionWeight R a d m)
    (hDn : (D : ℝ) ≤ R * n) (haA : a * n ≤ A)
    (hmoment : (273 / 100 : ℝ) < weightedSimplexExpectation d
      (ratePartitionWeight R a d m)
      (fun u ↦ (max (Real.log (6 * d) - (d : ℝ) * weightedRadius u /
        ratePartitionWeight R a d m) 0) ^ 2)) :
    sharpRatePartitionFiniteRatio R a d m * n *
      ratePartitionRankBound d m (ratePartitionWeight R a d m) <
      ((ratePartitionExponents D d (ratePartitionWeight R a d m)
        (m * A : ℕ) hD).card : ℝ) := by
  let W := ratePartitionWeight R a d m
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hL : 0 < Real.log (6 * d) := Real.log_pos (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  have hcut : Real.log (6 * d) ≤ (m : ℝ) * a * d / (R * W) := by
    have hf : (W : ℝ) ≤ (m : ℝ) * a * d / (R * Real.log (6 * d)) :=
      Nat.floor_le (by positivity)
    have hf' := (le_div_iff₀ (mul_pos hR hL)).mp hf
    apply (le_div_iff₀ (mul_pos hR hW')).mpr
    nlinarith only [hf']
  have hs := ratePartition_dimension_gt_of_moment hD hd hW hn hR hDn haA hcut hmoment
  have hr := ratePartitionRankBound_le_exponential (m := m) hd hW
  have hgamma : 0 < sharpRatePartitionFiniteRatio R a d m := by
    unfold sharpRatePartitionFiniteRatio
    positivity
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hc := mul_le_mul_of_nonneg_left hr (mul_nonneg hgamma.le hnr)
  apply lt_of_le_of_lt hc
  calc
    _ = (273 / 100 : ℝ) / 2 * R * n *
        volume.real (weightedSimplex d (W : ℝ)) * (W : ℝ) ^ 2 / d ^ 2 := by
      rw [sharpRatePartitionFiniteRatio_eq_scale,
        ratePartitionFiniteRatio_eq hm hW, volume_weightedSimplex d hW'.le]
      have hexp := Real.exp_pos ((d : ℝ) / W * (m + (d + 1) * d / 2))
      dsimp only
      rw [Real.exp_neg]
      field_simp
      ring
    _ < _ := hs

/-- For `d ≥ 1000`, the sharpened finite ratio bounds the actual source and local rank over
every field. -/
theorem ratePartition_dimension_gt_sharpFiniteRatio
    {D d m n A : ℕ} {R a : ℝ}
    (hD : 0 < D) (hd : 1000 ≤ d) (hm : 0 < m) (hn : 0 < n)
    (hR : 0 < R) (ha : 0 < a) (hW : 0 < ratePartitionWeight R a d m)
    (hDn : (D : ℝ) ≤ R * n) (haA : a * n ≤ A) :
    sharpRatePartitionFiniteRatio R a d m * n *
      ratePartitionRankBound d m (ratePartitionWeight R a d m) <
      ((ratePartitionExponents D d (ratePartitionWeight R a d m)
        (m * A : ℕ) hD).card : ℝ) := by
  apply ratePartition_dimension_gt_sharpRatio_of_moment hD (by omega) hm hn hR ha hW hDn haA
  exact RatePartition.weightedSimplexMoment_gt_sharp hd (by exact_mod_cast hW)

end ReedSolomon.HiddenDerivative
