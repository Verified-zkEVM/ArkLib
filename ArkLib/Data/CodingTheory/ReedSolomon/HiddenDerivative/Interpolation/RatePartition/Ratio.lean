/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.SourceEstimate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.RankEstimate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Convergence

/-! # Comparing the actual partition source dimension and local rank -/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MeasureTheory SimplexIntegration

/-- The analytic second moment and finite lattice estimates give the exact finite ratio. -/
theorem ratePartition_dimension_gt_ratio_of_moment
    {D d m n A : ℕ} {R a : ℝ}
    (hD : 0 < D) (hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (hR : 0 < R) (ha : 0 < a) (hW : 0 < ratePartitionWeight R a d m)
    (hDn : (D : ℝ) ≤ R * n) (haA : a * n ≤ A)
    (hmoment : (27 / 10 : ℝ) < weightedSimplexExpectation d
      (ratePartitionWeight R a d m)
      (fun u ↦ (max (Real.log (6 * d) - (d : ℝ) * weightedRadius u /
        ratePartitionWeight R a d m) 0) ^ 2)) :
    ratePartitionFiniteRatio R a d m * n *
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
  have hgamma : 0 < ratePartitionFiniteRatio R a d m := by
    rw [ratePartitionFiniteRatio_eq hm hW]
    positivity
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hc := mul_le_mul_of_nonneg_left hr (mul_nonneg hgamma.le hnr)
  apply lt_of_le_of_lt hc
  calc
    _ = (27 / 10 : ℝ) / 2 * R * n *
        volume.real (weightedSimplex d (W : ℝ)) * (W : ℝ) ^ 2 / d ^ 2 := by
      rw [ratePartitionFiniteRatio_eq hm hW, volume_weightedSimplex d hW'.le]
      have hexp := Real.exp_pos ((d : ℝ) / W * (m + (d + 1) * d / 2))
      dsimp only
      rw [Real.exp_neg]
      field_simp
      ring
    _ < _ := hs

end ReedSolomon.HiddenDerivative
