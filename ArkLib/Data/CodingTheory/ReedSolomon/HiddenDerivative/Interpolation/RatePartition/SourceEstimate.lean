/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Integral
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Moments

/-!
# Normalizing the partition source integral

This bridge converts a normalized positive-part second moment into a strict
source-dimension bound. The analytic moment is supplied by the ordered-simplex
theorem; the bridge is independent of the particular moment constant.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MeasureTheory SimplexIntegration
open scoped BigOperators

/-- A normalized positive-part moment transfers to the actual finite source count. -/
theorem ratePartition_dimension_gt_of_moment
    {D d W m n A : ℕ} {R a b c : ℝ}
    (hD : 0 < D) (hd : 0 < d) (hW : 0 < W) (hn : 0 < n) (hR : 0 < R)
    (hDn : (D : ℝ) ≤ R * n) (haA : a * n ≤ A)
    (hcut : b ≤ (m : ℝ) * a * d / (R * W))
    (hmoment : c < weightedSimplexExpectation d W
      (fun u ↦ (max (b - (d : ℝ) * weightedRadius u / W) 0) ^ 2)) :
    c / 2 * R * n * volume.real (weightedSimplex d W) *
      (W : ℝ) ^ 2 / d ^ 2 <
      ((ratePartitionExponents D d W (m * A : ℕ) hD).card : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let S := weightedSimplex d (W : ℝ)
  let f := fun u : Fin d → ℝ ↦ (max (b - (d : ℝ) * weightedRadius u / W) 0) ^ 2
  let g := fun u : Fin d → ℝ ↦ (max ((m : ℝ) * a - R * weightedRadius u) 0) ^ 2
  let q : ℝ := R * W / d
  have hq : 0 < q := by dsimp [q]; positivity
  have hfcont : Continuous f :=
    ((continuous_const.sub ((continuous_const.mul continuous_weightedRadius).div_const _)).max
      continuous_const).pow 2
  have hgcont : Continuous g :=
    ((continuous_const.sub (continuous_const.mul continuous_weightedRadius)).max
      continuous_const).pow 2
  have hf := hfcont.integrableOn_weightedSimplex hW'.le
  have hg := hgcont.integrableOn_weightedSimplex hW'.le
  have hpoint : ∀ u, q ^ 2 * f u ≤ g u := by
    intro u
    have hbase : q * (b - (d : ℝ) * weightedRadius u / W) ≤
        (m : ℝ) * a - R * weightedRadius u := by
      have hh := mul_le_mul_of_nonneg_left hcut hq.le
      dsimp [q] at hh ⊢
      field_simp at hh ⊢
      nlinarith only [hh]
    dsimp [f, g]
    rw [← mul_pow, mul_max_of_nonneg _ _ hq.le, mul_zero]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 hbase) 2
  have hS : MeasurableSet S := (isCompact_weightedSimplex d hW'.le).measurableSet
  have hcompare := setIntegral_mono_on (hf.const_mul (q ^ 2)) hg hS
    (fun u _ ↦ hpoint u)
  rw [integral_const_mul] at hcompare
  have hvol : 0 < volume.real S := by
    dsimp [S]
    rw [volume_weightedSimplex d hW'.le]
    positivity
  have hnormalize : volume.real S * weightedSimplexExpectation d W f = ∫ u in S, f u := by
    rw [weightedSimplexExpectation, setAverage_eq]
    simp only [smul_eq_mul]
    dsimp [S] at hvol ⊢
    field_simp
  have hstrict := mul_lt_mul_of_pos_left hmoment hvol
  change volume.real S * c < volume.real S * weightedSimplexExpectation d W f at hstrict
  rw [hnormalize] at hstrict
  have hstrict' := (mul_lt_mul_of_pos_left hstrict (sq_pos_of_pos hq)).trans_le hcompare
  have hsource := ratePartition_dimension_ge_rate_integral hD hn hR hDn haA S hS
    (fun u hu ↦ hu.1) (fun u hu ↦ by simpa [coordinateWeight] using hu.2)
    (by
      apply Continuous.integrableOn_weightedSimplex _ hW'.le
      exact ((continuous_const.sub continuous_weightedRadius).max continuous_const).pow 2)
    hg
  have hlast := (mul_lt_mul_of_pos_left hstrict'
    (by positivity : (0 : ℝ) < n / (2 * R))).trans_le hsource
  calc
    _ = (n : ℝ) / (2 * R) * (q ^ 2 * (volume.real S * c)) := by
      dsimp [q, S]
      field_simp
    _ < _ := hlast

end ReedSolomon.HiddenDerivative
