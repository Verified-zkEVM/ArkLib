/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Moments
public import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Cubic
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer

/-!
# Dimension from the cubic simplex contribution

First the exact centered moments bound the positive cubic residual in expectation.
The floor transfer then converts this probability estimate to the dimension of the
actual polynomial support, including every point of the weighted simplex.
-/

@[expose] public section

open MeasureTheory SimplexIntegration
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

/-- The actual centered radius supplies the cubic contribution used in the dimension bound. -/
theorem normalizedRadius_contribution_lower (n : ℕ) {W t : ℝ} (hW : 0 < W) (ht : 0 < t)
    (hd : 48000 ≤ (n : ℝ) + 1)
    (hHsq : harmonicPowerSum n 1 ^ 2 ≤ ((n : ℝ) + 1) / 100)
    (hH2 : 38 / 25 ≤ harmonicPowerSum n 2)
    (hH3 : harmonicPowerSum n 3 ≤ 12021 / 10000)
    (hs : W / (((n : ℝ) + 1) * t) ≤ 10 / 27) :
    (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (W / (((n : ℝ) + 1) * t)) ^ 2 ≤
      ∫ u, (max (5 / 8 - normalizedRadius W t u) 0) ^ 3
        ∂(weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ)) := by
  have hc := continuous_normalizedRadius n W t
  have h1 := integrable_weighted_probability hW hc
  have h2 := integrable_weighted_probability hW (hc.pow 2)
  have h3 := integrable_weighted_probability hW (hc.pow 3)
  have hf : Integrable (fun u : Fin n → ℝ ↦ (max (5 / 8 - normalizedRadius W t u) 0) ^ 3)
      (weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ)) :=
    integrable_weighted_probability hW
    (((continuous_const.sub hc).max continuous_const).pow 3)
  have hHnonneg (q : ℕ) : 0 ≤ harmonicPowerSum n q := by
    unfold harmonicPowerSum coefficientPowerSum harmonicCoefficient coordinateWeight
    exact Finset.sum_nonneg fun i _ ↦ by positivity
  apply WeightedSupportParameters.contribution_integral_lower _ _ _ h1
    (integral_normalizedRadius n hW t) h2 h3 hf hs
  · rw [integral_normalizedRadius_sq n hW t]
    have hv := weightedSupport_variance_factor_gt (d := (n : ℝ) + 1)
      (by linarith) hHsq hH2
    have hh := mul_le_mul_of_nonneg_left hv.le
      (sq_nonneg (W / (((n : ℝ) + 1) * t)))
    convert hh using 1 <;> first | rfl | ring
  · rw [integral_normalizedRadius_cube n hW t]
    have ha := weightedSupport_third_factor_le (d := (n : ℝ) + 1)
      (by positivity) (hHnonneg 1) (hHnonneg 2) (hHnonneg 3)
    have hb := weightedSupport_third_factor_numeric hd (hHnonneg 1) hHsq hH3
    have hh := mul_le_mul_of_nonneg_left (ha.trans hb)
      (show 0 ≤ (W / (((n : ℝ) + 1) * t)) ^ 3 by positivity)
    convert hh using 1 <;> first | rfl | ring

/-- Whole-simplex floor transfer turns the probability integral into actual support dimension. -/
theorem weighted_dimension_probability (F : Type*) [Field F] (d D W : ℕ)
    (hd : 0 < d) (hD : 0 < D) (hW : 0 < W) (g m : ℝ) (ht : 0 < g * m)
    (hμ : W * harmonicPowerSum (d - 1) 1 / d ≤ (1 + 3 * g / 8) * m) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    V * D / 6 * (g * m) ^ 3 *
      (∫ u, (max (5 / 8 - normalizedRadius W (g * m) u) 0) ^ 3
        ∂(weightedSimplexProbabilityMeasure (d - 1) W : Measure (Fin (d - 1) → ℝ))) ≤
      Module.finrank F (weightedSupportSpace F D d W (m * D * (1 + g)) hD) := by
  let n := d - 1
  let S := weightedSimplex n (W : ℝ)
  let μ : ℝ := W * harmonicPowerSum n 1 / d
  let z := normalizedRadius (n := n) W (g * m)
  let f := fun u : Fin n → ℝ ↦ (max (5 / 8 - z u) 0) ^ 3
  have hWR : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have hn : (n : ℝ) + 1 = d := by exact_mod_cast (Nat.sub_add_cancel hd)
  have hS : MeasurableSet S := (isCompact_weightedSimplex n hWR.le).measurableSet
  have hf : Continuous f :=
    ((continuous_const.sub (continuous_normalizedRadius n W (g * m))).max continuous_const).pow 3
  have hint : IntegrableOn (fun u ↦ (g * m) ^ 3 * f u) S volume :=
    SimplexIntegration.Continuous.integrableOn_weightedSimplex (continuous_const.mul hf) hWR.le
  have hdim := WeightedSupportParameters.weighted_dimension_integral F d D W hd hD g m μ S hS z
    (fun u hu ↦ hu.1) (fun u hu ↦ by simpa [coordinateWeight] using hu.2)
    hμ ht.le (fun u _ ↦ by
      dsimp [z, normalizedRadius, weightedRadius, μ]
      rw [hn, div_mul_cancel₀ _ ht.ne']) hint
  have hnorm : (∫ u in S, f u) =
      volume.real S * (∫ u, f u
        ∂(weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ))) := by
    rw [← weightedSimplexExpectation_eq_integral_probability n hWR]
    rw [weightedSimplexExpectation, setAverage_eq]
    have hvol : volume.real S ≠ 0 := by
      dsimp [S]
      rw [volume_weightedSimplex n hWR.le]
      positivity
    simp only [smul_eq_mul]
    change (∫ u in S, f u) = volume.real S * ((volume.real S)⁻¹ * (∫ u in S, f u))
    field_simp
  change (D : ℝ) / 6 * (∫ u in S, (g * m) ^ 3 * f u) ≤ _ at hdim
  rw [integral_const_mul, hnorm] at hdim
  have hvol := volume_weightedSimplex n hWR.le
  change volume.real S = _ at hvol
  rw [hvol] at hdim
  convert hdim using 1
  ring

/-- The no-band dimension estimate, with all harmonic moment bounds discharged. -/
theorem weighted_dimension_lower (F : Type*) [Field F] (d D W : ℕ)
    (hd : 48000 ≤ d) (hD : 0 < D) (hW : 0 < W) (g m : ℝ) (ht : 0 < g * m)
    (hμ : W * harmonicPowerSum (d - 1) 1 / d ≤ (1 + 3 * g / 8) * m)
    (hs : W / ((d : ℝ) * (g * m)) ≤ 10 / 27) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    V * D / 6 * (g * m) ^ 3 *
      ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (W / ((d : ℝ) * (g * m))) ^ 2) ≤
      Module.finrank F (weightedSupportSpace F D d W (m * D * (1 + g)) hD) := by
  have hd0 : 0 < d := by omega
  have hn : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast Nat.sub_add_cancel hd0
  have hdR : (48000 : ℝ) ≤ d := by exact_mod_cast hd
  have hH0 : 0 ≤ harmonicPowerSum (d - 1) 1 := by
    rw [harmonicPowerSum_eq_range]
    positivity
  have hH := Real.harmonic_pred_le_log_add_three_fifths d (by omega)
  rw [← harmonicPowerSum_one] at hH
  have hlog := Real.log_add_three_fifths_le_sqrt_div_ten (d : ℝ) (by linarith)
  have hHsq : harmonicPowerSum (d - 1) 1 ^ 2 ≤ (d : ℝ) / 100 := by
    have hh := hH.trans hlog
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have hc := normalizedRadius_contribution_lower (d - 1) (Nat.cast_pos.mpr hW) ht
    (by simpa [hn] using hdR) (by simpa [hn] using hHsq)
    (by rw [harmonicPowerSum_eq_range]; exact (Real.reciprocal_square_sum_gt (by omega)).le)
    (by rw [harmonicPowerSum_eq_range]; exact (Real.reciprocal_cube_sum_lt _).le)
    (by simpa [hn] using hs)
  rw [hn] at hc
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
    (weighted_dimension_probability F d D W hd0 hD hW g m ht hμ)

end ReedSolomon.HiddenDerivative
