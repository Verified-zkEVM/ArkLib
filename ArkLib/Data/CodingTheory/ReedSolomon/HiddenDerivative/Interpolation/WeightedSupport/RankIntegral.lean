/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.CubeTransfer
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Moments
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.PositivePart

/-!
# The weighted residual rank integral

The unit-cell comparison turns the discrete residual count into an integral on the weighted
simplex enlarged by `choose d 2`.  We normalize that integral to the uniform probability measure
and apply the mean-variance positive-part estimate.  The variance bound is an explicit input so
that its exact evaluation remains in the shared centered-moments module.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory SimplexIntegration

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The discrete residual sum is controlled by the volume of the enlarged weighted simplex times
the mean-variance majorant.  Here `V` may be any upper bound for the centered second moment. -/
theorem weighted_residual_sum_le_volume_mul_mean_variance
    (d W : ℕ) (T V : ℝ) (hd : 1 ≤ d)
    (hW' : 0 < (W : ℝ) + d.choose 2)
    (hc : (W + d.choose 2) * harmonicPowerSum (d - 1) 1 / d < T + (d - 1 : ℕ))
    (hV : (∫ u, (weightedRadius u -
        (W + d.choose 2) * harmonicPowerSum (d - 1) 1 / d) ^ 2
          ∂(weightedSimplexProbabilityMeasure (d - 1) (W + d.choose 2) :
            Measure (Fin (d - 1) → ℝ))) ≤ V) :
    (∑ z ∈ weightedHigherJetTuples d W, (max (T - higherJetTupleDegree z) 0 + 1)) ≤
      volume.real (weightedSimplex (d - 1) (W + d.choose 2)) *
        ((T + (d - 1 : ℕ)) -
            (W + d.choose 2) * harmonicPowerSum (d - 1) 1 / d +
          V / (4 * ((T + (d - 1 : ℕ)) -
            (W + d.choose 2) * harmonicPowerSum (d - 1) 1 / d)) + 1) := by
  let n := d - 1
  let W' : ℝ := W + d.choose 2
  let c : ℝ := T + (d - 1 : ℕ)
  let μ : ℝ := W' * harmonicPowerSum n 1 / d
  let P : Measure (Fin n → ℝ) := weightedSimplexProbabilityMeasure n W'
  have hn : n + 1 = d := by dsimp [n]; omega
  have hnR : (n : ℝ) + 1 = d := by exact_mod_cast hn
  have hY : Integrable (weightedRadius : (Fin n → ℝ) → ℝ) P := by
    exact integrable_weighted_probability hW' continuous_weightedRadius
  have hv : Integrable (fun u : Fin n → ℝ ↦ (weightedRadius u - μ) ^ 2) P := by
    exact integrable_weighted_probability hW'
      ((continuous_weightedRadius.sub continuous_const).pow 2)
  have hmean : (∫ u, weightedRadius u ∂P) = μ := by
    rw [← weightedSimplexExpectation_eq_integral_probability n hW' weightedRadius,
      weightedSimplexExpectation_radius n hW']
    rw [hnR]
  have hpositive := positivePart_mean_variance P weightedRadius c μ hY hmean hv hc
  have hden : 0 < 4 * (c - μ) := by positivity
  have hpositiveV : (∫ u, max (c - weightedRadius u) 0 ∂P) ≤
      c - μ + V / (4 * (c - μ)) := by
    calc
      _ ≤ c - μ + (∫ u, (weightedRadius u - μ) ^ 2 ∂P) / (4 * (c - μ)) := hpositive
      _ ≤ c - μ + V / (4 * (c - μ)) := by gcongr
  have hmax : Integrable (fun u : Fin n → ℝ ↦ max (c - weightedRadius u) 0) P := by
    exact integrable_weighted_probability hW'
      ((continuous_const.sub continuous_weightedRadius).max continuous_const)
  have hexpect : weightedSimplexExpectation n W'
      (fun u ↦ max (c - weightedRadius u) 0 + 1) ≤
        c - μ + V / (4 * (c - μ)) + 1 := by
    rw [weightedSimplexExpectation_eq_integral_probability n hW',
      integral_add hmax (integrable_const (1 : ℝ))]
    simp only [integral_const, smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_mul]
    linarith
  have hint : IntegrableOn (fun u : Fin n → ℝ ↦ max (c - weightedRadius u) 0 + 1)
      (weightedSimplex n W') volume := by
    apply SimplexIntegration.Continuous.integrableOn_weightedSimplex _ hW'.le
    exact ((continuous_const.sub continuous_weightedRadius).max continuous_const).add
      continuous_const
  have htransfer := weighted_residual_sum_le_integral d W T (by
    simpa [n, W', c, weightedRadius, coordinateWeight_sum] using hint)
  rw [coordinateWeight_sum] at htransfer
  have hvolume : 0 < volume.real (weightedSimplex n W') := by
    rw [volume_weightedSimplex n hW'.le]
    positivity
  have hnormalize :
      (∫ u in weightedSimplex n W', max (c - weightedRadius u) 0 + 1) =
        volume.real (weightedSimplex n W') *
          weightedSimplexExpectation n W' (fun u ↦ max (c - weightedRadius u) 0 + 1) := by
    rw [weightedSimplexExpectation, MeasureTheory.setAverage_eq]
    simp only [smul_eq_mul]
    field_simp
  have hnormalize' :
      (∫ u in weightedSimplex (d - 1) W', max (c - ∑ i, u i) 0 + 1) =
        volume.real (weightedSimplex (d - 1) W') *
          weightedSimplexExpectation n W' (fun u ↦ max (c - weightedRadius u) 0 + 1) := by
    simpa [n, weightedRadius] using hnormalize
  rw [show (T + (d - 1 : ℕ)) = c by rfl,
    show ((W : ℝ) + d.choose 2) = W' by rfl] at htransfer ⊢
  rw [hnormalize'] at htransfer
  exact htransfer.trans (by
    simpa [μ, n] using mul_le_mul_of_nonneg_left hexpect hvolume.le)

/-- The exact centered second moment is at most its positive harmonic-square term. -/
theorem weightedSimplex_centeredRadius_sq_le_harmonic
    (d : ℕ) {W' : ℝ} (hd : 1 ≤ d) (hW' : 0 < W') :
    (∫ u, (weightedRadius u - W' * harmonicPowerSum (d - 1) 1 / d) ^ 2
      ∂(weightedSimplexProbabilityMeasure (d - 1) W' :
        Measure (Fin (d - 1) → ℝ))) ≤
      W' ^ 2 * harmonicPowerSum (d - 1) 2 / (d * (d + 1)) := by
  let n := d - 1
  have hn : n + 1 = d := by dsimp [n]; omega
  have hnR : (n : ℝ) + 1 = d := by exact_mod_cast hn
  have hnR2 : (n : ℝ) + 2 = d + 1 := by linarith
  have hformula := integral_normalizedRadius_sq n hW' 1
  have hformula' :
      (∫ u, (weightedRadius u - W' * harmonicPowerSum n 1 / d) ^ 2
        ∂(weightedSimplexProbabilityMeasure n W' : Measure (Fin n → ℝ))) =
        (W' / d) ^ 2 * d / (d + 1) *
          (harmonicPowerSum n 2 - harmonicPowerSum n 1 ^ 2 / d) := by
    simpa [normalizedRadius, hnR, hnR2] using hformula
  rw [show d - 1 = n by rfl, hformula']
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hsubtract : harmonicPowerSum n 2 - harmonicPowerSum n 1 ^ 2 / d ≤
      harmonicPowerSum n 2 := sub_le_self _ (div_nonneg (sq_nonneg _) hdR.le)
  calc
    (W' / d) ^ 2 * d / (d + 1) *
        (harmonicPowerSum n 2 - harmonicPowerSum n 1 ^ 2 / d) ≤
      ((W' / d) ^ 2 * d / (d + 1)) * harmonicPowerSum n 2 := by
        exact mul_le_mul_of_nonneg_left hsubtract (by positivity)
    _ = W' ^ 2 * harmonicPowerSum n 2 / (d * (d + 1)) := by
      field_simp

/-- The residual count with the variance premise discharged by the exact simplex moment. -/
theorem weighted_residual_sum_le_volume_mul_harmonic_variance
    (d W : ℕ) (T : ℝ) (hd : 1 ≤ d)
    (hW' : 0 < (W : ℝ) + d.choose 2)
    (hc : (W + d.choose 2) * harmonicPowerSum (d - 1) 1 / d < T + (d - 1 : ℕ)) :
    (∑ z ∈ weightedHigherJetTuples d W, (max (T - higherJetTupleDegree z) 0 + 1)) ≤
      volume.real (weightedSimplex (d - 1) (W + d.choose 2)) *
        ((T + (d - 1 : ℕ)) -
            (W + d.choose 2) * harmonicPowerSum (d - 1) 1 / d +
          (((W + d.choose 2) ^ 2 * harmonicPowerSum (d - 1) 2 /
              (d * (d + 1))) /
            (4 * ((T + (d - 1 : ℕ)) -
              (W + d.choose 2) * harmonicPowerSum (d - 1) 1 / d))) + 1) := by
  apply weighted_residual_sum_le_volume_mul_mean_variance d W T
    ((W + d.choose 2) ^ 2 * harmonicPowerSum (d - 1) 2 / (d * (d + 1))) hd hW' hc
  exact weightedSimplex_centeredRadius_sq_le_harmonic d hd hW'

/-- Enlarging the weighted radius by `r + choose d 2` costs the exponential factor used by the
contact sum. -/
theorem volume_weightedSimplex_add_choose_le_exp (d W r : ℕ)
    (hW : 0 < W) :
    volume.real (weightedSimplex (d - 1) (W + r + d.choose 2)) ≤
      ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
        Real.exp (((d - 1 : ℕ) : ℝ) / W * (r + d.choose 2)) := by
  rw [volume_weightedSimplex (d - 1) (by positivity : (0 : ℝ) ≤ W + r + d.choose 2)]
  have hWreal : (0 : ℝ) < W := by exact_mod_cast hW
  have he := Real.add_one_le_exp (((r : ℝ) + d.choose 2) / W)
  have he' := mul_le_mul_of_nonneg_left he hWreal.le
  have hbase : (W : ℝ) + r + d.choose 2 ≤
      W * Real.exp (((r : ℝ) + d.choose 2) / W) := by
    have heq : (W : ℝ) * (((r : ℝ) + d.choose 2) / W + 1) =
        W + r + d.choose 2 := by
      field_simp
      ring
    rwa [heq] at he'
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ W + r + d.choose 2)
    hbase (d - 1)
  have hp' : ((W : ℝ) + r + d.choose 2) ^ (d - 1) ≤
      (W : ℝ) ^ (d - 1) *
        Real.exp (((d - 1 : ℕ) : ℝ) / W * (r + d.choose 2)) := by
    calc
      _ ≤ (W * Real.exp (((r : ℝ) + d.choose 2) / W)) ^ (d - 1) := hp
      _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  calc
    ((W : ℝ) + r + d.choose 2) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 ≤
        ((W : ℝ) ^ (d - 1) *
          Real.exp (((d - 1 : ℕ) : ℝ) / W * (r + d.choose 2))) /
            ((d - 1).factorial : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hp' (sq_nonneg _)
    _ = _ := by ring

end

end ReedSolomon.HiddenDerivative
