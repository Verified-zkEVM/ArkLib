/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.Moments
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.MomentBounds
/-!
# Centered moments of the actual weighted-simplex distribution

The generic simplex integrals provide the first three raw radius moments. Here they are
centered at their exact mean and scaled by the gap-times-multiplicity parameter. All
integrability premises are discharged for the actual normalized Lebesgue restriction.
-/

@[expose] public section

open MeasureTheory SimplexIntegration
open scoped BigOperators
namespace ReedSolomon.HiddenDerivative

/-- Continuous functions are integrable for the uniform weighted-simplex probability measure. -/
theorem integrable_weighted_probability {n : ℕ} {W : ℝ} (hW : 0 < W)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ)) := by
  rw [weightedSimplexProbabilityMeasure,
    FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (weightedSimplexFiniteMeasure_ne_zero n hW)]
  exact (SimplexIntegration.Continuous.integrableOn_weightedSimplex hf hW.le).smul_measure_nnreal

/-- The radius centered at its exact mean and divided by a chosen scale. -/
noncomputable def normalizedRadius {n : ℕ} (W t : ℝ) (u : Fin n → ℝ) : ℝ :=
  (weightedRadius u - W * harmonicPowerSum n 1 / (n + 1)) / t

/-- Centering and scaling preserve continuity. -/
theorem continuous_normalizedRadius (n : ℕ) (W t : ℝ) :
    Continuous (normalizedRadius (n := n) W t) :=
  (continuous_weightedRadius.sub continuous_const).div_const t

/-- The normalized radius has mean zero. -/
theorem integral_normalizedRadius (n : ℕ) {W : ℝ} (hW : 0 < W) (t : ℝ) :
    (∫ u, normalizedRadius W t u
      ∂(weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ))) = 0 := by
  have hr := integrable_weighted_probability hW (continuous_weightedRadius (n := n))
  unfold normalizedRadius
  rw [integral_div, integral_sub hr (integrable_const _)]
  rw [← weightedSimplexExpectation_eq_integral_probability n hW weightedRadius,
    weightedSimplexExpectation_radius n hW]
  simp

/-- The exact centered second moment. -/
theorem integral_normalizedRadius_sq (n : ℕ) {W : ℝ} (hW : 0 < W) (t : ℝ) :
    (∫ u, normalizedRadius W t u ^ 2
      ∂(weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ))) =
    (W / ((n + 1) * t)) ^ 2 * (n + 1) / (n
       + 2) * (harmonicPowerSum n 2 - harmonicPowerSum n 1 ^ 2 / (n + 1)) := by
  let P : Measure (Fin n → ℝ) := weightedSimplexProbabilityMeasure n W
  let μ := W * harmonicPowerSum n 1 / (n + 1)
  have hr := integrable_weighted_probability hW (continuous_weightedRadius (n := n))
  have hr2 : Integrable (fun u : Fin n → ℝ ↦ weightedRadius u ^ 2)
      (weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ)) :=
    integrable_weighted_probability hW ((continuous_weightedRadius (n := n)).pow 2)
  have he : (fun u : Fin n → ℝ ↦ normalizedRadius W t u ^ 2) =
      (fun u ↦ (weightedRadius u ^ 2 - 2 * μ * weightedRadius u + μ ^ 2) / t ^ 2) := by
    funext u
    dsimp [normalizedRadius, μ]
    ring
  have hi : Integrable (fun u : Fin n → ℝ ↦ weightedRadius u ^ 2 -
      2 * μ * weightedRadius u) P := hr2.sub (hr.const_mul _)
  rw [he, integral_div, integral_add hi (integrable_const _),
    integral_sub hr2 (hr.const_mul _), integral_const_mul]
  rw [← weightedSimplexExpectation_eq_integral_probability n hW _,
    ← weightedSimplexExpectation_eq_integral_probability n hW _,
    weightedSimplexExpectation_radius_sq n hW, weightedSimplexExpectation_radius n hW]
  simp only [integral_const, smul_eq_mul]
  have hP : P.real Set.univ = 1 := by dsimp [P]; simp
  rw [hP, one_mul]
  dsimp [μ]
  field_simp
  ring

/-- The exact centered third moment; no fourth moment is needed. -/
theorem integral_normalizedRadius_cube (n : ℕ) {W : ℝ} (hW : 0 < W) (t : ℝ) :
    (∫ u, normalizedRadius W t u ^ 3
      ∂(weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ))) =
    2 * (W / ((n + 1) * t)) ^ 3 * ((n + 1) ^ 2 * harmonicPowerSum n 3 -
        3 * (n + 1) * harmonicPowerSum n 1 * harmonicPowerSum n 2
       + 2 * harmonicPowerSum n 1 ^ 3) / ((n + 2) * (n + 3)) := by
  let P : Measure (Fin n → ℝ) := weightedSimplexProbabilityMeasure n W
  let μ := W * harmonicPowerSum n 1 / (n + 1)
  have hr : Integrable (weightedRadius : (Fin n → ℝ) → ℝ) P :=
    integrable_weighted_probability hW continuous_weightedRadius
  have hr2 : Integrable (fun u : Fin n → ℝ ↦ weightedRadius u ^ 2) P :=
    integrable_weighted_probability hW (continuous_weightedRadius.pow 2)
  have hr3 : Integrable (fun u : Fin n → ℝ ↦ weightedRadius u ^ 3) P :=
    integrable_weighted_probability hW (continuous_weightedRadius.pow 3)
  have he : (fun u : Fin n → ℝ ↦ normalizedRadius W t u ^ 3) =
      (fun u ↦ (weightedRadius u ^ 3 - 3 * μ * weightedRadius u ^ 2
       + 3 * μ ^ 2 * weightedRadius u - μ ^ 3) / t ^ 3) := by
    funext u
    dsimp [normalizedRadius, μ]
    ring
  have hi2 : Integrable (fun u : Fin n → ℝ ↦ weightedRadius u ^ 3 -
      3 * μ * weightedRadius u ^ 2) P := hr3.sub (hr2.const_mul _)
  have hi3 : Integrable (fun u : Fin n → ℝ ↦ weightedRadius u ^ 3 -
      3 * μ * weightedRadius u ^ 2 + 3 * μ ^ 2 * weightedRadius u) P := hi2.add (hr.const_mul _)
  rw [he, integral_div, integral_sub hi3 (integrable_const _),
    integral_add hi2 (hr.const_mul _), integral_sub hr3 (hr2.const_mul _),
    integral_const_mul, integral_const_mul]
  change (((∫ u, weightedRadius u ^ 3 ∂P) - 3 * μ * (∫ u, weightedRadius u ^ 2 ∂P)
       + 3 * μ ^ 2 * (∫ u, weightedRadius u ∂P)) - (∫ _ : Fin n → ℝ, μ ^ 3 ∂P)) / t ^ 3 = _
  dsimp only [P]
  rw [← weightedSimplexExpectation_eq_integral_probability n hW (fun u ↦ weightedRadius u ^ 3),
    ← weightedSimplexExpectation_eq_integral_probability n hW (fun u ↦ weightedRadius u ^ 2),
    ← weightedSimplexExpectation_eq_integral_probability n hW weightedRadius,
    weightedSimplexExpectation_radius_cube n hW,
    weightedSimplexExpectation_radius_sq n hW, weightedSimplexExpectation_radius n hW]
  simp only [integral_const, smul_eq_mul]
  have hP : P.real Set.univ = 1 := by dsimp [P]; simp
  simp only [P] at hP
  rw [hP, one_mul]
  dsimp [μ]
  field_simp
  ring
end ReedSolomon.HiddenDerivative
