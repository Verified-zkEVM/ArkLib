/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Analysis.Convex.Mul
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
/-!
# Cubic expectation bounds on the whole simplex

The positive-part cube is convex. Its supporting tangent at the mean gives the Jensen
baseline, and its ordinary cubic expansion gives the stronger variance correction. Only
moments through order three enter either argument; no event is removed from the support.
-/

@[expose] public section

open MeasureTheory
namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters
noncomputable section

/-- The positive-part cube dominates the signed cube. -/
theorem cubic_le_positive_cube (b z : ℝ) : (b - z) ^ 3 ≤ (max (b - z) 0) ^ 3 := by
  by_cases h : 0 ≤ b - z
  · rw [max_eq_left h]
  · rw [max_eq_right (le_of_not_ge h)]
    have hn : b - z ≤ 0 := le_of_not_ge h
    nlinarith [sq_nonneg (b - z)]

/-- The tangent at the centered mean lies below the positive-part cube. -/
theorem positive_cube_tangent (b z : ℝ) (hb : 0 ≤ b) :
    b ^ 3 - 3 * b ^ 2 * z ≤ (max (b - z) 0) ^ 3 := by
  by_cases h : 0 ≤ b - z
  · rw [max_eq_left h]
    have he : (b - z) ^ 3 - (b ^ 3 - 3 * b ^ 2 * z) = z ^ 2 * (3 * b - z) := by ring
    have hp : 0 ≤ z ^ 2 * (3 * b - z) := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    have hp := mul_nonneg (sq_nonneg b) (show 0 ≤ 3 * z-b by linarith)
    nlinarith

/-- The supporting tangent proves the centered Jensen baseline. -/
theorem positive_cube_jensen {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (z : X → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (hz : Integrable z P) (hm : ∫ x, z x ∂P = 0)
    (hf : Integrable (fun x ↦ (max (b - z x) 0) ^ 3) P) :
    b ^ 3 ≤ ∫ x, (max (b - z x) 0) ^ 3 ∂P := by
  have ht := (integrable_const (b ^ 3)).sub (hz.const_mul (3 * b ^ 2))
  have h := integral_mono ht hf (fun x ↦ positive_cube_tangent b (z x) hb)
  change (∫ x, b ^ 3 - 3 * b ^ 2 * z x ∂P) ≤ _ at h
  rw [integral_sub (integrable_const _) (hz.const_mul _)] at h
  simpa [integral_const_mul, hm] using h

/-- Integrating the cubic expansion gives the variance and third-moment correction. -/
theorem positive_cube_moments {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (z : X → ℝ) (b : ℝ)
    (hz : Integrable z P) (hm : ∫ x, z x ∂P = 0)
    (h2 : Integrable (fun x ↦ z x ^ 2) P)
    (h3 : Integrable (fun x ↦ z x ^ 3) P)
    (hf : Integrable (fun x ↦ (max (b - z x) 0) ^ 3) P) :
    b ^ 3 + 3 * b * (∫ x, z x ^ 2 ∂P) - (∫ x, z x ^ 3 ∂P) ≤
      ∫ x, (max (b - z x) 0) ^ 3 ∂P := by
  have he : (fun x ↦ (b - z x) ^ 3) =
      (fun x ↦ b ^ 3 - 3 * b ^ 2 * z x + 3 * b * z x ^ 2 - z x ^ 3) := by funext x; ring
  have hi := (((integrable_const (b ^ 3)).sub (hz.const_mul (3 * b ^ 2))).add
    (h2.const_mul (3 * b))).sub h3
  have hc : Integrable (fun x ↦ (b - z x) ^ 3) P := by rw [he]; exact hi
  have h := integral_mono hc hf (fun x ↦ cubic_le_positive_cube b (z x))
  rw [he, integral_sub _ h3, integral_add _ (h2.const_mul (3 * b)),
    integral_sub (integrable_const _) (hz.const_mul (3 * b ^ 2))] at h
  · simpa [integral_const_mul, hm] using h
  · exact (integrable_const _).sub (hz.const_mul _)
  · exact ((integrable_const _).sub (hz.const_mul _)).add (h2.const_mul _)


/-- The positive-part cubic is convex on the entire real line. -/
theorem positive_cube_convex (b : ℝ) :
    ConvexOn ℝ Set.univ (fun z : ℝ ↦ (max (b - z) 0) ^ 3) := by
  have hf : ConvexOn ℝ Set.univ (fun z : ℝ ↦ b - z) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a c ha hc hac
    simp only [smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ ↦ t * b) hac]
  exact (hf.sup (convexOn_const 0 convex_univ)).pow (fun _ _ ↦ le_max_right _ _) 3

/-- The prescribed normalized radius gives the exact variance correction. -/
theorem cubic_numeric (s v2 v3 : ℝ) (hsmax : s ≤ 10 / 27)
    (h2 : 3 / 2 * s ^ 2 ≤ v2) (h3 : v3 ≤ 241 / 100 * s ^ 3) :
    (5 / 8:ℝ) ^ 3 + (4147 / 2160) * s ^ 2 ≤ (5 / 8:ℝ) ^ 3 + 3 * (5 / 8) * v2 - v3 := by
  have hp := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hsmax)
  nlinarith

/-- The centered moment estimates yield the no-band dimension contribution. -/
theorem contribution_integral_lower {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (z : X → ℝ) (s : ℝ)
    (hz : Integrable z P) (hm : ∫ x, z x ∂P = 0)
    (h2 : Integrable (fun x ↦ z x ^ 2) P)
    (h3 : Integrable (fun x ↦ z x ^ 3) P)
    (hf : Integrable (fun x ↦ (max (5 / 8 - z x) 0) ^ 3) P)
    (hs : s ≤ 10 / 27)
    (hv2 : 3 / 2 * s ^ 2 ≤ ∫ x, z x ^ 2 ∂P)
    (hv3 : (∫ x, z x ^ 3 ∂P) ≤ 241 / 100 * s ^ 3) :
    (5 / 8:ℝ) ^ 3 + (4147 / 2160) * s ^ 2 ≤ ∫ x, (max (5 / 8 - z x) 0) ^ 3 ∂P :=
  (cubic_numeric s _ _ hs hv2 hv3).trans (positive_cube_moments P z (5 / 8) hz hm h2 h3 hf)

end
end ReedSolomon.HiddenDerivative.WeightedSupportParameters
