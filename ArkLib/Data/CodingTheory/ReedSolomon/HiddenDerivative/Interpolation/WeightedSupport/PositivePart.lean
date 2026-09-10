/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-!
# A positive-part bound from the mean and variance

The local coordinate count retains the remaining first-derivative exponent. Its averaged
positive part is bounded by a quadratic majorant centered at the mean. Integrating this
pointwise inequality needs only a probability measure and a finite second moment.
-/

@[expose] public section

open MeasureTheory

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- A quadratic majorant for the positive part, centered below its threshold. -/
theorem positivePart_pointwise (c μ y : ℝ) (h : μ < c) :
    max (c - y) 0 ≤ c - y + (y - μ) ^ 2 / (4 * (c - μ)) := by
  have hd : 0 < 4 * (c - μ) := by positivity
  by_cases hy : y ≤ c
  · rw [max_eq_left (sub_nonneg.mpr hy)]
    have hp : 0 ≤ (y - μ) ^ 2 / (4 * (c - μ)) := by positivity
    linarith
  · rw [max_eq_right (by linarith : c - y ≤ 0)]
    have hs := sq_nonneg (y - μ - 2 * (c - μ))
    have he : c - y + (y - μ) ^ 2 / (4 * (c - μ)) =
        ((c - y) * (4 * (c - μ)) + (y - μ) ^ 2) / (4 * (c - μ)) := by
      field_simp [ne_of_gt (sub_pos.mpr h)]
    rw [he]
    exact div_nonneg (by nlinarith) hd.le

/-- The mean and variance control the expected positive residual. -/
theorem positivePart_mean_variance {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (Y : X → ℝ) (c μ : ℝ)
    (hY : Integrable Y P) (hmean : ∫ x, Y x ∂P = μ)
    (hv : Integrable (fun x ↦ (Y x - μ) ^ 2) P) (hc : μ < c) :
    (∫ x, max (c - Y x) 0 ∂P) ≤ c - μ +
      (∫ x, (Y x - μ) ^ 2 ∂P) / (4 * (c - μ)) := by
  have hl : Integrable (fun x ↦ c - Y x) P := (integrable_const c).sub hY
  have hp : Integrable (fun x ↦ max (c - Y x) 0) P := hl.sup (integrable_const 0)
  have h := integral_mono hp (hl.add (hv.div_const (4 * (c - μ))))
    (fun x ↦ positivePart_pointwise c μ (Y x) hc)
  change (∫ x, max (c - Y x) 0 ∂P) ≤
    ∫ x, (c - Y x) + (Y x - μ)^2 / (4 * (c - μ)) ∂P at h
  rw [integral_add hl (hv.div_const (4 * (c - μ))),
    integral_sub (integrable_const c) hY] at h
  simpa [integral_div, hmean] using h

end
end ReedSolomon.HiddenDerivative
