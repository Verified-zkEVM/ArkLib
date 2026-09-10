/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Positivity
/-!
# Integrating finite cellwise bounds

A lattice count assigns a contribution to each cell. When the cells are disjoint and have
measure at most one, integrating a pointwise bound on each cell cannot overcount that finite
sum. Applications may intersect unit flooring cells with a simplex; the intersections only
reduce their measure.
-/

@[expose] public section

open scoped BigOperators

namespace MeasureTheory
/-- Integrating over disjoint cells of measure at most one cannot exceed the sum of
nonnegative bounds assigned to the cells. The bound is imposed pointwise on each cell. -/
theorem integral_biUnion_le_sum_of_cell_measure_le_one
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (s : Finset ι) (cell : ι → Set X) (f : X → ℝ) (w : ι → ℝ)
    (hmeas : ∀ i ∈ s, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint (s : Set ι) cell)
    (hint : ∀ i ∈ s, IntegrableOn f (cell i) μ)
    (hvol : ∀ i ∈ s, μ (cell i) ≤ 1)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hbound : ∀ i ∈ s, ∀ x ∈ cell i, ‖f x‖ ≤ w i) :
    (∫ x in ⋃ i ∈ s, cell i, f x ∂μ) ≤ ∑ i ∈ s, w i := by
  rw [integral_biUnion_finset s hmeas hdisj hint]
  apply Finset.sum_le_sum
  intro i hi
  have hfin : μ (cell i) < ⊤ := (hvol i hi).trans_lt (by simp)
  have hv : (μ (cell i)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp) (hvol i hi)
  calc
    (∫ x in cell i, f x ∂μ) ≤ ‖∫ x in cell i, f x ∂μ‖ := le_abs_self _
    _ ≤ w i * (μ (cell i)).toReal := norm_setIntegral_le_of_norm_le_const hfin (hbound i hi)
    _ ≤ w i * 1 := mul_le_mul_of_nonneg_left hv (hw i hi)
    _ = w i := mul_one _

/-- Unit cells contained in a region transfer their pointwise lower bounds to its integral. -/
theorem sum_le_integral_of_unit_cells {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} (s : Finset ι) (cell : ι → Set X) (S : Set X)
    (f : X → ℝ) (w : ι → ℝ)
    (hmeas : ∀ i ∈ s, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint (s : Set ι) cell)
    (hvol : ∀ i ∈ s, μ (cell i) = 1)
    (hsub : ∀ i ∈ s, cell i ⊆ S)
    (hint : IntegrableOn f S μ) (hf : ∀ x, 0 ≤ f x)
    (hbound : ∀ i ∈ s, ∀ x ∈ cell i, w i ≤ f x) :
    ∑ i ∈ s, w i ≤ ∫ x in S, f x ∂μ := by
  have hintCell : ∀ i ∈ s, IntegrableOn f (cell i) μ :=
    fun i hi ↦ hint.mono_set (hsub i hi)
  have hsum : ∑ i ∈ s, w i ≤ ∫ x in ⋃ i ∈ s, cell i, f x ∂μ := by
    rw [integral_biUnion_finset s hmeas hdisj hintCell]
    apply Finset.sum_le_sum
    intro i hi
    have hfin : μ (cell i) < ⊤ := by rw [hvol i hi]; simp
    have hc : IntegrableOn (fun _ : X ↦ w i) (cell i) μ :=
      integrableOn_const hfin.ne
    have h := setIntegral_mono_on hc (hintCell i hi) (hmeas i hi) (hbound i hi)
    simpa [Measure.real, hvol i hi] using h
  apply hsum.trans
  apply setIntegral_mono_set hint (Filter.Eventually.of_forall hf)
  apply Filter.Eventually.of_forall
  intro x hx
  obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hx
  exact hsub i hi hx

end MeasureTheory
