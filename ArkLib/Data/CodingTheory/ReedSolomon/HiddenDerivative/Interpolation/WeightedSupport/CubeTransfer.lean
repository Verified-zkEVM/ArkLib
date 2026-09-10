/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Analysis.Simplex.AffinePushforward
public import ArkLib.ToMathlib.MeasureTheory.Integral.NaturalFloorCells
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Coordinates
/-!
# Enlarged cubes for the remaining-degree rank count

Unlike the dimension comparison, this comparison integrates full unit cubes above lattice
points. Their weighted radii increase by `choose d 2`, and their ordinary degree increases by
at most `d - 1`. Thus the original residual is bounded by a positive part on the enlarged simplex.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory SimplexIntegration
namespace ReedSolomon.HiddenDerivative

/-- Each lattice cube lies in the simplex enlarged by the sum of coordinate weights. -/
theorem floorCell_subset_weightedSimplex {d W : ℕ} {z : HigherJetTuple d}
    (hz : z ∈ weightedHigherJetTuples d W) :
    natFloorCell z ⊆ weightedSimplex (d - 1)
      ((W : ℝ) + ∑ i : Fin (d - 1), coordinateWeight i) := by
  intro u hu
  refine ⟨fun i ↦ (Nat.cast_nonneg (z i)).trans (hu i trivial).1, ?_⟩
  have hw : (∑ i, coordinateWeight i * (z i : ℝ)) ≤ W := by
    have hz' := mem_weightedHigherJetTuples.mp hz
    simpa [coordinateWeight, higherJetTupleWeight, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hz'
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    mul_le_mul_of_nonneg_left (hu i trivial).2.le
      (show 0 ≤ coordinateWeight i by unfold coordinateWeight; positivity))
  simp_rw [mul_add, mul_one, Finset.sum_add_distrib] at hsum
  linarith

/-- Inside a unit cube, the continuous total degree increases by at most its dimension. -/
theorem residual_le_on_floorCell {d : ℕ} (T : ℝ) (z : HigherJetTuple d)
    {u : Fin (d - 1) → ℝ} (hu : u ∈ natFloorCell z) :
    max (T - higherJetTupleDegree z) 0 + 1 ≤
      max (T + (d - 1 : ℕ) - ∑ i, u i) 0 + 1 := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (hu i trivial).2.le)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have he : (higherJetTupleDegree z : ℝ) = ∑ i, (z i : ℝ) := by
    simp [higherJetTupleDegree]
  apply add_le_add _ le_rfl
  apply max_le_max _ le_rfl
  rw [he]
  linarith

/-- The weighted residual sum is bounded by an integral over the enlarged simplex. -/
theorem weighted_residual_sum_le_integral (d W : ℕ) (T : ℝ)
    (hint : IntegrableOn (fun u : Fin (d - 1) → ℝ ↦
      max (T + (d - 1 : ℕ) - ∑ i, u i) 0 + 1)
      (weightedSimplex (d - 1) ((W : ℝ) + ∑ i : Fin (d - 1), coordinateWeight i)) volume) :
    (∑ z ∈ weightedHigherJetTuples d W, (max (T - higherJetTupleDegree z) 0 + 1)) ≤
      ∫ u in weightedSimplex (d - 1) ((W : ℝ) + ∑ i : Fin (d - 1), coordinateWeight i),
        max (T + (d - 1 : ℕ) - ∑ i, u i) 0 + 1 := by
  apply sum_le_integral_of_unit_cells (weightedHigherJetTuples d W) natFloorCell
  · exact fun z _ ↦ measurableSet_natFloorCell z
  · exact fun _ _ _ _ h ↦ disjoint_natFloorCell h
  · exact fun z _ ↦ volume_natFloorCell z
  · exact fun _ hz ↦ floorCell_subset_weightedSimplex hz
  · exact hint
  · intro u
    positivity
  · exact fun z _ _ hu ↦ residual_le_on_floorCell T z hu


/-- The enlargement in weighted radius is exactly the triangular number. -/
theorem coordinateWeight_sum (d : ℕ) :
    (∑ i : Fin (d - 1), coordinateWeight i) = (d.choose 2 : ℝ) := by
  simp only [coordinateWeight]
  have hn : ∑ i : Fin (d - 1), (i.val + 1) = d.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i + 1)]
    have h := Finset.sum_range_id d
    cases d with
    | zero => simp
    | succ d =>
      simp only [Nat.add_sub_cancel]
      rw [Finset.sum_range_succ'] at h
      simpa [Nat.choose_two_right] using h
  exact_mod_cast hn
end ReedSolomon.HiddenDerivative
