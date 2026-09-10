/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.PartitionSupport.Dimension
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer
public import ArkLib.ToMathlib.Analysis.Simplex.Moments

/-!
# Flooring the rate partition simplex

Coordinatewise flooring keeps the derivative-order budget and can only increase the
remaining specialization degree. Integrating over the whole weighted simplex therefore
gives a lower bound on the finite source count. No subset or tail of the simplex is dropped.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential MeasureTheory SimplexIntegration
open scoped BigOperators

/-- Unit flooring cells transfer the positive-part square to the finite derivative tuples. -/
theorem partition_floor_square_integral (d W : ℕ) (level rate : ℝ) (hrate : 0 ≤ rate) :
    (∫ point in weightedSimplex d W, (max (level - rate * ∑ index, point index) 0) ^ 2) ≤
      ∑ jets ∈ weightedHigherJetTuples (d + 1) W,
        (max (level - rate * higherJetTupleDegree jets) 0) ^ 2 := by
  classical
  let region := weightedSimplex d (W : ℝ)
  let tuples := weightedHigherJetTuples (d + 1) W
  let cells := fun jets : Fin d → ℕ ↦ region ∩ natFloorCell jets
  have hmeasurable : MeasurableSet region :=
    (isCompact_weightedSimplex d (Nat.cast_nonneg W)).isClosed.measurableSet
  have hintegrable : IntegrableOn
      (fun point : Fin d → ℝ ↦ (max (level - rate * ∑ index, point index) 0) ^ 2)
      region volume := by
    apply Continuous.integrableOn_weightedSimplex (hW := Nat.cast_nonneg W)
    fun_prop
  have hcover : region = ⋃ jets ∈ tuples, cells jets := by
    ext point
    constructor
    · intro hpoint
      have hweight : ∑ index : Fin d, ((index.val + 1 : ℕ) : ℝ) * point index ≤ W := by
        simpa [coordinateWeight] using hpoint.2
      have hfloor := WeightedSupportParameters.floor_higher_mem (d + 1) W point hpoint.1 hweight
      refine Set.mem_iUnion.mpr ⟨fun index ↦ Nat.floor (point index), ?_⟩
      refine Set.mem_iUnion.mpr ⟨hfloor, hpoint, ?_⟩
      exact (mem_natFloorCell_iff hpoint.1).mpr (fun _ ↦ rfl)
    · intro hpoint
      obtain ⟨jets, hpoint⟩ := Set.mem_iUnion.mp hpoint
      obtain ⟨_, hpoint⟩ := Set.mem_iUnion.mp hpoint
      exact hpoint.1
  change (∫ point in region, _) ≤ _
  rw [hcover]
  apply integral_biUnion_le_sum_of_cell_measure_le_one tuples cells
  · intro jets _
    exact hmeasurable.inter (measurableSet_natFloorCell jets)
  · intro left _ right _ hne
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (disjoint_natFloorCell hne)
  · intro jets _
    exact hintegrable.mono_set Set.inter_subset_left
  · intro jets _
    exact (measure_mono Set.inter_subset_right).trans_eq (volume_natFloorCell jets)
  · intro jets _
    positivity
  · intro jets _ point hpoint
    have hfloor := (sum_natFloor_bounds point hpoint.1.1).1
    have hcoordinates := (mem_natFloorCell_iff hpoint.1.1).mp hpoint.2
    simp_rw [hcoordinates] at hfloor
    have hdegree : (higherJetTupleDegree jets : ℝ) ≤ ∑ index, point index := by
      simpa [higherJetTupleDegree] using hfloor
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply pow_le_pow_left₀ (by positivity)
    apply max_le_max_right
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hdegree hrate) level

/-- The actual source dimension dominates the complete weighted-simplex square integral. -/
theorem partitionSupport_dimension_ge_rate_integral {F : Type*} [Field F]
    {D d n m A W : ℕ} {rate agreement : ℝ}
    (hD : 0 < D) (hn : 0 < n) (hrate : 0 < rate)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A) :
    (n : ℝ) / (2 * rate) *
      (∫ point in weightedSimplex d W,
        (max ((m : ℝ) * agreement - rate * ∑ index, point index) 0) ^ 2) ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  exact (mul_le_mul_of_nonneg_left
    (partition_floor_square_integral d W ((m : ℝ) * agreement) rate hrate.le)
    (by positivity)).trans (partitionSupport_dimension_ge_rate_sum hD hn hrate hupper hlower)

end ReedSolomon.HiddenDerivative
