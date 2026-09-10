/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MeasureTheory.Integral.NaturalFloorCells
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Dimension

/-!
# Transferring the whole weighted simplex to the support

Coordinatewise flooring preserves the weighted upper cutoff and increases the remaining
three-exponent degree budget. Disjoint unit cells transfer the positive-part cubic integral
over the whole simplex to the actual finite support. No event or lower cutoff is discarded.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- Flooring can only increase the remaining three-exponent degree budget. -/
theorem floor_remaining (g m μ R C z : ℝ)
    (hμ : μ ≤ (1 + 3 * g / 8) * m)
    (hZ : R - μ = z * (g * m)) (hfloor : C ≤ R) :
    g * m * (5 / 8 - z) ≤ m * (1 + g) - C := by
  nlinarith


/-- Flooring every point of the weighted simplex preserves its weighted budget. -/
theorem floor_higher_mem (d W : ℕ) (u : Fin (d - 1) → ℝ)
    (hu : ∀ i, 0 ≤ u i)
    (hW : ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W) :
    (fun i ↦ Nat.floor (u i)) ∈ weightedHigherJetTuples d W := by
  rw [mem_weightedHigherJetTuples]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ ↦ mul_le_mul_of_nonneg_left (Nat.floor_le (hu i))
      (show (0 : ℝ) ≤ (i.val + 1 : ℕ) by positivity))
  exact_mod_cast h.trans hW

/-- The positive-part cubic contribution is bounded by the floor tuple's available degree. -/
theorem floor_cubic (g m μ R C z : ℝ) (hgm : 0 ≤ g * m)
    (hμ : μ ≤ (1 + 3 * g / 8) * m)
    (hZ : R - μ = z * (g * m)) (hfloor : C ≤ R) :
    (g * m) ^ 3 * (max (5 / 8 - z) 0) ^ 3 ≤
      (max (m * (1 + g) - C) 0) ^ 3 := by
  rw [← mul_pow]
  have hrem := floor_remaining g m μ R C z hμ hZ hfloor
  have hmax : g * m * max (5 / 8 - z) 0 ≤ max (m * (1 + g) - C) 0 := by
    rw [mul_max_of_nonneg _ _ hgm, mul_zero]
    exact max_le_max_right 0 hrem
  exact pow_le_pow_left₀ (by positivity) hmax _


/-- Unit flooring cells transfer the whole-domain integral to the actual finite weighted sum. -/
theorem weighted_floor_integral (d W : ℕ) (g m μ : ℝ)
    (T : Set (Fin (d - 1) → ℝ)) (hT : MeasurableSet T)
    (z : (Fin (d - 1) → ℝ) → ℝ)
    (hu : ∀ u ∈ T, ∀ i, 0 ≤ u i)
    (hW : ∀ u ∈ T, ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W)
    (hμhi : μ ≤ (1 + 3 * g / 8) * m)
    (hgm0 : 0 ≤ g * m)
    (hZ : ∀ u ∈ T, (∑ i, u i) - μ = z u * (g * m))
    (hint : IntegrableOn (fun u ↦ (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3)
      T volume) :
    (∫ u in T, (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3) ≤
      ∑ c ∈ weightedHigherJetTuples d W,
        (max (m * (1 + g) - higherJetTupleDegree c) 0) ^ 3 := by
  classical
  let s := weightedHigherJetTuples d W
  let cells := fun c : HigherJetTuple d ↦ T ∩ natFloorCell c
  have hcover : T = ⋃ c ∈ s, cells c := by
    ext u
    constructor
    · intro hut
      have hc := floor_higher_mem d W u (hu u hut) (hW u hut)
      apply Set.mem_iUnion.mpr ⟨fun i ↦ Nat.floor (u i), ?_⟩
      apply Set.mem_iUnion.mpr ⟨hc, ?_⟩
      refine ⟨hut, ?_⟩
      exact (mem_natFloorCell_iff (hu u hut)).mpr (fun _ ↦ rfl)
    · intro hut
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hut
      obtain ⟨_, hh⟩ := Set.mem_iUnion.mp hc
      exact hh.1
  rw [hcover]
  apply integral_biUnion_le_sum_of_cell_measure_le_one s cells
  · intro c hc
    exact hT.inter (measurableSet_natFloorCell c)
  · intro c hc e he hce
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (disjoint_natFloorCell hce)
  · intro c hc
    exact hint.mono_set Set.inter_subset_left
  · intro c hc
    exact (measure_mono Set.inter_subset_right).trans_eq (volume_natFloorCell c)
  · intro c hc
    positivity
  · intro c hc u hut
    have heq := (mem_natFloorCell_iff (hu u hut.1)).mp hut.2
    have hf := (sum_natFloor_bounds u (hu u hut.1)).1
    simp_rw [heq] at hf
    have hb := floor_cubic g m μ (∑ i, u i) (higherJetTupleDegree c) (z u)
      hgm0 hμhi (hZ u hut.1) (by simpa [higherJetTupleDegree] using hf)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb

/-- The whole-domain integral bounds the dimension of the actual polynomial support. -/
theorem weighted_dimension_integral (F : Type*) [Field F] (d D W : ℕ)
    (hd : 0 < d) (hD : 0 < D) (g m μ : ℝ)
    (T : Set (Fin (d - 1) → ℝ)) (hT : MeasurableSet T)
    (z : (Fin (d - 1) → ℝ) → ℝ)
    (hu : ∀ u ∈ T, ∀ i, 0 ≤ u i)
    (hW : ∀ u ∈ T, ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W)
    (hμhi : μ ≤ (1 + 3 * g / 8) * m)
    (hgm0 : 0 ≤ g * m)
    (hZ : ∀ u ∈ T, (∑ i, u i) - μ = z u * (g * m))
    (hint : IntegrableOn (fun u ↦ (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3)
      T volume) :
    (D : ℝ) / 6 * (∫ u in T, (g * m) ^ 3 * (max (5 / 8 - z u) 0) ^ 3) ≤
      Module.finrank F (weightedSupportSpace F D d W
        (m * D * (1 + g)) hD) := by
  have hf := weighted_floor_integral d W g m μ T hT z hu hW hμhi hgm0 hZ hint
  have hscaled := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ D / 6 by positivity)
  have hdim := weightedSupport_dimension_ge_cubic_sum F
    (W := W)
    (L := m * D * (1 + g)) hd hD
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have he : m * D * (1 + g) / D = m * (1 + g) := by field_simp
  rw [he] at hdim
  refine hscaled.trans (le_trans (le_of_eq ?_) hdim)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
