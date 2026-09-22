/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.WeightedSimplex.FloorTransfer

/-!
# Acceptance cases for the floor-cell transfers of weighted simplices

These cases derive the counting sandwich
`vol (weightedSimplex w W) ≤ #(natWeightedSimplex w W) ≤ vol (weightedSimplex w (W + ∑ i, w i))`
from the two transfers, evaluate it on a segment where the upper half is attained, show that a
zero weight breaks flooring, and derive the source's `floor_higher_mem`.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace FloorTransferTest

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The lower half of the counting sandwich: the transfer to lattice sums with integrand and
cellwise bound `1`. -/
theorem volume_real_le_card {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    volume.real (Set.weightedSimplex (fun i ↦ (w i : ℝ)) W) ≤ #(natWeightedSimplex w W) := by
  have hpos : ∀ i, 0 < (w i : ℝ) := fun i ↦ Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hw i))
  have h := setIntegral_le_sum_natWeightedSimplex hw (W := (W : ℝ))
    (Set.measurableSet_weightedSimplex _ _) subset_rfl (f := fun _ ↦ (1 : ℝ)) (g := fun _ ↦ 1)
    (integrableOn_const (volume_weightedSimplex_lt_top hpos _).ne) (fun _ _ ↦ zero_le_one)
    (fun _ _ ↦ le_rfl)
  simpa [Nat.floor_natCast] using h

/-- The upper half of the counting sandwich: the transfer to integrals with integrand and cellwise
bound `1`. Positive weights make the enlarged simplex bounded, so `1` is integrable on it. -/
theorem card_le_volume_real {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    (#(natWeightedSimplex w W) : ℝ) ≤
      volume.real (Set.weightedSimplex (fun i ↦ (w i : ℝ)) ((W : ℝ) + ∑ i, (w i : ℝ))) := by
  have hpos : ∀ i, 0 < (w i : ℝ) := fun i ↦ Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hw i))
  have h := sum_natWeightedSimplex_le_setIntegral W (w := w) (f := fun _ ↦ (1 : ℝ))
    (g := fun _ ↦ 1) (integrableOn_const (volume_weightedSimplex_lt_top hpos _).ne)
    (fun _ _ ↦ zero_le_one) (fun _ _ _ _ ↦ le_rfl)
  simpa using h

/-- On the segment `Fin 1` with weight `1` and budget `2`, the sandwich reads `2 ≤ 3 ≤ 3`: the
lattice points are `0, 1, 2`, the segment `[0, 2]` has length `2`, and the enlarged segment
`[0, 3]` has length `3`. -/
example : volume.real (Set.weightedSimplex (fun _ : Fin 1 ↦ ((1 : ℕ) : ℝ)) (2 : ℕ)) = 2 ∧
    #(natWeightedSimplex (fun _ : Fin 1 ↦ 1) 2) = 3 ∧
    volume.real (Set.weightedSimplex (fun _ : Fin 1 ↦ ((1 : ℕ) : ℝ))
      (((2 : ℕ) : ℝ) + ∑ _i : Fin 1, ((1 : ℕ) : ℝ))) = 3 := by
  refine ⟨?_, by decide, ?_⟩
  · rw [volume_real_weightedSimplex (fun _ ↦ by norm_num) (by norm_num)]
    norm_num
  · rw [volume_real_weightedSimplex (fun _ ↦ by norm_num) (by norm_num)]
    norm_num

example : (2 : ℝ) ≤ #(natWeightedSimplex (fun _ : Fin 1 ↦ 1) 2) ∧
    (#(natWeightedSimplex (fun _ : Fin 1 ↦ 1) 2) : ℝ) ≤ 3 := by
  have h1 := volume_real_le_card (w := fun _ : Fin 1 ↦ 1) (fun _ ↦ one_ne_zero) 2
  have h2 := card_le_volume_real (w := fun _ : Fin 1 ↦ 1) (fun _ ↦ one_ne_zero) 2
  rw [volume_real_weightedSimplex (fun _ ↦ by norm_num) (by norm_num)] at h1 h2
  norm_num at h1 h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- Positive weights are needed for flooring: with one coordinate of weight `0` and budget `0`,
the point `5` lies in the continuous simplex, but its floor `5` is not a lattice point, since
`natWeightedSimplex` bounds every coordinate by the budget. -/
example : (fun _ : Fin 1 ↦ (5 : ℝ)) ∈ Set.weightedSimplex (fun _ ↦ ((0 : ℕ) : ℝ)) 0 ∧
    (fun _ : Fin 1 ↦ ⌊(5 : ℝ)⌋₊) ∉ natWeightedSimplex (fun _ ↦ 0) ⌊(0 : ℝ)⌋₊ := by
  refine ⟨Set.mem_weightedSimplex.mpr ⟨fun _ ↦ by norm_num, by simp⟩, ?_⟩
  rw [Nat.floor_zero, show ⌊(5 : ℝ)⌋₊ = 5 from Nat.floor_natCast 5]
  decide

/-- The upper half of the sandwich needs positive weights: with one coordinate of weight `0` and
budget `0`, the lattice simplex has one point, while the enlarged continuous simplex is the
half-line `[0, ∞)`, of infinite volume and hence of `volume.real` zero. -/
example : #(natWeightedSimplex (fun _ : Fin 1 ↦ 0) 0) = 1 ∧
    volume (Set.weightedSimplex (fun _ : Fin 1 ↦ ((0 : ℕ) : ℝ))
      (((0 : ℕ) : ℝ) + ∑ _i : Fin 1, ((0 : ℕ) : ℝ))) = ⊤ := by
  refine ⟨by decide, ?_⟩
  have hset : Set.weightedSimplex (fun _ : Fin 1 ↦ ((0 : ℕ) : ℝ))
      (((0 : ℕ) : ℝ) + ∑ _i : Fin 1, ((0 : ℕ) : ℝ)) =
      MeasurableEquiv.funUnique (Fin 1) ℝ ⁻¹' Set.Ici 0 := by
    ext u
    simp [Set.mem_weightedSimplex, Fin.forall_fin_one]
  rw [hset]
  exact ((volume_preserving_funUnique (Fin 1) ℝ).measure_preimage_equiv _).trans Real.volume_Ici

/-- The source's `floor_higher_mem`, for the weights `i + 1` on `Fin (d - 1)` and a natural
budget `W`, derived from `natFloor_mem_natWeightedSimplex`. -/
example (d W : ℕ) (u : Fin (d - 1) → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hW : ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W) :
    (fun i ↦ ⌊u i⌋₊) ∈ natWeightedSimplex (fun i : Fin (d - 1) ↦ i.val + 1) W := by
  have h := natFloor_mem_natWeightedSimplex (w := fun i : Fin (d - 1) ↦ i.val + 1)
    (fun i ↦ Nat.succ_ne_zero _) (W := (W : ℝ)) (Set.mem_weightedSimplex.mpr ⟨hu, hW⟩)
  rwa [Nat.floor_natCast] at h

end FloorTransferTest
