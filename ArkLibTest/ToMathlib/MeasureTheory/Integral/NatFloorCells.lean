/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MeasureTheory.Integral.NatFloorCells
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance cases for natural floor cells and cellwise integral bounds

These cases compute cell membership and floors for concrete vectors, check the one-point case of
an empty index type, show that nonnegativity is needed to identify a cell by floors, show that the
cellwise bounds of `setIntegral_biUnion_le_sum` must be nonnegative, and apply that bound to a
concrete integrand on two cells.
-/

open MeasureTheory Set
open scoped BigOperators

/-- The vector `(5 / 2, 0)` lies in the cell of `(2, 0)`, and its floors are `(2, 0)`. -/
example : (![5 / 2, 0] : Fin 2 → ℝ) ∈ natFloorCell ![2, 0] := by
  simp only [mem_natFloorCell, Fin.forall_fin_two]
  norm_num

example : (fun i ↦ ⌊(![5 / 2, 0] : Fin 2 → ℝ) i⌋₊) = ![2, 0] := by
  have hx : ∀ i, 0 ≤ (![5 / 2, 0] : Fin 2 → ℝ) i := by
    simp only [Fin.forall_fin_two]
    norm_num
  have h := (mem_natFloorCell_iff_natFloor_eq (c := ![2, 0]) hx).mp (by
    simp only [mem_natFloorCell, Fin.forall_fin_two]
    norm_num)
  exact funext h

/-- Over an empty index type the unique cell is the whole one-point space, of volume one. -/
example (c : Fin 0 → ℕ) : natFloorCell c = univ ∧ volume (natFloorCell c) = 1 :=
  ⟨by ext x; simp [natFloorCell], volume_natFloorCell c⟩

/-- Nonnegativity is needed in `mem_natFloorCell_iff_natFloor_eq`: the vector `-1 / 2` has natural
floor `0` but does not lie in the cell of `0`. -/
example : (fun _ : Fin 1 ↦ ⌊(-1 / 2 : ℝ)⌋₊) = 0 ∧
    (fun _ : Fin 1 ↦ (-1 / 2 : ℝ)) ∉ natFloorCell (0 : Fin 1 → ℕ) := by
  refine ⟨funext fun _ ↦ Nat.floor_eq_zero.mpr (by norm_num), ?_⟩
  simp only [mem_natFloorCell, Pi.zero_apply, Nat.cast_zero, not_forall]
  exact ⟨0, by norm_num⟩

/-- The bounds in `setIntegral_biUnion_le_sum` must be nonnegative: an empty cell has measure zero,
so the integral over it is `0`, which is not bounded by a negative number. Every other hypothesis
holds here. -/
example : ¬ (∫ _x in ⋃ i ∈ ({()} : Finset Unit), (∅ : Set ℝ), (0 : ℝ)) ≤
    ∑ _i ∈ ({()} : Finset Unit), (-1 : ℝ) := by
  simp

/-- The coordinate `x 0` on the two cells `[0, 1)` and `[1, 2)` of `Fin 1 → ℝ` is bounded by `1`
and `2`, so its integral over their union is at most `3`. -/
example : ∫ x in ⋃ c ∈ ({![0], ![1]} : Finset (Fin 1 → ℕ)), natFloorCell c, x 0 ≤ 3 := by
  have hint : ∀ c : Fin 1 → ℕ, IntegrableOn (fun x : Fin 1 → ℝ ↦ x 0) (natFloorCell c) := by
    intro c
    refine ((continuous_apply 0).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun i ↦ isCompact_Icc (a := (c i : ℝ)) (b := c i + 1))).mono_set ?_
    exact pi_mono fun i _ ↦ Ico_subset_Icc_self
  have h := setIntegral_biUnion_le_sum ({![0], ![1]} : Finset (Fin 1 → ℕ)) natFloorCell
    (fun x : Fin 1 → ℝ ↦ x 0) (fun c ↦ (c 0 : ℝ) + 1)
    (fun c _ ↦ measurableSet_natFloorCell c)
    (fun _ _ _ _ hcd ↦ pairwise_disjoint_natFloorCell hcd)
    (fun c _ ↦ hint c) (fun c _ ↦ (volume_natFloorCell c).le)
    (fun c _ ↦ by positivity) (fun c _ x hx ↦ (mem_natFloorCell.mp hx 0).2.le)
  have hs : ∑ c ∈ ({![0], ![1]} : Finset (Fin 1 → ℕ)), ((c 0 : ℝ) + 1) = 3 := by
    rw [Finset.sum_pair (by decide)]
    norm_num
  exact h.trans hs.le
