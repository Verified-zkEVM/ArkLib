/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MeasureTheory.Integral.NatFloorCells
import ArkLib.ToMathlib.MeasureTheory.Integral.PositivePart
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance cases for finite floor cells and positive-part moments

Concrete instances check a floor-cell membership and volume, and the finite-average positive-part
bound for a two-point sample.
-/

open MeasureTheory Set
open scoped BigOperators

/-- The vector `(5 / 2, 0)` lies in the cell indexed by `(2, 0)`. -/
example : (![5 / 2, 0] : Fin 2 → ℝ) ∈ natFloorCell ![2, 0] := by
  simp only [mem_natFloorCell, Fin.forall_fin_two]
  norm_num

/-- The two-dimensional cell with lower corner `(2, 0)` has volume one. -/
example : volume (natFloorCell ![2, 0]) = 1 := volume_natFloorCell _

/-- Integrating `1` over one positive-dimensional floor cell gives its unit cell bound. -/
example :
    ∫ _x in ⋃ i ∈ (Finset.univ : Finset Unit), natFloorCell (fun _ : Fin 1 ↦ 0),
      (1 : ℝ) ∂(volume : Measure (Fin 1 → ℝ)) ≤ 1 := by
  calc
    _ ≤ ∑ i ∈ (Finset.univ : Finset Unit), (1 : ℝ) := by
      apply setIntegral_biUnion_le_sum
      · intro _i _hi
        exact measurableSet_natFloorCell (fun _ : Fin 1 ↦ 0)
      · intro i _ j _ hij
        exact (hij rfl).elim
      · intro _i _hi
        exact integrableOn_const (by rw [volume_natFloorCell]; simp)
      · intro _i _hi
        calc
          volume (natFloorCell (fun _ : Fin 1 ↦ 0)) = 1 := volume_natFloorCell _
          _ ≤ 1 := le_rfl
      · intro _i _hi
        norm_num
      · intro _i _hi _x _hx
        norm_num
    _ = 1 := by simp

/-- The same unit cell contributes its lower constant bound to the integral over itself. -/
example :
    1 ≤ ∫ _x in natFloorCell (fun _ : Fin 1 ↦ 0), (1 : ℝ) ∂(volume : Measure (Fin 1 → ℝ)) := by
  calc
    1 = ∑ i ∈ (Finset.univ : Finset Unit), (1 : ℝ) := by simp
    _ ≤ ∫ x in natFloorCell (fun _ : Fin 1 ↦ 0), (1 : ℝ) ∂volume := by
      apply sum_le_setIntegral_of_measure_eq_one
      · intro _i _hi
        exact measurableSet_natFloorCell (fun _ : Fin 1 ↦ 0)
      · intro i _ j _ hij
        exact (hij rfl).elim
      · intro _i _hi
        exact volume_natFloorCell _
      · intro _i _hi
        exact Subset.rfl
      · exact measurableSet_natFloorCell _
      · exact integrableOn_const (by rw [volume_natFloorCell]; simp)
      · intro _x _hx
        norm_num
      · intro _i _hi _x _hx
        norm_num

/-- For the sample `(0, 2)`, the threshold `2` gives the bound `1 ≤ 1 + 1 / 4`. -/
example : 𝔼 i, max (2 - (![0, 2] : Fin 2 → ℚ) i) 0 ≤ 5 / 4 := by
  have hmean : 𝔼 i, (![0, 2] : Fin 2 → ℚ) i = 1 := by
    simp [Finset.expect, Fin.sum_univ_two, NNRat.smul_def]
  have h := Finset.expect_max_sub_zero_le (s := Finset.univ) (![0, 2] : Fin 2 → ℚ) (c := 2)
    hmean (by norm_num)
  have hvar : 𝔼 i, ((![0, 2] : Fin 2 → ℚ) i - 1) ^ 2 = 1 := by
    simp [Finset.expect, Fin.sum_univ_two, NNRat.smul_def]
    norm_num
  rw [hvar] at h
  linarith

/-- On a point-mass probability measure, the integral bound is attained by the constant `1`. -/
example :
    ∫ _x : Unit, max (3 - (1 : ℝ)) 0 ∂Measure.dirac () ≤
      3 - 1 + (∫ _x : Unit, ((1 : ℝ) - 1) ^ 2 ∂Measure.dirac ()) / (4 * (3 - 1)) := by
  exact (MeasureTheory.integral_max_sub_zero_le (Measure.dirac ())
    (fun _ : Unit ↦ (1 : ℝ)) 3 1 (integrable_const _) (by simp) (integrable_const _) (by norm_num))
