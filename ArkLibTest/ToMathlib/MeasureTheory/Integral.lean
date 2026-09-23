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

/-- In zero dimensions, the unique floor cell has volume one. -/
example : volume (natFloorCell (fun _ : Fin 0 ↦ 0)) = 1 := volume_natFloorCell _

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
