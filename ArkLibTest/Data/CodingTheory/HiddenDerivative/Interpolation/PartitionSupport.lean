/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FiniteSurplus
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Moment

/-!
# Acceptance tests for the finite-ratio partition surplus

At order `500`, the lower-tail moment bound and a positive floor-defined weight budget give a
concrete finite-ratio surplus instance.
-/

open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.RatePartition

private theorem finiteRatioBudget_pos : 0 < partitionWeightBudget 1 1 500 6 := by
  rw [partitionWeightBudget]
  apply Nat.floor_pos.mpr
  have hlogpos : 0 < Real.log (3000 : ℝ) := Real.log_pos (by norm_num)
  have hloglt : Real.log (3000 : ℝ) < 3000 := by
    exact (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)).trans (by norm_num)
  push_cast
  norm_num
  exact (le_div_iff₀ hlogpos).2 (by linarith)

/-- With order `500`, the established lower-tail moment verifies a concrete finite-ratio surplus. -/
example : partitionFiniteRatio 1 1 500 6 * 1 *
    localDerivativeCoordinateBudget 500 6 (partitionWeightBudget 1 1 500 6) <
      Module.finrank ℚ (partitionSupportSpace ℚ 1 500
        (partitionWeightBudget 1 1 500 6) ((6 * 1 : ℕ) : ℝ) one_pos) := by
  have hW : 0 < (partitionWeightBudget 1 1 500 6 : ℕ) := finiteRatioBudget_pos
  have hW' : 0 < (partitionWeightBudget 1 1 500 6 : ℝ) := by exact_mod_cast hW
  have hmoment : (27 / 10 : ℝ) <
      ⨍ u in Set.weightedSimplex (fun i : Fin 500 ↦ (i : ℝ) + 1)
          (partitionWeightBudget 1 1 500 6 : ℝ),
        (max (Real.log (6 * (500 : ℝ)) - 500 * (∑ i, u i) /
          partitionWeightBudget 1 1 500 6) 0) ^ 2 := by
    simpa using RatePartition.setAverage_weightedSimplex_succ_lowerTail_sq_gt
      (d := 500) (by norm_num) hW'
  simpa only [Nat.cast_one] using
    partitionSupport_finiteRatio_surplus (F := ℚ) (D := 1) (d := 500) (n := 1) (m := 6)
    (A := 1)
    (rate := 1) (agreement := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hW (by norm_num) (by norm_num) hmoment
