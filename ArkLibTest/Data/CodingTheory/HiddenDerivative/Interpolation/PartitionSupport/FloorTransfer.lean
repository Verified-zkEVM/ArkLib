/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FloorTransfer

/-!
# Acceptance tests for the partition floor transfer

A concrete instance at `d = 1`, `W = 1`, where the lattice simplex is `{0, 1}`, and the source
statement of `partitionSupport_dimension_ge_rate_integral` at level `m * agreement` and cutoff
`m * A`.
-/

open Finset MeasureTheory PolynomialDifferential ReedSolomon.HiddenDerivative

private theorem natWeightedSimplex_one_one :
    natWeightedSimplex (fun i : Fin 1 => i.val + 1) 1 = {![0], ![1]} := by
  decide

/-- At `d = 1`, `W = 1`, `level = 2`, `rate = 1` the lattice sum is `2 ^ 2 + 1 ^ 2 = 5`, so the
integral of `(max (2 - u) 0) ^ 2` over `[0, 1]` (which is `7 / 3`) is at most `5`. -/
example : ∫ u in Set.weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) ((1 : ℕ) : ℝ),
    (max (2 - 1 * ∑ i, u i) 0) ^ 2 ≤ 5 := by
  refine (partition_floor_square_integral 1 1 2 1 zero_le_one).trans (le_of_eq ?_)
  rw [natWeightedSimplex_one_one, sum_pair (by decide)]
  norm_num

/-- Source shape `partitionSupport_dimension_ge_rate_integral`: level `m * agreement`, cutoff
`m * A`, and `agreement * n ≤ A`. The source's `0 < n` and `0 < rate` are not used. -/
example (F : Type*) [Field F] {D d n m A W : ℕ} {rate agreement : ℝ} (hD : 0 < D)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A) :
    (n : ℝ) / (2 * rate) *
        ∫ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
          (max ((m : ℝ) * agreement - rate * ∑ i, u i) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  refine partitionSupport_dimension_ge_rate_integral F hD hupper ?_
  have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  push_cast
  linarith
