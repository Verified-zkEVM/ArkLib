/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Dimension

/-!
# Acceptance tests for the partition support dimension bounds

The staircase form of the dimension at `d = 0`, the source statements at the cutoff `m * A` with
level `m * agreement`, and the failure of `partition_quadratic_rate_lower` without either of its
hypotheses `D ≤ rate * n` and `level * n ≤ L`.
-/

open Finset PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At `d = 0`, `D = 2`, `L = 3` the only tuple is empty and the dimension is the staircase count
`QuadraticStaircase.count 2 (3 / 2 - 0)`, which is `4` by the partition count test. -/
example : Module.finrank ℚ (partitionSupportSpace ℚ 2 0 0 ((3 : ℕ) : ℝ) two_pos) =
    QuadraticStaircase.count 2 ((3 : ℕ) / (2 : ℕ) - ((0 : ℕ) : ℝ)) := by
  rw [finrank_partitionSupportSpace_eq_sum_count]
  simp [natWeightedSimplex]

/-- Source shape `partitionSupport_dimension_ge_quadratic_sum`, at the cutoff `m * A`. -/
example (F : Type*) [Field F] {D d m A W : ℕ} (hD : 0 < D) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (D : ℝ) * (max ((m * A : ℕ) / (D : ℝ) - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 / 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) :=
  partitionSupport_dimension_ge_quadratic_sum F hD (m * A)

/-- Source shape `partitionSupport_dimension_ge_rate_sum`: level `m * agreement`, cutoff `m * A`,
and `agreement * n ≤ A`. The source's `0 < n` and `0 < rate` are not used. -/
example (F : Type*) [Field F] {D d n m A W : ℕ} {rate agreement : ℝ} (hD : 0 < D)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A) :
    (n : ℝ) / (2 * rate) *
        ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
          (max ((m : ℝ) * agreement - rate * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  refine partitionSupport_dimension_ge_rate_sum F hD hupper ?_
  have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  push_cast
  linarith

/-- `partition_quadratic_rate_lower` needs `D ≤ rate * n`: at `D = n = L = level = 1`,
`rate = 1 / 2`, `deg = 0` the left side is `1` and the right side is `1 / 2`. -/
example : ¬ (((1 : ℕ) : ℝ) / (2 * (1 / 2)) * (max (1 - 1 / 2 * ((0 : ℕ) : ℝ)) 0) ^ 2 ≤
    ((1 : ℕ) : ℝ) * (max (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) 0) ^ 2 / 2) := by
  norm_num

/-- `partition_quadratic_rate_lower` needs `level * n ≤ L`: at `D = n = rate = L = 1`,
`level = 2`, `deg = 0` the left side is `2` and the right side is `1 / 2`. -/
example : ¬ (((1 : ℕ) : ℝ) / (2 * 1) * (max (2 - 1 * ((0 : ℕ) : ℝ)) 0) ^ 2 ≤
    ((1 : ℕ) : ℝ) * (max (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) 0) ^ 2 / 2) := by
  norm_num

/-- With both hypotheses, `D = 1 ≤ rate * n = 1` and `level * n = 1 ≤ L = 1`, the bound holds at
`deg = 0`, where both sides are `1 / 2`. -/
example : ((1 : ℕ) : ℝ) / (2 * 1) * (max (1 - 1 * ((0 : ℕ) : ℝ)) 0) ^ 2 ≤
    ((1 : ℕ) : ℝ) * (max (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) 0) ^ 2 / 2 :=
  partition_quadratic_rate_lower (D := 1) (n := 1) (L := 1) one_pos (by norm_num) (by norm_num)
