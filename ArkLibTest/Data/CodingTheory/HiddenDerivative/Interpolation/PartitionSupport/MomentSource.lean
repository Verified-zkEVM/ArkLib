/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.MomentSource

/-!
# Acceptance tests for the moment form of the partition dimension bound

The necessity of `0 ≤ rate` in `partition_square_rescale`, the degenerate case of a zero scale,
`partitionSupport_dimension_gt_moment` with moment constant `27 / 10` and
coefficient `27 / 20`, and the failure of its conclusion at `W = 0`.
-/

open Finset MeasureTheory PolynomialDifferential ReedSolomon.HiddenDerivative

/-- `partition_square_rescale` needs `0 ≤ rate`: at `rate = -1`, `radius = degree = logarithm = 1`,
`level = -1` and `total = 0`, the hypothesis `-1 * 1 / 1 * 1 ≤ -1` holds, the left side is `1` and
the right side is `0`. -/
example : (-1 : ℝ) * 1 / 1 * 1 ≤ -1 ∧
    ¬ (((-1 : ℝ) * 1 / 1) ^ 2 * (max (1 - 1 * 0 / 1) 0) ^ 2 ≤ (max (-1 - -1 * 0) 0) ^ 2) := by
  norm_num

/-- At `degree = 0` the scale is zero and the comparison holds for any `logarithm`, `level` and
`total`, although `0 < degree` fails. -/
example (level logarithm total : ℝ) (h : 1 * 1 / 0 * logarithm ≤ level) :
    (1 * 1 / 0 : ℝ) ^ 2 * (max (logarithm - 0 * total / 1) 0) ^ 2 ≤
      (max (level - 1 * total) 0) ^ 2 :=
  partition_square_rescale zero_le_one zero_le_one le_rfl h

/-- The moment bound with moment constant `27 / 10`, coefficient `27 / 20`, level
`m * agreement`, cutoff `m * A`, and `agreement * n ≤ A`. -/
example (F : Type*) [Field F] {D d n m A W : ℕ} {rate agreement logarithm : ℝ}
    (hD : 0 < D) (hd : 0 < d) (hW : 0 < W)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A)
    (hlevel : rate * W / d * logarithm ≤ m * agreement)
    (hmoment : (27 / 10 : ℝ) < ⨍ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
      (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2) :
    (27 / 20 : ℝ) * n * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) <
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  have hcutoff : (m : ℝ) * agreement * n ≤ ((m * A : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    push_cast
    linarith
  have h := partitionSupport_dimension_gt_moment F hD hd hW hupper hcutoff hlevel hmoment
  norm_num at h
  exact h

private theorem setAverage_weightedSimplex_zero (f : (Fin 1 → ℝ) → ℝ) :
    ⨍ u in Set.weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) ((0 : ℕ) : ℝ), f u = 0 := by
  rw [setAverage_eq, volume_real_weightedSimplex_succ 1 (by norm_num)]
  simp

/-- The conclusion of `partitionSupport_dimension_gt_moment` fails at `W = 0`. Take `D = d = n = 1`,
`rate = 1`, `level = logarithm = 0`, `L = 0` and `μ = -1`. The simplex is a null set, so the
average is `0 > -1`; `D ≤ rate * n`, `level * n ≤ L` and `rate * W / d * logarithm ≤ level` hold;
and both sides of the conclusion are `0`. -/
example : (((1 : ℕ) : ℝ) ≤ 1 * ((1 : ℕ) : ℝ)) ∧ ((0 : ℝ) * ((1 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ)) ∧
    ((1 : ℝ) * ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * 0 ≤ 0) ∧
    ((-1 : ℝ) < ⨍ u in Set.weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) ((0 : ℕ) : ℝ),
      (max (0 - ((1 : ℕ) : ℝ) * (∑ i, u i) / ((0 : ℕ) : ℝ)) 0) ^ 2) ∧
    ¬ ((-1 : ℝ) / 2 * ((1 : ℕ) : ℝ) * 1 * (((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 *
        (((0 : ℕ) : ℝ) ^ 1 / ((Nat.factorial 1 : ℕ) : ℝ) ^ 2) <
      (Module.finrank ℚ (partitionSupportSpace ℚ 1 1 0 ((0 : ℕ) : ℝ) one_pos) : ℝ)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [setAverage_weightedSimplex_zero]
    norm_num
  · rw [finrank_partitionSupportSpace_eq_partitionSourceCount]
    simp [partitionSourceCount]
