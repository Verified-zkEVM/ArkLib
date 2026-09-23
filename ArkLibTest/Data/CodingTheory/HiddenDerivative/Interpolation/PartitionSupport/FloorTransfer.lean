/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FloorTransfer

/-!
# Acceptance tests for the partition floor transfer

A concrete instance at `d = 1`, `W = 1`, where the lattice simplex is `{0, 1}`, and
`partitionSupport_dimension_ge_rate_integral` at level `m * agreement` and cutoff
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

/-- The integral lower bound at level `m * agreement`, cutoff `m * A`, and
`agreement * n ≤ A`. -/
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

private def halfInterval : Set (Fin 1 → ℝ) := {u | 0 ≤ u 0 ∧ u 0 ≤ 1 / 2}

private theorem halfInterval_subset_weightedSimplex :
    halfInterval ⊆ Set.weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) (1 : ℕ) := by
  intro u hu
  rw [Set.mem_weightedSimplex]
  constructor
  · intro i
    fin_cases i
    exact hu.1
  · have hsum : ∑ i : Fin 1, ((i : ℝ) + 1) * u i = u 0 := by simp
    rw [hsum]
    exact hu.2.trans (by norm_num)

private theorem halfInterval_strictSubset_weightedSimplex :
    halfInterval ⊂ Set.weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) (1 : ℕ) := by
  refine ⟨halfInterval_subset_weightedSimplex, ?_⟩
  intro hsubset
  let u : Fin 1 → ℝ := fun _ ↦ 3 / 4
  have hu : u ∈ Set.weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) (1 : ℕ) := by
    rw [Set.mem_weightedSimplex]
    constructor
    · intro i
      norm_num [u]
    · have hsum : ∑ i : Fin 1, ((i : ℝ) + 1) * u i = 3 / 4 := by simp [u]
      rw [hsum]
      norm_num
  have hnot : u ∉ halfInterval := by
    change ¬ (0 ≤ u 0 ∧ u 0 ≤ 1 / 2)
    norm_num [u]
  exact hnot (hsubset hu)

/-- At the fractional cutoff `3 / 2`, the area integral on `[0, 1 / 2]` is bounded by the
partition-support dimension at that cutoff. -/
example : (1 : ℝ) / 2 *
      ∫ u in halfInterval, (max (3 / 2 - ∑ i : Fin 1, u i) 0) ^ 2 ≤
        (Module.finrank ℚ (partitionSupportSpace ℚ 1 1 1 (3 / 2 : ℝ) one_pos) : ℝ) := by
  simpa using partitionSupport_dimension_ge_integral_on (F := ℚ) (D := 1) (d := 1) (W := 1)
    (L := 3 / 2) one_pos halfInterval_strictSubset_weightedSimplex.subset

/-- On the proper subinterval `[0, 1/2]` of the simplex at `d = W = 1`, the positive-part
integral is bounded by the dimension at cutoff `1`. -/
example : (1 : ℝ) / 2 *
      ∫ u in halfInterval, (max (1 - ∑ i : Fin 1, u i) 0) ^ 2 ≤
        (Module.finrank ℚ (partitionSupportSpace ℚ 1 1 1 (1 : ℝ) one_pos) : ℝ) := by
  simpa [mul_one] using partitionSupport_dimension_ge_rate_integral_on (F := ℚ) (D := 1) (d := 1)
    (W := 1) (n := 1) (L := 1) (rate := 1) (level := 1) one_pos (by norm_num) (by norm_num)
    halfInterval_subset_weightedSimplex

/-- The cutoff `m * A` and level `m * agreement` give the rate integral bound on any subset
whose points are nonnegative and whose weighted coordinate sum is at most `W`. -/
example (F : Type*) [Field F] {D d n m A W : ℕ} {rate agreement : ℝ} (hD : 0 < D)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A)
    {S : Set (Fin d → ℝ)}
    (hcoordinates : ∀ u ∈ S, ∀ i, 0 ≤ u i)
    (hweight : ∀ u ∈ S, ∑ i, ((i.val + 1 : ℕ) : ℝ) * u i ≤ W) :
    (n : ℝ) / (2 * rate) *
        ∫ u in S, (max ((m : ℝ) * agreement - rate * ∑ i, u i) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  have hsubset : S ⊆ Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W := by
    intro u hu
    rw [Set.mem_weightedSimplex]
    refine ⟨hcoordinates u hu, ?_⟩
    calc
      ∑ i : Fin d, ((i : ℝ) + 1) * u i =
          ∑ i : Fin d, ((i.val + 1 : ℕ) : ℝ) * u i := by
        apply Finset.sum_congr rfl
        intro i _
        have hweight : (i : ℝ) + 1 = ((i.val + 1 : ℕ) : ℝ) := by
          push_cast
          rfl
        rw [hweight]
      _ ≤ W := hweight u hu
  apply partitionSupport_dimension_ge_rate_integral_on F hD hupper ?_ hsubset
  have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  push_cast
  linarith
