/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting

/-!
# Acceptance tests for the partition support count

A small dimension computed from the exact count, the source statement at the cutoff `m * A`, the
coordinates of a concrete exponent, and the failure of the count at `D = 0`, where every exponent
of `Y₀` is eligible.
-/

open Finset PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At `D = 1`, `d = 1`, `W = 1`, `L = 2`: the tuple `c = 0` admits `b₀ ∈ {0, 1}` with `2 + 1`
choices of `x`, and `c = 1` admits `b₀ = 0` with one choice, so the count is `4`. -/
example : partitionSourceCount 1 1 1 2 = 4 := by decide

/-- The dimension of the corresponding space over `ℚ` is `4`. -/
example : Module.finrank ℚ (partitionSupportSpace ℚ 1 1 1 ((2 : ℕ) : ℝ) one_pos) = 4 := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount]
  decide

/-- At `d = 0` there are no higher jets and the count is the natural staircase:
`(3 - 0) + (3 - 2) + 0 = 4` at `D = 2`, `L = 3`. -/
example : Module.finrank ℚ (partitionSupportSpace ℚ 2 0 0 ((3 : ℕ) : ℝ) two_pos) = 4 := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount]
  decide

/-- Source shape `finrank_partitionSupportSpace_eq_sourceCount`, at the cutoff `m * A`. -/
example (F : Type*) [Field F] {D d m A W : ℕ} (hD : 0 < D) :
    Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) =
      ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        ∑ b₀ ∈ range (m * A), (m * A - D * (b₀ + ∑ i, c i)) :=
  finrank_partitionSupportSpace_eq_partitionSourceCount F hD (m * A)

/-- The exponent `X^2 Y₀ Y₁^3 Y₂` at `d = 2` has derivative-order weight `1 * 3 + 2 * 1 = 5` and
total jet degree `1 + 3 + 1 = 5`. -/
example : fullDerivativeJetWeight (partitionSourceExponent 2 1 ![3, 1]) = 5 ∧
    totalJetDegree (partitionSourceExponent 2 1 ![3, 1]) = 5 := by
  rw [fullDerivativeJetWeight_eq_sum_succ, totalJetDegree_eq_zero_add_sum_succ]
  simp [Fin.sum_univ_two]

/-- The count needs `0 < D`: at `D = 0` the exponent `Y₀^b` is eligible for every `b`, so the
eligible set is infinite, while the range `b₀ < L` of `partitionSourceCount` omits `b ≥ L`. -/
example (d : ℕ) (b : ℕ) :
    PartitionSupportEligible 0 d 0 1 (partitionSourceExponent 0 b (0 : Fin d → ℕ)) := by
  rw [partitionSupportEligible_partitionSourceExponent_iff]
  simp
