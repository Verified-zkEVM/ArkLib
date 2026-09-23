/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FiniteSurplus

/-!
# Acceptance tests for the partition surplus

The real form of `(d + 1).choose 2` from Mathlib, `localDerivativeCoordinateBudget` written
out, and the surplus with moment constant `27 / 10`, level `m * agreement` and cutoff `m * A`,
for any `γ ≥ 0` satisfying the envelope inequality.
-/

open Finset MeasureTheory PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The finite-ratio surplus at order `500`, rate `500` and multiplicity `1`, with weight budget
`1` and cutoff `3000`. -/
example :
    RatePartition.partitionFiniteRatio 500 (Real.log 3000) 500 1 * (1 : ℝ) *
      localDerivativeCoordinateBudget 500 1
        (RatePartition.partitionWeightBudget 500 (Real.log 3000) 500 1) <
      (Module.finrank ℚ
        (partitionSupportSpace ℚ 1 500
          (RatePartition.partitionWeightBudget 500 (Real.log 3000) 500 1) (3000 : ℝ) one_pos) :
          ℝ) := by
  have hlog : 0 < Real.log (3000 : ℝ) := Real.log_pos (by norm_num)
  have hbudget : RatePartition.partitionWeightBudget 500 (Real.log 3000) 500 1 = 1 := by
    unfold RatePartition.partitionWeightBudget
    norm_num only [Nat.cast_one, Nat.cast_ofNat]
    rw [show (1 : ℝ) * Real.log 3000 * 500 / (500 * Real.log 3000) = 1 by
      field_simp [ne_of_gt hlog]]
    norm_num
  have hlogbound : Real.log (3000 : ℝ) ≤ 3000 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3000 by norm_num)
    linarith
  have hlevel : (1 : ℝ) * Real.log 3000 * 1 ≤ (3000 : ℝ) := by
    simpa using hlogbound
  simpa only [Nat.cast_one, Nat.cast_ofNat, one_mul, mul_one] using
    partitionSupport_finiteRatio_surplus (F := ℚ) (D := 1) (d := 500) (m := 1)
      (n := 1) (L := 3000) (rate := 500) (agreement := Real.log 3000)
      one_pos (by omega) one_pos (by norm_num) hlog (by rw [hbudget]; norm_num)
      (by norm_num) (by simpa using hlevel)

/-- `(d + 1).choose 2 = d (d + 1) / 2` in `ℝ`, from Mathlib's `Nat.cast_choose_two`. -/
example (d : ℕ) : ((d + 1).choose 2 : ℝ) = (d : ℝ) * (d + 1) / 2 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- `localDerivativeCoordinateBudget d m W` unfolds to its defining sum. -/
example (d m W : ℕ) : localDerivativeCoordinateBudget d m W =
    ∑ r ∈ range m, ((m - r) ⌈/⌉ (d + 1)) * weightedHigherJetCount (d + 1) (W + r) := rfl

/-- The surplus with moment constant `27 / 10`, level `m * agreement`, cutoff `m * A`, and any
`γ ≥ 0` whose product with the geometric envelope equals
`27 / 20 * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2)`. -/
example (F : Type*) [Field F] {D d n m A W : ℕ} {rate agreement logarithm γ : ℝ}
    (hD : 0 < D) (hd : 0 < d) (hW : 0 < W)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A)
    (hlevel : rate * W / d * logarithm ≤ m * agreement)
    (hmoment : (27 / 10 : ℝ) < ⨍ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
      (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2)
    (hγ : 0 ≤ γ)
    (henvelope : γ * (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W))) =
      27 / 20 * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2)) :
    γ * n * localDerivativeCoordinateBudget d m W <
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  have hcutoff : (m : ℝ) * agreement * n ≤ ((m * A : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    push_cast
    linarith
  refine partitionSupport_surplus F hD hd hW hupper hcutoff hlevel hmoment hγ ?_
  rw [henvelope]
  norm_num

/-- The rank of the local constraint map of order `m = 1` on the partition support space at
`d = 1`, `W = 1` is at most the budget `⌈1 / 2⌉ * N_2(1) = 2`, over `ℚ` and for every cutoff. -/
example (L : ℝ) (center received : ℚ) :
    Module.finrank ℚ (LinearMap.range
      (partitionSupportLocalConstraint (d := 1) (D := 1) (W := 1) (L := L) 1 one_pos center
        received)) ≤ 2 :=
  (finrank_partitionSupportLocalConstraint_le one_pos center received).trans (by decide)
