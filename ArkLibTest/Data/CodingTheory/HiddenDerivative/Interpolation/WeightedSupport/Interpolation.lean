/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Interpolation

/-!
# Acceptance cases for weighted-support interpolation

At `d = 1`, `D = 2`, `W = 0`, `L = 4`, `m = 1` the cutoff is `⌈4 / 2⌉₊ = 2`, the local budget is
`localResidualCoordinateBudget 1 1 0 2 = 2`, and the weighted support space has at least `8`
exponents. Three received points use `3 * 2 = 6 < 8` coordinates, so a nonzero interpolant exists
in the weighted support space and, with `A = 4` and `M = 2`, in the exact interpolation space.
With no received points the global map has rank `0`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative Finset

/-- The local budget at `d = 1`, `m = 1`, `W = 0`, cutoff `2`: the contact threshold is `1`, the
only higher-jet tuple is empty, and it leaves `2` values of the `Y₁`-degree. -/
example : localResidualCoordinateBudget 1 1 0 2 = 2 := by decide

/-- The weighted support space at `d = 1`, `D = 2`, `W = 0`, `L = 4` has at least
`count 2 2 = 1 * 4 + 2 * 2 = 8` exponents. -/
theorem eight_le_card_weightedSupportExponents :
    8 ≤ #(weightedSupportExponents 2 1 0 4 two_pos) := by
  refine le_trans (le_of_eq ?_) (sum_count_le_card_weightedSupportExponents (d := 1) (W := 0)
    (L := 4) one_pos two_pos)
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by decide
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  have h4 : ⌈(4 : ℝ)⌉₊ = 4 := by exact_mod_cast Nat.ceil_natCast 4
  rw [hs, sum_singleton]
  norm_num [CubicStaircase.count, h2, h4, Finset.sum_range_succ]

/-- The dimension surplus for three points: `3 * localResidualCoordinateBudget 1 1 0 ⌈4 / 2⌉₊`
is `6 < 8`. -/
theorem three_points_surplus :
    Fintype.card (Fin 3) * localResidualCoordinateBudget 1 1 0 ⌈(4 : ℝ) / ((2 : ℕ) : ℝ)⌉₊ <
      #(weightedSupportExponents 2 1 0 4 two_pos) := by
  have hceil : ⌈(4 : ℝ) / ((2 : ℕ) : ℝ)⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [hceil, show localResidualCoordinateBudget 1 1 0 2 = 2 by decide, Fintype.card_fin]
  exact (show 3 * 2 < 8 by norm_num).trans_le eight_le_card_weightedSupportExponents

/-- Three received points leave a nonzero `Q` in the weighted support space satisfying every local
constraint of order `1`. -/
example (centers received : Fin 3 → ℚ) :
    ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧ Q ∈ weightedSupportSpace ℚ 2 1 0 4 two_pos ∧
      ∀ i, SatisfiesLocalConstraints 1 (centers i) (received i) Q :=
  exists_nonzero_weightedSupport_interpolant one_pos two_pos centers received three_points_surplus

/-- The same interpolant lies in the exact interpolation space with `A = 4`, `M = 2`: the cutoff
hypotheses are `4 ≤ 1 * 4` and `4 ≤ 2 * 2`. -/
example (centers received : Fin 3 → ℚ) :
    ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
      Q ∈ exactInterpolationSpace ℚ 2 4 1 1 2 0 (by norm_num) ∧
      ∀ i, SatisfiesLocalConstraints 1 (centers i) (received i) Q :=
  exists_nonzero_exact_interpolant_of_weightedSupport_surplus one_pos two_pos (by norm_num)
    centers received (by norm_num) (by norm_num) three_points_surplus

/-- With no received points the global constraint map has rank `0 = 0 * budget`. -/
example : Module.finrank ℚ (LinearMap.range (weightedSupportGlobalConstraint (F := ℚ)
    (ι := Fin 0) (d := 1) (m := 1) (W := 0) (L := 4) two_pos Fin.elim0 Fin.elim0)) = 0 := by
  have h := finrank_weightedSupportGlobalConstraint_le (F := ℚ) (ι := Fin 0) (d := 1) (m := 1)
    (W := 0) (L := 4) one_pos two_pos Fin.elim0 Fin.elim0
  simpa using h
