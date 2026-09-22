/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.RatePartition.Basic

/-!
# Acceptance tests for the rate-partition support at a real cutoff

Dimensions at non-integral cutoffs computed through `⌈L⌉₊`, the boundary `L = 0` where the space
is zero, a small positive cutoff where only the constant monomial survives, and the source forms of
`card_ratePartitionExponents_eq_dimensionCount`, `card_ratePartitionExponents_pos` and
`totalJetDegree_lt_of_ratePartitionEligible`.
-/

open Finset PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At `D = 1`, `d = 1`, `W = 1`, the real cutoff `3 / 2` gives the space at the natural cutoff
`2`, of dimension `4`. -/
example : Module.finrank ℚ (partitionSupportSpace ℚ 1 1 1 (3 / 2 : ℝ) one_pos) = 4 := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
    show ⌈(3 / 2 : ℝ)⌉₊ = 2 by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num]
  decide

/-- At the cutoff `1 / 2` only the constant monomial is eligible, for every derivative budget: the
dimension is `1` at `W = 3`. -/
example : Module.finrank ℚ (partitionSupportSpace ℚ 1 1 3 (1 / 2 : ℝ) one_pos) = 1 := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
    show ⌈(1 / 2 : ℝ)⌉₊ = 1 by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num]
  decide

/-- The positivity of the cutoff is needed: at `L = 0` the space is zero, even with a large
derivative budget. -/
example : Module.finrank ℚ (partitionSupportSpace ℚ 2 3 10 0 two_pos) = 0 := by
  have h := (finrank_partitionSupportSpace_pos_iff (F := ℚ) (d := 3) (W := 10) (L := 0)
    two_pos).not
  simpa using h

/-- A negative cutoff gives the zero space, through the count at `⌈L⌉₊ = 0`. -/
example : Module.finrank ℚ (partitionSupportSpace ℚ 1 2 5 (-3) one_pos) = 0 := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
    Nat.ceil_eq_zero.mpr (by norm_num)]
  simp [partitionSourceCount]

/-- Source shape `card_ratePartitionExponents_eq_dimensionCount`: the source sums the `Y₀` exponent
over `range (L + 1)`. The extra term `L - D (L + ∑_i c_i)` vanishes because `0 < D`. -/
example {D d W L : ℕ} (hD : 0 < D) :
    #(partitionSupportExponents D d W (L : ℝ) hD) =
      ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        ∑ u ∈ range (L + 1), (L - D * (u + ∑ i, c i)) := by
  rw [card_partitionSupportExponents, partitionSourceCount]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_range_succ, Nat.sub_eq_zero_of_le
    ((Nat.le_add_right L _).trans (Nat.le_mul_of_pos_left _ hD)), add_zero]

/-- The extra term is needed only for `D = 0`: there the `range (L + 1)` form and `range L` form
differ, `partitionSourceCount 0 0 0 2 = 4` against `6`. -/
example : partitionSourceCount 0 0 0 2 = 4 ∧
    ∑ c ∈ natWeightedSimplex (fun i : Fin 0 => i.val + 1) 0,
      ∑ u ∈ range (2 + 1), (2 - 0 * (u + ∑ i, c i)) = 6 := by
  decide

/-- Source shape `card_ratePartitionExponents_pos`. -/
example {D d W : ℕ} {L : ℝ} (hD : 0 < D) (hL : 0 < L) :
    0 < #(partitionSupportExponents D d W L hD) :=
  (card_partitionSupportExponents_pos_iff hD).mpr hL

/-- Source shape `totalJetDegree_lt_of_ratePartitionEligible`, at the exponent `X Y₀ Y₁` for
`D = 2`, `L = 7`: its coarse weight is `1 + 2 · 2 = 5 < 7`, so its total jet degree `2` is below
`7 / 2`. -/
example : ((totalJetDegree (partitionSourceExponent 1 1 ![1]) : ℕ) : ℝ) < 7 / 2 := by
  apply totalJetDegree_lt_of_partitionSupportEligible (D := 2) (W := 1) two_pos
  rw [partitionSupportEligible_partitionSourceExponent_iff]
  norm_num
