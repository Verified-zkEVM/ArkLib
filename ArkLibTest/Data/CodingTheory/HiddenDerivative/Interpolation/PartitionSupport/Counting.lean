/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting

/-!
# Acceptance tests for the partition support count

A small dimension computed from the exact count, the exact count at the cutoff `m * A`, the
coordinates of a concrete exponent, and the failure of the count at `D = 0`, where every exponent
of `Y₀` is eligible.

At real cutoffs: dimensions at non-integral cutoffs computed through `⌈L⌉₊`, the boundary `L = 0`
where the space is zero, a small positive cutoff where only the constant monomial survives, the
count with the `Y₀` exponent summed over `range (L + 1)`, positivity, and the total jet degree
bound.
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

/-- The exact count at the cutoff `m * A`. -/
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

/-! ### Real cutoffs -/

section

open Finset

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

/-- The count with the `Y₀` exponent summed over `range (L + 1)`: the extra term
`L - D (L + ∑_i c_i)` vanishes because `0 < D`. -/
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

/-- A positive cutoff gives an eligible exponent. -/
example {D d W : ℕ} {L : ℝ} (hD : 0 < D) (hL : 0 < L) :
    0 < #(partitionSupportExponents D d W L hD) :=
  (card_partitionSupportExponents_pos_iff hD).mpr hL

/-- The total jet degree bound at the exponent `X Y₀ Y₁` for
`D = 2`, `L = 7`: its coarse weight is `1 + 2 · 2 = 5 < 7`, so its total jet degree `2` is below
`7 / 2`. -/
example : ((totalJetDegree (partitionSourceExponent 1 1 ![1]) : ℕ) : ℝ) < 7 / 2 := by
  apply totalJetDegree_lt_of_partitionSupportEligible (D := 2) (W := 1) two_pos
  rw [partitionSupportEligible_partitionSourceExponent_iff]
  norm_num

end
