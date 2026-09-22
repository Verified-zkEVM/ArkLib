/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Dimension
public import ArkLib.Data.Finset.WeightedSimplex.FloorTransfer

/-!
# From the lattice sum to an integral over the weighted simplex

The rate form of the dimension bound in `PartitionSupport/Dimension.lean` is a sum over the
lattice points `c` of the simplex `∑_i (i + 1) c_i ≤ W` of `(max (level - rate ∑_i c_i) 0) ^ 2`.
Flooring a point `u` of the continuous simplex `∑_i (i + 1) u_i ≤ W` gives a lattice point of the
same simplex whose coordinate sum is at most `∑_i u_i`. For `0 ≤ rate` the integrand
`(max (level - rate ∑_i u_i) 0) ^ 2` can only grow under flooring, and the unit cells of the
lattice points have volume one, so the integral over the whole simplex is at most the lattice sum.
Combined with the rate form, the integral bounds the dimension of the partition support space from
below.

## Main statements

* `partition_floor_square_integral`: the integral is at most the lattice sum.
* `partitionSupport_dimension_ge_rate_integral`: the integral form of the dimension bound.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/`
`PartitionSupport/FloorTransfer.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `partition_floor_square_integral` keeps its statement, with the source's `weightedSimplex d W`
  written `Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W`. The source's cell argument is
  `Finset.setIntegral_le_sum_natWeightedSimplex` of
  `ArkLib.Data.Finset.WeightedSimplex.FloorTransfer` applied to the whole simplex.
* `partitionSupport_dimension_ge_rate_integral` has the hypotheses of
  `partitionSupport_dimension_ge_rate_sum`: a real level and a natural cutoff with
  `level * n ≤ L` replace `m * agreement` and `m * A`, and `0 < n` and `0 < rate` are dropped.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Finset MeasureTheory

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ}

/-- For `0 ≤ rate`, the integral of `(max (level - rate ∑_i u_i) 0) ^ 2` over the continuous
simplex `∑_i (i + 1) u_i ≤ W` is at most the sum of `(max (level - rate ∑_i c_i) 0) ^ 2` over the
lattice points `c` of the same simplex. The point `u` lies in the unit cell of its floor, and
flooring lowers the coordinate sum. The hypothesis `0 ≤ rate` makes the integrand nonincreasing
in the coordinate sum, which is what the comparison on each cell uses. -/
theorem partition_floor_square_integral (d W : ℕ) (level rate : ℝ) (hrate : 0 ≤ rate) :
    ∫ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
        (max (level - rate * ∑ i, u i) 0) ^ 2 ≤
      ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (max (level - rate * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 := by
  have hweights : (fun i : Fin d ↦ (i : ℝ) + 1) = fun i ↦ ((i.val + 1 : ℕ) : ℝ) := by
    funext i
    push_cast
    rfl
  have hpos : ∀ i : Fin d, 0 < ((i : ℝ) + 1) := fun i => by positivity
  have h := setIntegral_le_sum_natWeightedSimplex (w := fun i : Fin d ↦ i.val + 1)
    (fun i ↦ Nat.succ_ne_zero _) (W := (W : ℝ)) (Set.measurableSet_weightedSimplex _ _)
    (hweights ▸ subset_rfl : Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W ⊆
      Set.weightedSimplex (fun i ↦ ((i.val + 1 : ℕ) : ℝ)) W)
    (f := fun u ↦ (max (level - rate * ∑ i, u i) 0) ^ 2)
    (g := fun c ↦ (max (level - rate * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2)
    (ContinuousOn.integrableOn_weightedSimplex hpos (by fun_prop))
    (fun c _ ↦ by positivity) fun u hu ↦ ?_
  · simpa only [Nat.floor_natCast] using h
  have hu0 := (Set.mem_weightedSimplex.mp hu).1
  have hfloor : ((∑ i, ⌊u i⌋₊ : ℕ) : ℝ) ≤ ∑ i, u i := by
    push_cast
    exact sum_le_sum fun i _ ↦ Nat.floor_le (hu0 i)
  exact pow_le_pow_left₀ (le_max_right _ _)
    (max_le_max_right 0 (sub_le_sub_left (mul_le_mul_of_nonneg_left hfloor hrate) level)) 2

/-- The integral form of the dimension bound: if `0 < D ≤ rate * n` and `level * n ≤ L`, then
`n / (2 rate)` times the integral of `(max (level - rate ∑_i u_i) 0) ^ 2` over the continuous
simplex `∑_i (i + 1) u_i ≤ W` is at most the dimension of the partition support space at the
natural cutoff `L`. -/
theorem partitionSupport_dimension_ge_rate_integral (F : Type*) [Field F] {n L : ℕ}
    {rate level : ℝ} (hD : 0 < D) (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L) :
    (n : ℝ) / (2 * rate) *
        ∫ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
          (max (level - rate * ∑ i, u i) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  have hrn : 0 < rate * n := (Nat.cast_pos.mpr hD).trans_le hupper
  have hrate : 0 < rate := pos_of_mul_pos_left hrn (Nat.cast_nonneg n)
  exact (mul_le_mul_of_nonneg_left (partition_floor_square_integral d W level rate hrate.le)
    (by positivity)).trans (partitionSupport_dimension_ge_rate_sum F hD hupper hlevel)

end ReedSolomon.HiddenDerivative
