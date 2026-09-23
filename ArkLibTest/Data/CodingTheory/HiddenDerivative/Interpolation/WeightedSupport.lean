/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Estimate
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Interpolation
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankBound
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Moments

/-!
# Weighted-support acceptance cases

Concrete eligibility, dimension, probability, interpolation, rank, residual, volume, and moment
instances for the weighted-support statements.
-/

open Finset MeasureTheory Set MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators ProbabilityTheory

example : WeightedSupportEligible 2 2 1 4
    ((jetExponentCoordinatesEquiv (d := 2) (by norm_num)).symm (1, 0, 0, fun _ => 1)) :=
  (weightedSupportEligible_coordinates_iff (by norm_num) 1 0 0 _).mpr ⟨by decide, by norm_num⟩

example : 5 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 2 1 2 one_pos) := by
  refine le_trans (le_of_eq ?_) (sum_count_le_finrank_weightedSupportSpace ℚ (d := 2) (W := 1)
    (L := 2) (by norm_num) one_pos)
  have hs : natWeightedSimplex (fun i : Fin (2 - 1) => i.val + 1) 1 = {fun _ => 0, fun _ => 1} := by
    decide
  have h1 : ⌈(1 : ℝ)⌉₊ = 1 := by exact_mod_cast Nat.ceil_natCast 1
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  rw [hs, sum_pair (by decide)]
  norm_num [CubicStaircase.count, h1, h2, Finset.sum_range_succ]

example : 5 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 3 one_pos) := by
  have h := weightedSupport_dimension_ge_cubic_sum ℚ (d := 1) (W := 0) (L := 3) (by norm_num)
    one_pos
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by decide
  rw [hs, sum_singleton] at h
  norm_num at h
  have h4 : (4 : ℝ) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 3 one_pos) := by linarith
  exact_mod_cast h4

example : 21 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 5 16 one_pos) := by
  have h := weighted_dimension_probability ℚ (d := 1) (D := 1) (W := 5) (by norm_num) one_pos 1 8
    (by norm_num [harmonic])
  have hS : weightedSimplex (fun i : Fin (1 - 1) ↦ (i : ℝ) + 1) (5 : ℕ) = univ := by
    ext u
    simp [mem_weightedSimplex]
  have havg : ⨍ u in weightedSimplex (fun i : Fin (1 - 1) ↦ (i : ℝ) + 1) (5 : ℕ),
      (max (5 / 8 - normalizedRadius (5 : ℕ) (1 * 8) u) 0) ^ 3 = (5 / 8 : ℝ) ^ 3 := by
    rw [hS, Measure.restrict_univ]
    simp [normalizedRadius]
    norm_num
  rw [havg, show (8 : ℝ) * ((1 : ℕ) : ℝ) * (1 + 1) = 16 by norm_num] at h
  norm_num at h
  have h20 : (20 : ℝ) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 5 16 one_pos) := by linarith
  exact_mod_cast h20

private theorem eightLeCardWeightedSupportExponents :
    8 ≤ #(weightedSupportExponents 2 1 0 4 two_pos) := by
  refine le_trans (le_of_eq ?_) (sum_count_le_card_weightedSupportExponents (d := 1) (W := 0)
    (L := 4) one_pos two_pos)
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by decide
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  have h4 : ⌈(4 : ℝ)⌉₊ = 4 := by exact_mod_cast Nat.ceil_natCast 4
  rw [hs, sum_singleton]
  norm_num [CubicStaircase.count, h2, h4, Finset.sum_range_succ]

private theorem threePointSurplus :
    Fintype.card (Fin 3) * localResidualCoordinateBudget 1 1 0
        ⌈(4 : ℝ) / ((2 : ℕ) : ℝ)⌉₊ < #(weightedSupportExponents 2 1 0 4 two_pos) := by
  have hceil : ⌈(4 : ℝ) / ((2 : ℕ) : ℝ)⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [hceil, show localResidualCoordinateBudget 1 1 0 2 = 2 by decide, Fintype.card_fin]
  exact (show 3 * 2 < 8 by norm_num).trans_le eightLeCardWeightedSupportExponents

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ weightedSupportSpace ℚ 2 1 0 4 two_pos ∧
      ∀ _ : Fin 3, SatisfiesLocalConstraints 1 0 0 Q :=
  exists_nonzero_weightedSupport_interpolant one_pos two_pos (fun _ : Fin 3 => (0 : ℚ))
    (fun _ : Fin 3 => (0 : ℚ)) threePointSurplus

example : Module.finrank ℚ (LinearMap.range
    (weightedSupportLocalConstraint (D := 2) (d := 1) (W := 0) (L := 4) 2 (by norm_num)
      (0 : ℚ) (0 : ℚ))) ≤ 4 := by
  have hceil : ⌈(4 : ℝ) / ((2 : ℕ) : ℝ)⌉₊ = 2 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have h := finrank_weightedSupportLocalConstraint_le (D := 2) (d := 1) (W := 0) (L := 4)
    (m := 2) one_pos (by norm_num) (0 : ℚ) (0 : ℚ)
  rw [hceil] at h
  exact h.trans (by decide)

private theorem natWeightedSimplexFinZero (W : ℕ) :
    natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) W = {fun _ => 0} := by
  ext c
  have hc : c = fun _ => 0 := funext fun i => Fin.elim0 i
  subst hc
  simp only [Finset.mem_singleton, iff_true]
  exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => Fin.elim0 i, by simp⟩

private theorem ceilTwentyOneDivTen : ⌈(21 / 10 : ℝ)⌉₊ = 3 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

example :
    (localResidualCoordinateBudget 1 2 0 ⌈(21 / 10 : ℝ)⌉₊ : ℝ) = 6 ∧
      ∑ r ∈ range 2, (contactThreshold 2 2 r : ℝ) *
        ∑ z ∈ natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) (0 + r),
          (max ((21 / 10 : ℝ) - ((∑ i, z i : ℕ) : ℝ)) 0 + 1) = 31 / 5 ∧
      (6 : ℝ) ≤ 31 / 5 := by
  have hb : localResidualCoordinateBudget 1 2 0 3 = 6 := by decide
  have h := localResidualCoordinateBudget_le_positivePart_sum 1 2 0 (21 / 10)
  have hc0 : contactThreshold 2 2 0 = 1 := by decide
  have hc1 : contactThreshold 2 2 1 = 1 := by decide
  simp only [ceilTwentyOneDivTen, hb, natWeightedSimplexFinZero, sum_range_succ,
    range_zero, sum_empty, sum_singleton, Nat.reduceAdd, hc0, hc1] at h ⊢
  norm_num at h ⊢

example : (1 : ℝ) ≤ 567 / 128 := by
  have hH : (harmonic 2 : ℝ) = 3 / 2 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have h := weighted_residual_sum_le_volume_mul_harmonic_variance 2 0 (T := 0)
    (by norm_num [hH, Nat.choose])
  have hset : Finset.natWeightedSimplex (fun i : Fin 2 ↦ i.val + 1) 0 = {fun _ ↦ 0} := by
    decide
  rw [hset, volume_real_weightedSimplex_succ 2 (by positivity)] at h
  norm_num [hH, Nat.choose, Nat.factorial, Fin.sum_univ_two] at h
  linarith

example : ∑ i : Fin 4, (i.val + 1) = 10 := by
  rw [sum_fin_succ_eq_choose_two]
  rfl

example : (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * 0 ^ 2 ≤
    ∫ _x, (max (5 / 8 - (0 : ℝ)) 0) ^ 3 ∂Measure.dirac (0 : ℝ) :=
  contribution_integral_lower (Measure.dirac (0 : ℝ)) (fun _ ↦ 0) 0 (integrable_const _)
    (by simp) (by simp) (by norm_num) (by simp) (by simp)
