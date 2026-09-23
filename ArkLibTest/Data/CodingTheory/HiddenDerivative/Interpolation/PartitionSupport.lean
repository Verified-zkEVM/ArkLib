/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FloorTransfer
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.LocalRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.MomentSource
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.RateBound
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Moment

/-!
# Partition-support acceptance cases

Concrete strict inclusion, dimension, lower-bound, integral, rank, and interpolant instances.
-/

open Finset MvPolynomial MeasureTheory PolynomialDifferential ReedSolomon.HiddenDerivative
  ReedSolomon.HiddenDerivative.RatePartition

/-- A concrete `d = 500` lower-tail moment feeds the partition-support dimension bound. -/
example :
    (27 / 10 : ℝ) / 2 * ((1 : ℕ) : ℝ) * 1 *
        (((1 : ℕ) : ℝ) / ((500 : ℕ) : ℝ)) ^ 2 *
        (((1 : ℕ) : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2) <
      (Module.finrank ℚ (partitionSupportSpace ℚ 1 500 1 ((10 : ℕ) : ℝ) one_pos) : ℝ) := by
  have hlog : (0 : ℝ) < 3000 := by norm_num
  have hlogBound : Real.log 3000 ≤ 2999 := by
    simpa only [show (3000 : ℝ) - 1 = 2999 by norm_num] using
      Real.log_le_sub_one_of_pos hlog
  have hlevel : Real.log 3000 / 500 * (1 : ℕ) ≤ (10 : ℕ) := by
    have h : Real.log 3000 / 500 ≤ 10 := by
      calc
        Real.log 3000 / 500 ≤ 2999 / 500 := div_le_div_of_nonneg_right hlogBound (by norm_num)
        _ ≤ 10 := by norm_num
    norm_num at h ⊢
    exact h
  have hscale : (1 : ℝ) * (1 : ℕ) / (500 : ℕ) * Real.log 3000 ≤ Real.log 3000 / 500 := by
    norm_num
    ring_nf
    exact le_rfl
  have hmoment := setAverage_weightedSimplex_succ_lowerTail_sq_gt (d := 500)
    (by norm_num) (W := (1 : ℝ)) one_pos
  exact partitionSupport_dimension_gt_moment (F := ℚ) (D := 1) (d := 500) (W := 1)
    (n := 1) (L := 10) (rate := 1) (level := Real.log 3000 / 500)
    (logarithm := Real.log 3000) (μ := 27 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simpa using hlevel) (by simpa using hscale)
    (by simpa only [Nat.cast_one, Nat.cast_ofNat,
      show (6 : ℝ) * 500 = 3000 by norm_num] using hmoment)

private theorem YOneWeights :
    fullHigherJetWeight (d := 1) (Finsupp.single (some 1) 1) = 0 ∧
      fullDerivativeJetWeight (d := 1) (Finsupp.single (some 1) 1) = 1 ∧
      totalJetDegree (d := 1) (Finsupp.single (some 1) 1) = 1 := by
  simp [fullHigherJetWeight, fullDerivativeJetWeight, totalJetDegree, Finsupp.weight_single,
    jetHigherWeight, jetDerivativeWeight]

example : X (some 1) ∈ weightedSupportSpace ℚ 1 1 0 2 one_pos ∧
    X (some 1) ∉ partitionSupportSpace ℚ 1 1 0 2 one_pos := by
  obtain ⟨hw, hd, ht⟩ := YOneWeights
  refine ⟨mem_weightedSupportSpace_iff.mpr fun u hu => ?_, fun h => ?_⟩
  · rw [X] at hu
    obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hu)
    refine ⟨hw.le, ?_⟩
    simp only [ht]
    norm_num
  · have := (mem_partitionSupportSpace_iff.mp h (Finsupp.single (some 1) 1)
      (by simp [X, support_monomial])).1
    omega

example : Module.finrank ℚ (partitionSupportSpace ℚ 1 1 1 (3 / 2 : ℝ) one_pos) = 4 := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
    show ⌈(3 / 2 : ℝ)⌉₊ = 2 by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num]
  decide

example :
    ((1 : ℕ) : ℝ) / (2 * (1 : ℝ)) * (max (1 - 1 * ((0 : ℕ) : ℝ)) 0) ^ 2 ≤
      ((1 : ℕ) : ℝ) * (max (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) 0) ^ 2 / 2 :=
  partition_quadratic_rate_lower (D := 1) (n := 1) (L := 1) one_pos (by norm_num) (by norm_num)

private theorem natWeightedSimplexFinZero (W : ℕ) :
    natWeightedSimplex (fun i : Fin 0 => i.val + 1) W = {0} := by
  ext c
  simp [mem_natWeightedSimplex, Subsingleton.elim c 0]

example :
    (25 / 8 : ℝ) ≤ Module.finrank ℚ (partitionSupportSpace ℚ 1 0 0 (5 / 2 : ℝ) one_pos) ∧
      Module.finrank ℚ (partitionSupportSpace ℚ 1 0 0 (5 / 2 : ℝ) one_pos) = 6 := by
  constructor
  · have h := partitionSupport_dimension_ge_quadratic_sum_real ℚ (d := 0) (W := 0) one_pos
      (5 / 2 : ℝ)
    rw [natWeightedSimplexFinZero, sum_singleton] at h
    norm_num at h
    exact h
  · rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
      show ⌈(5 / 2 : ℝ)⌉₊ = 3 by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num]
    decide

private theorem emptyTupleMemNatWeightedSimplex :
    (0 : Fin 0 → ℕ) ∈ natWeightedSimplex (fun i : Fin 0 => i.val + 1) 0 := by
  rw [natWeightedSimplexFinZero]
  simp

private noncomputable def xCoefficientAreaSlot : PartitionSupportAreaSlot 2 0 0 3 :=
  ⟨⟨0, emptyTupleMemNatWeightedSimplex⟩, ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩⟩⟩

private noncomputable def constantCoefficientAreaSlot : PartitionSupportAreaSlot 2 0 0 3 :=
  ⟨⟨0, emptyTupleMemNatWeightedSimplex⟩, ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩⟩

example :
    partitionSupportAreaSlotExponent xCoefficientAreaSlot ∈
        partitionSupportExponents 2 0 0 3 two_pos ∧
      partitionSupportAreaSlotExponent constantCoefficientAreaSlot ∈
        partitionSupportExponents 2 0 0 3 two_pos ∧
      partitionSupportAreaSlotExponent xCoefficientAreaSlot ≠
        partitionSupportAreaSlotExponent constantCoefficientAreaSlot := by
  refine ⟨(mem_partitionSupportExponents).mpr
      (partitionSupportAreaSlotExponent_eligible two_pos xCoefficientAreaSlot),
    (mem_partitionSupportExponents).mpr
      (partitionSupportAreaSlotExponent_eligible two_pos constantCoefficientAreaSlot), ?_⟩
  intro h
  have hslots := partitionSupportAreaSlotExponent_injective h
  have hX := congrArg (fun p => p.2.exponents.1) hslots
  change (1 : ℕ) = 0 at hX
  omega

private theorem natWeightedSimplexOneOne :
    natWeightedSimplex (fun i : Fin 1 => i.val + 1) 1 = {![0], ![1]} := by
  decide

example : ∫ u in Set.weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) ((1 : ℕ) : ℝ),
    (max (2 - 1 * ∑ i, u i) 0) ^ 2 ≤ 5 := by
  refine (partition_floor_square_integral 1 1 2 1 zero_le_one).trans (le_of_eq ?_)
  rw [natWeightedSimplexOneOne, sum_pair (by decide)]
  norm_num

private def halfInterval : Set (Fin 1 → ℝ) := {u | 0 ≤ u 0 ∧ u 0 ≤ 1 / 2}

private theorem halfIntervalSubsetWeightedSimplex :
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

private theorem halfIntervalStrictSubsetWeightedSimplex :
    halfInterval ⊂ Set.weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) (1 : ℕ) := by
  refine ⟨halfIntervalSubsetWeightedSimplex, ?_⟩
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

example : (1 : ℝ) / 2 *
      ∫ u in halfInterval, (max (3 / 2 - ∑ i : Fin 1, u i) 0) ^ 2 ≤
        (Module.finrank ℚ (partitionSupportSpace ℚ 1 1 1 (3 / 2 : ℝ) one_pos) : ℝ) := by
  simpa using partitionSupport_dimension_ge_integral_on (F := ℚ) (D := 1) (d := 1) (W := 1)
    (L := 3 / 2) one_pos halfIntervalStrictSubsetWeightedSimplex.subset

example : (1 : ℝ) / 2 *
      ∫ u in halfInterval, (max (1 - ∑ i : Fin 1, u i) 0) ^ 2 ≤
        (Module.finrank ℚ (partitionSupportSpace ℚ 1 1 1 (1 : ℝ) one_pos) : ℝ) := by
  simpa [mul_one] using partitionSupport_dimension_ge_rate_integral_on (F := ℚ) (D := 1) (d := 1)
    (W := 1) (n := 1) (L := 1) (rate := 1) (level := 1) one_pos (by norm_num) (by norm_num)
    halfIntervalSubsetWeightedSimplex

example : Module.finrank ℚ (LinearMap.range
    (partitionSupportLocalConstraint (d := 1) (W := 0) (L := 2) 2 one_pos
      (0 : ℚ) (0 : ℚ))) ≤ 3 := by
  exact (finrank_partitionSupportLocalConstraint_le one_pos (0 : ℚ) (0 : ℚ)).trans (by decide)

example :
    totalJetDegree (Finsupp.single (some 0 : JetVariable 1) 1) ≤ rateJetCap (1 / 2) 1 := by
  apply partitionSupport_totalJetDegree_le_rateJetCap (D := 2) (W := 1) (m := 1) (n := 4)
    (A := 4) (rate := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp [PartitionSupportEligible, fullDerivativeJetWeight, totalJetDegree,
    jetDerivativeWeight, Finsupp.weight_single]
  norm_num

example : ∃ Q : DifferentialPolynomial ℚ 0, Q ≠ 0 ∧
    Q ∈ partitionSupportSpace ℚ 1 0 0 ((2 : ℕ) : ℝ) one_pos ∧
      ∀ _ : Fin 1, SatisfiesLocalConstraints 1 0 0 Q := by
  refine exists_nonzero_partitionSupport_interpolant one_pos (fun _ : Fin 1 => (0 : ℚ))
    (fun _ => 0) ?_
  rw [card_partitionSupportExponents]
  decide
