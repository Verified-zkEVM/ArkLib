/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FloorTransfer
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FiniteSurplus
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.LocalRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.MomentSource
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.RateBound
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.CurveCertificate
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Moment

/-!
# Partition-support acceptance cases

Concrete strict inclusion, dimension, lower-bound, integral, rank, and interpolant instances.
-/

open Finset MvPolynomial MeasureTheory PolynomialDifferential ReedSolomon.HiddenDerivative
  ReedSolomon.HiddenDerivative.RatePartition

/-- The large-order finite-ratio surplus at order `500`, rate `500`, and weight budget `1`. -/
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
    partitionSupport_largeOrder_finiteRatio_surplus (F := ℚ) (D := 1) (d := 500) (m := 1)
      (n := 1) (L := 3000) (rate := 500) (agreement := Real.log 3000)
      one_pos (by omega) one_pos (by norm_num) hlog (by rw [hbudget]; norm_num)
      (by norm_num) (by simpa using hlevel)

private theorem largeWeightLowerTailMoment :
    (27 / 10 : ℝ) < ⨍ u in Set.weightedSimplex
      (fun i : Fin 500 ↦ (i : ℝ) + 1) (100000000 : ℝ),
        (max (Real.log 3000 - ((500 : ℕ) : ℝ) * (∑ i, u i) / 100000000) 0) ^ 2 := by
  simpa only [show (6 * (500 : ℕ) : ℝ) = 3000 by norm_num] using
    setAverage_weightedSimplex_succ_lowerTail_sq_gt (d := 500) (by norm_num)
      (W := (100000000 : ℝ)) (by norm_num)

private theorem largeWeightSurplusEnvelope :
    ((100000000 : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2) *
        Real.exp ((500 : ℝ) / 100000000 * (1 + (501 : ℕ).choose 2)) *
          (1 / (((500 : ℝ) + 1) * ((500 : ℝ) / 100000000) ^ 2) +
            1 / ((500 : ℝ) / 100000000)) ≤
      (27 / 20 : ℝ) * ((100000000 : ℝ) / 500) ^ 2 *
        ((100000000 : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2) := by
  let volume : ℝ := (100000000 : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2
  have hchoose : (501 : ℕ).choose 2 = 125250 := by
    rw [Nat.choose_two_right]
  have hexpArg : (500 : ℝ) / 100000000 * (1 + (501 : ℕ).choose 2) ≤ 1 := by
    rw [hchoose]
    norm_num
  have hexp : Real.exp ((500 : ℝ) / 100000000 * (1 + (501 : ℕ).choose 2)) ≤ 3 := by
    calc
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hexpArg
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hfactor : Real.exp ((500 : ℝ) / 100000000 * (1 + (501 : ℕ).choose 2)) *
      (1 / (((500 : ℝ) + 1) * ((500 : ℝ) / 100000000) ^ 2) +
        1 / ((500 : ℝ) / 100000000)) ≤ (27 / 20 : ℝ) *
          ((100000000 : ℝ) / 500) ^ 2 := by
    calc
      _ ≤ 3 * (1 / (((500 : ℝ) + 1) * ((500 : ℝ) / 100000000) ^ 2) +
          1 / ((500 : ℝ) / 100000000)) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ (27 / 20 : ℝ) * ((100000000 : ℝ) / 500) ^ 2 := by norm_num
  have hvolume : 0 ≤ volume := by positivity
  have hvolume_def : volume =
      ((100000000 : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2) := rfl
  calc
    _ = volume * (Real.exp ((500 : ℝ) / 100000000 * (1 + (501 : ℕ).choose 2)) *
        (1 / (((500 : ℝ) + 1) * ((500 : ℝ) / 100000000) ^ 2) +
          1 / ((500 : ℝ) / 100000000))) := by
      rw [← hvolume_def]
      ac_rfl
    _ ≤ volume * ((27 / 20 : ℝ) * ((100000000 : ℝ) / 500) ^ 2) :=
      mul_le_mul_of_nonneg_left hfactor hvolume
    _ = _ := by
      rw [← hvolume_def]
      ac_rfl

private theorem largeWeightSurplusEnvelopeForTheorem :
      (1 : ℝ) * (((100000000 : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2) *
        Real.exp ((500 : ℝ) / 100000000 * (1 + (501 : ℕ).choose 2)) *
          (1 / (((500 : ℝ) + 1) * ((500 : ℝ) / 100000000) ^ 2) +
            1 / ((500 : ℝ) / 100000000))) ≤
      (27 / 10 : ℝ) / 2 * 1 * ((100000000 : ℝ) / 500) ^ 2 *
        ((100000000 : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2) := by
  calc
    _ = ((100000000 : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2) *
        Real.exp ((500 : ℝ) / 100000000 * (1 + (501 : ℕ).choose 2)) *
          (1 / (((500 : ℝ) + 1) * ((500 : ℝ) / 100000000) ^ 2) +
            1 / ((500 : ℝ) / 100000000)) := by simp only [one_mul]
    _ ≤ (27 / 20 : ℝ) * ((100000000 : ℝ) / 500) ^ 2 *
        ((100000000 : ℝ) ^ 500 / (Nat.factorial 500 : ℝ) ^ 2) :=
      largeWeightSurplusEnvelope
    _ = _ := by
      rw [show (27 / 10 : ℝ) / 2 = 27 / 20 by norm_num,
        show (100000000 : ℝ) / 500 = 200000 by norm_num]
      ac_rfl

private noncomputable def largeWeightCutoff : ℕ :=
  ⌈(200000 : ℝ) * Real.log (3000 : ℝ)⌉₊

private theorem largeWeightLevel_le_cutoff :
    (200000 : ℝ) * Real.log (3000 : ℝ) * ((1 : ℕ) : ℝ) ≤ (largeWeightCutoff : ℝ) := by
  have h := Nat.le_ceil ((200000 : ℝ) * Real.log (3000 : ℝ))
  simpa [largeWeightCutoff] using h

/-- A positive-order finite-surplus instance with a positive surplus multiplier. -/
example :
    (localDerivativeCoordinateBudget 500 1 100000000 : ℝ) <
      (Module.finrank ℚ
        (partitionSupportSpace ℚ 1 500 100000000
          largeWeightCutoff one_pos) : ℝ) := by
  have hbudget := partitionSupport_surplus (F := ℚ) (D := 1) (d := 500)
    (W := 100000000) (n := 1) (L := largeWeightCutoff) (m := 1)
    (rate := 1) (level := (200000 : ℝ) * Real.log (3000 : ℝ)) (logarithm := Real.log 3000)
    (μ := 27 / 10) (γ := 1) one_pos (by norm_num) (by norm_num)
    (by norm_num) largeWeightLevel_le_cutoff
    (by norm_num [show (100000000 : ℝ) / 500 = 200000 by norm_num])
    largeWeightLowerTailMoment (by norm_num)
    (by simpa only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_add]
      using largeWeightSurplusEnvelopeForTheorem)
  simpa only [Nat.cast_one, one_mul] using hbudget

/-- The same strict surplus bounds the rank of a concrete local constraint map. -/
example :
    Module.finrank ℚ (LinearMap.range
      (partitionSupportLocalConstraint (d := 500) (W := 100000000)
        (L := largeWeightCutoff) 1 one_pos (0 : ℚ) 0)) <
      (Module.finrank ℚ
        (partitionSupportSpace ℚ 1 500 100000000
          largeWeightCutoff one_pos) : ℝ) := by
  have hbudget := partitionSupport_localConstraint_surplus (F := ℚ) (D := 1) (d := 500)
    (W := 100000000) (n := 1) (L := largeWeightCutoff) (m := 1)
    (rate := 1) (level := (200000 : ℝ) * Real.log (3000 : ℝ)) (logarithm := Real.log 3000)
    (μ := 27 / 10) (γ := 1) one_pos (by norm_num) (by norm_num)
    (by norm_num) largeWeightLevel_le_cutoff
    (by norm_num [show (100000000 : ℝ) / 500 = 200000 by norm_num])
    largeWeightLowerTailMoment (by norm_num)
    (by simpa only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_add]
      using largeWeightSurplusEnvelopeForTheorem)
    (0 : ℚ) 0
  simpa only [Nat.cast_one, one_mul] using hbudget

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

example : (1 : ℝ) / 2 *
      ∫ u in halfInterval, (max (3 / 2 - ∑ i : Fin 1, u i) 0) ^ 2 ≤
        (Module.finrank ℚ (partitionSupportSpace ℚ 1 1 1 (3 / 2 : ℝ) one_pos) : ℝ) := by
  simpa using partitionSupport_dimension_ge_integral_on (F := ℚ) (D := 1) (d := 1) (W := 1)
    (L := 3 / 2) one_pos halfIntervalSubsetWeightedSimplex

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

private theorem finiteRatioBudget_pos : 0 < partitionWeightBudget 1 1 500 6 := by
  rw [partitionWeightBudget]
  apply Nat.floor_pos.mpr
  have hlogpos : 0 < Real.log (3000 : ℝ) := Real.log_pos (by norm_num)
  have hloglt : Real.log (3000 : ℝ) < 3000 := by
    exact (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)).trans (by norm_num)
  push_cast
  norm_num
  exact (le_div_iff₀ hlogpos).2 (by linarith)

/-- At order `500`, the lower-tail moment verifies a concrete finite-ratio surplus. -/
example : partitionFiniteRatio 1 1 500 6 * 1 *
    localDerivativeCoordinateBudget 500 6 (partitionWeightBudget 1 1 500 6) <
      Module.finrank ℚ (partitionSupportSpace ℚ 1 500
        (partitionWeightBudget 1 1 500 6) ((6 * 1 : ℕ) : ℝ) one_pos) := by
  have hW : 0 < (partitionWeightBudget 1 1 500 6 : ℕ) := finiteRatioBudget_pos
  have hW' : 0 < (partitionWeightBudget 1 1 500 6 : ℝ) := by exact_mod_cast hW
  have hmoment : (27 / 10 : ℝ) <
      ⨍ u in Set.weightedSimplex (fun i : Fin 500 ↦ (i : ℝ) + 1)
          (partitionWeightBudget 1 1 500 6 : ℝ),
        (max (Real.log (6 * (500 : ℝ)) - 500 * (∑ i, u i) /
          partitionWeightBudget 1 1 500 6) 0) ^ 2 := by
    simpa using setAverage_weightedSimplex_succ_lowerTail_sq_gt
      (d := 500) (by norm_num) hW'
  simpa only [Nat.cast_one] using
    partitionSupport_finiteRatio_surplus (F := ℚ) (D := 1) (d := 500) (n := 1) (m := 6)
      (A := 1) (rate := 1) (agreement := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hW (by norm_num) (by norm_num) hmoment

private def twoCenters : Fin 2 ↪ ℚ where
  toFun i := i.val
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

private noncomputable def zeroReceived : Fin 2 → Polynomial ℚ := fun _ ↦ 0

example : Nonempty (SymbolicReceivedCurve.Certificate 2 2 0 1 0 0 twoCenters zeroReceived) := by
  simpa using exists_partitionSupport_curve_certificate
    (D := 1) (d := 0) (m := 1) (W := 0) (n := 2) (A := 2) (k := 2) (ℓ := 0) (ν := 1)
    (L := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    twoCenters zeroReceived (by intro i; simp [zeroReceived])
    (by
      intro u hu
      have h : u none + 1 * totalJetDegree u < 2 := by
        exact_mod_cast hu.2
      omega)
    (by
      have hcard : (partitionSupportExponents 1 0 0 (2 : ℝ) (by norm_num)).card =
          partitionSourceCount 1 0 0 2 := by
        simpa using
          (card_partitionSupportExponents (D := 1) (d := 0) (W := 0) (by norm_num) 2)
      rw [hcard]
      norm_num [partitionSourceCount, localDerivativeCoordinateBudget, contactThreshold,
        weightedHigherJetCount, Finset.natWeightedSimplex, Finset.sum_range_succ])
