/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Dimension

/-!
# Acceptance tests for the partition support dimension bounds

The staircase form of the dimension at `d = 0`, the lower bounds at the cutoff `m * A` with
level `m * agreement`, and the failure of `partition_quadratic_rate_lower` without either of its
hypotheses `D ≤ rate * n` and `level * n ≤ L`.

At real cutoffs: the bound for the number of eligible exponents, a concrete instance at the cutoff
`5 / 2` where the real bound exceeds the natural bound at `⌊5 / 2⌋`, and a failure of the rate
form
when `level * n ≤ L` is dropped.
-/

open Finset PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At `d = 0`, `D = 2`, `L = 3` the only tuple is empty and the dimension is the staircase count
`QuadraticStaircase.count 2 (3 / 2 - 0)`, which is `4` by the partition count test. -/
example : Module.finrank ℚ (partitionSupportSpace ℚ 2 0 0 ((3 : ℕ) : ℝ) two_pos) =
    QuadraticStaircase.count 2 ((3 : ℕ) / (2 : ℕ) - ((0 : ℕ) : ℝ)) := by
  rw [finrank_partitionSupportSpace_eq_sum_count]
  simp [natWeightedSimplex]

/-- The quadratic lower bound at the cutoff `m * A`. -/
example (F : Type*) [Field F] {D d m A W : ℕ} (hD : 0 < D) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (D : ℝ) * (max ((m * A : ℕ) / (D : ℝ) - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 / 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) :=
  partitionSupport_dimension_ge_quadratic_sum F hD (m * A)

/-- The rate lower bound at level `m * agreement`, cutoff `m * A`, and `agreement * n ≤ A`. -/
example (F : Type*) [Field F] {D d n m A W : ℕ} {rate agreement : ℝ} (hD : 0 < D)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A) :
    (n : ℝ) / (2 * rate) *
        ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
          (max ((m : ℝ) * agreement - rate * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (m * A : ℕ) hD) : ℝ) := by
  refine partitionSupport_dimension_ge_rate_sum F hD hupper ?_
  have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  push_cast
  linarith

/-- `partition_quadratic_rate_lower` needs `D ≤ rate * n`: at `D = n = L = level = 1`,
`rate = 1 / 2`, `deg = 0` the left side is `1` and the right side is `1 / 2`. -/
example : ¬ (((1 : ℕ) : ℝ) / (2 * (1 / 2)) * (max (1 - 1 / 2 * ((0 : ℕ) : ℝ)) 0) ^ 2 ≤
    ((1 : ℕ) : ℝ) *
      (max (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) 0) ^ 2 / 2) := by
  norm_num

/-- `partition_quadratic_rate_lower` needs `level * n ≤ L`: at `D = n = rate = L = 1`,
`level = 2`, `deg = 0` the left side is `2` and the right side is `1 / 2`. -/
example : ¬ (((1 : ℕ) : ℝ) / (2 * 1) * (max (2 - 1 * ((0 : ℕ) : ℝ)) 0) ^ 2 ≤
    ((1 : ℕ) : ℝ) *
      (max (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) 0) ^ 2 / 2) := by
  norm_num

/-- With both hypotheses, `D = 1 ≤ rate * n = 1` and `level * n = 1 ≤ L = 1`, the bound holds at
`deg = 0`, where both sides are `1 / 2`. -/
example : ((1 : ℕ) : ℝ) / (2 * 1) * (max (1 - 1 * ((0 : ℕ) : ℝ)) 0) ^ 2 ≤
    ((1 : ℕ) : ℝ) *
      (max (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) 0) ^ 2 / 2 :=
  partition_quadratic_rate_lower (D := 1) (n := 1) (L := 1) one_pos (by norm_num) (by norm_num)

/-! ### Real cutoffs -/

section

open Finset

/-- The quadratic lower bound for the number of eligible exponents at a real cutoff. -/
example {D d W : ℕ} {L : ℝ} (hD : 0 < D) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (D : ℝ) * (max (L / D - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 / 2 ≤
      (#(partitionSupportExponents D d W L hD) : ℝ) := by
  rw [← finrank_partitionSupportSpace_eq_card (F := ℚ)]
  exact partitionSupport_dimension_ge_quadratic_sum_real ℚ hD L

/-- With no visible jets the only tuple is empty. -/
private theorem natWeightedSimplex_fin_zero (W : ℕ) :
    natWeightedSimplex (fun i : Fin 0 => i.val + 1) W = {0} := by
  ext c
  simp [mem_natWeightedSimplex, Subsingleton.elim c 0]

/-- At `D = 1`, `d = 0`, `W = 0` and the cutoff `5 / 2`, the bound is
`(5 / 2) ^ 2 / 2 = 25 / 8`. The natural-cutoff bound at `⌊5 / 2⌋ = 2` gives only `2`.
The dimension itself is `3 + 2 + 1`. -/
example : (25 / 8 : ℝ) ≤
    Module.finrank ℚ (partitionSupportSpace ℚ 1 0 0 (5 / 2 : ℝ) one_pos) ∧
    Module.finrank ℚ (partitionSupportSpace ℚ 1 0 0 (5 / 2 : ℝ) one_pos) = 6 := by
  constructor
  · have h := partitionSupport_dimension_ge_quadratic_sum_real ℚ (d := 0) (W := 0) one_pos
      (5 / 2 : ℝ)
    rw [natWeightedSimplex_fin_zero, sum_singleton] at h
    norm_num at h
    exact h
  · rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
      show ⌈(5 / 2 : ℝ)⌉₊ = 3 by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num]
    decide

/-- The rate form needs `level * n ≤ L`: at `D = n = rate = 1`, `d = W = 0`, the level `10` and
the cutoff `1 / 2`, the left side is `1 / 2 * 10 ^ 2 = 50`, while the space contains only the
constant monomial. -/
example : (Module.finrank ℚ (partitionSupportSpace ℚ 1 0 0 (1 / 2 : ℝ) one_pos) : ℝ) <
    ((1 : ℕ) : ℝ) / (2 * 1) * ∑ c ∈ natWeightedSimplex (fun i : Fin 0 => i.val + 1) 0,
      (max ((10 : ℝ) - 1 * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil,
    show ⌈(1 / 2 : ℝ)⌉₊ = 1 by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num,
    natWeightedSimplex_fin_zero, sum_singleton,
    show partitionSourceCount 1 0 0 1 = 1 by decide]
  norm_num

end

/-- The real-variable comparison allows a continuous coordinate sum `t`: at `D = n = 2`,
`rate = 1`, `level = 2`, `L = 4` and `t = 1`, both sides are `1`. -/
example : (2 : ℝ) / (2 * 1) * (max (2 - 1 * 1) 0) ^ 2 ≤
    (2 : ℝ) / 2 * (max (4 / 2 - 1) 0) ^ 2 :=
  partition_quadratic_rate_lower_real (D := 2) (n := 2) (rate := 1) (L := 4) (level := 2)
    (t := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The real-variable comparison fails without `D ≤ rate * n`: with `D = 1`,
`n = level = L = 1`, `rate = 1/2` and `t = 0`, the left side is `1` and the right side is `1/2`.
-/
example : ¬ ((1 : ℝ) / (2 * (1 / 2)) * (max (1 - (1 / 2) * 0) 0) ^ 2 ≤
    (1 : ℝ) / 2 * (max (1 / 1 - 0) 0) ^ 2) := by
  norm_num

/-- The real-variable comparison fails without `n * level ≤ L`: at `D = n = rate = L = 1`,
`level = 2` and `t = 0`, the left side is `2` and the right side is `1/2`. -/
example : ¬ ((1 : ℝ) / (2 * 1) * (max (2 - 1 * 0) 0) ^ 2 ≤
    (1 : ℝ) / 2 * (max (1 / 1 - 0) 0) ^ 2) := by
  norm_num
/-! ### Staircase slots -/

private theorem emptyTuple_mem_natWeightedSimplex :
    (0 : Fin 0 → ℕ) ∈ natWeightedSimplex (fun i : Fin 0 => i.val + 1) 0 := by
  apply (mem_natWeightedSimplex (w := fun i : Fin 0 => i.val + 1)
    (hw := fun i => Nat.succ_ne_zero i.val)).2
  simp

private noncomputable def xCoefficientAreaSlot : PartitionSupportAreaSlot 2 0 0 3 :=
  ⟨⟨0, emptyTuple_mem_natWeightedSimplex⟩, ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩⟩⟩

private noncomputable def constantCoefficientAreaSlot : PartitionSupportAreaSlot 2 0 0 3 :=
  ⟨⟨0, emptyTuple_mem_natWeightedSimplex⟩, ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩⟩

/-- At `D = 2` and `L = 3`, two valid staircase slots represent `X` and the constant monomial. -/
example :
    partitionSupportAreaSlotExponent xCoefficientAreaSlot none = 1 ∧
      partitionSupportAreaSlotExponent constantCoefficientAreaSlot none = 0 := by
  constructor <;> rfl

/-- The distinct slots for `X` and the constant monomial have distinct exponents. -/
example : partitionSupportAreaSlotExponent xCoefficientAreaSlot ≠
    partitionSupportAreaSlotExponent constantCoefficientAreaSlot := by
  intro h
  have hslots := partitionSupportAreaSlotExponent_injective h
  have hX := congrArg (fun p => p.2.exponents.1) hslots
  change (1 : ℕ) = 0 at hX
  omega

/-- Each of these concrete area slots gives an exponent in the partition support. -/
example :
    partitionSupportAreaSlotExponent xCoefficientAreaSlot ∈
      partitionSupportExponents 2 0 0 3 two_pos ∧
      partitionSupportAreaSlotExponent constantCoefficientAreaSlot ∈
        partitionSupportExponents 2 0 0 3 two_pos := by
  constructor <;> apply mem_partitionSupportExponents.mpr
  · exact partitionSupportAreaSlotExponent_eligible two_pos xCoefficientAreaSlot
  · exact partitionSupportAreaSlotExponent_eligible two_pos constantCoefficientAreaSlot

private def zeroDerivativeTuple : Fin 1 → ℕ := fun _ => 0

private def unitDerivativeTuple : Fin 1 → ℕ := fun _ => 1

private theorem zeroDerivativeTuple_mem_natWeightedSimplex :
    zeroDerivativeTuple ∈ natWeightedSimplex (fun i : Fin 1 => i.val + 1) 1 := by
  apply (mem_natWeightedSimplex (hw := fun i : Fin 1 => Nat.succ_ne_zero i.val)).2
  norm_num [zeroDerivativeTuple]

private theorem unitDerivativeTuple_mem_natWeightedSimplex :
    unitDerivativeTuple ∈ natWeightedSimplex (fun i : Fin 1 => i.val + 1) 1 := by
  apply (mem_natWeightedSimplex (hw := fun i : Fin 1 => Nat.succ_ne_zero i.val)).2
  norm_num [unitDerivativeTuple]

private noncomputable def zeroDerivativeAreaSlot : PartitionSupportAreaSlot 2 1 1 5 :=
  ⟨⟨zeroDerivativeTuple, zeroDerivativeTuple_mem_natWeightedSimplex⟩,
    ⟨⟨0, by norm_num [zeroDerivativeTuple, QuadraticStaircase.Slot]⟩,
      ⟨0, by norm_num [zeroDerivativeTuple, QuadraticStaircase.Slot]⟩⟩⟩

private noncomputable def unitDerivativeAreaSlot : PartitionSupportAreaSlot 2 1 1 5 :=
  ⟨⟨unitDerivativeTuple, unitDerivativeTuple_mem_natWeightedSimplex⟩,
    ⟨⟨0, by norm_num [unitDerivativeTuple, QuadraticStaircase.Slot]⟩,
      ⟨0, by norm_num [unitDerivativeTuple, QuadraticStaircase.Slot]⟩⟩⟩

/-- With `d = 1`, the slots for derivative tuples `0` and `1` have the corresponding `Y₁`
exponents. -/
example :
    partitionSupportAreaSlotExponent zeroDerivativeAreaSlot (some (0 : Fin 1).succ) = 0 ∧
      partitionSupportAreaSlotExponent unitDerivativeAreaSlot (some (0 : Fin 1).succ) = 1 := by
  constructor <;> rfl

/-- The `d = 1` slots with different derivative tuples give distinct exponents by injectivity. -/
example : partitionSupportAreaSlotExponent zeroDerivativeAreaSlot ≠
    partitionSupportAreaSlotExponent unitDerivativeAreaSlot := by
  intro h
  have hslots := partitionSupportAreaSlotExponent_injective h
  have hc := congrArg (fun p => p.1.val 0) hslots
  norm_num [zeroDerivativeAreaSlot, unitDerivativeAreaSlot, zeroDerivativeTuple,
    unitDerivativeTuple] at hc

/-- At `D = 0`, no staircase slot represents the eligible exponent `Y₀`, so positive `D` is needed
for the slot enumeration to cover the partition support. -/
example : ¬ Nonempty (PartitionSupportAreaSlot 0 0 0 1) ∧
    PartitionSupportEligible 0 0 0 1 (partitionSourceExponent 0 1 0) := by
  constructor
  · rintro ⟨⟨c, slot⟩⟩
    have hbound := slot.1.isLt
    norm_num at hbound
  · rw [partitionSupportEligible_partitionSourceExponent_iff]
    simp
