/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MeasureTheory.Integral.NatFloorCells
import ArkLib.ToMathlib.MeasureTheory.Integral.PositivePart
import Mathlib.Data.Fin.VecNotation
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Acceptance cases for finite floor cells and positive-part moments

Concrete instances check a floor-cell membership and volume, and the finite-average positive-part
bound for a two-point sample.
-/

open MeasureTheory Set
open scoped BigOperators

/-- The two-dimensional cell with lower corner `(2, 0)` has volume one. -/
example : volume (natFloorCell ![2, 0]) = 1 := volume_natFloorCell _

/-- A nonnegative point lies in the cell indexed by its natural floor. -/
example :
    (fun _ : Unit ↦ (3 / 2 : ℝ)) ∈
      natFloorCell (fun _ : Unit ↦ ⌊(3 / 2 : ℝ)⌋₊) := by
  exact mem_natFloorCell_natFloor (fun _ ↦ by norm_num)

/-- The cell of `(3 / 2)` is indexed by its natural floor `1`. -/
example :
    (fun _ : Unit ↦ (3 / 2 : ℝ)) ∈ natFloorCell (fun _ : Unit ↦ 1) ↔
      ∀ i, ⌊(fun _ : Unit ↦ (3 / 2 : ℝ)) i⌋₊ = 1 := by
  exact mem_natFloorCell_iff_natFloor_eq (fun _ ↦ by norm_num)

/-- Distinct one-dimensional floor cells are disjoint. -/
example : Disjoint (natFloorCell (fun _ : Unit ↦ 0)) (natFloorCell (fun _ ↦ 1)) := by
  apply pairwise_disjoint_natFloorCell
  intro h
  have := congrFun h ()
  norm_num at this

/-- On the cell `[1, 2)`, the coefficient `2` gives the lower linear-form bound `2 ≤ 3`. -/
example :
    (∑ _i : Unit, (2 : ℝ) * 1) ≤ ∑ _i : Unit, (2 : ℝ) * (3 / 2) := by
  have hx : (fun _ : Unit ↦ (3 / 2 : ℝ)) ∈ natFloorCell (fun _ : Unit ↦ 1) := by
    simp [mem_natFloorCell]
    norm_num
  simpa using sum_mul_le_sum_mul_of_mem_natFloorCell
    (c := fun _ : Unit ↦ 1) (x := fun _ : Unit ↦ (3 / 2 : ℝ))
    (a := fun _ : Unit ↦ (2 : ℝ)) (fun _ ↦ by norm_num) hx

/-- On the same cell, the linear form is at most its corner value plus its coefficient. -/
example :
    (∑ _i : Unit, (2 : ℝ) * (3 / 2)) ≤
      (∑ _i : Unit, (2 : ℝ) * 1) + ∑ _i : Unit, (2 : ℝ) := by
  have hx : (fun _ : Unit ↦ (3 / 2 : ℝ)) ∈ natFloorCell (fun _ : Unit ↦ 1) := by
    simp [mem_natFloorCell]
    norm_num
  simpa using sum_mul_le_sum_mul_add_sum_of_mem_natFloorCell
    (c := fun _ : Unit ↦ 1) (x := fun _ : Unit ↦ (3 / 2 : ℝ))
    (a := fun _ : Unit ↦ (2 : ℝ)) (fun _ ↦ by norm_num) hx

private def twoCells (i : Fin 2) : Set ℝ := Set.Ico (i.val : ℝ) (i.val + 1)

/-- A nonconstant integrand over two unit cells is bounded by their endpoint sum. -/
example :
    ∫ x in ⋃ i ∈ (Finset.univ : Finset (Fin 2)), twoCells i, x ∂(volume : Measure ℝ) ≤ 3 := by
  calc
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 2)), (i.val + 1 : ℝ) := by
      apply setIntegral_biUnion_le_sum (s := Finset.univ) (cell := twoCells)
        (f := fun x : ℝ ↦ x) (w := fun i ↦ (i.val + 1 : ℝ))
      · intro i hi
        simp [twoCells]
      · intro i hi j hj hij
        fin_cases i <;> fin_cases j <;> simp_all [twoCells, Set.disjoint_left, Set.mem_Ico]
      · intro i hi
        have hIcc : IntegrableOn (fun x : ℝ ↦ x) (Set.Icc (i.val : ℝ) (i.val + 1)) volume :=
          continuous_id.integrableOn_Icc
        exact hIcc.mono_set Ico_subset_Icc_self
      · intro i hi
        simp [twoCells]
      · intro i hi
        positivity
      · intro i hi x hx
        exact hx.2.le
    _ = 3 := by norm_num [Fin.sum_univ_two]

/-- The two cells `[0, 1)` and `[1, 2)` give a positive lower sum for `x` on `[0, 2]`. -/
example :
    1 ≤ ∫ x in Set.Icc (0 : ℝ) 2, x ∂(volume : Measure ℝ) := by
  calc
    1 = ∑ i ∈ (Finset.univ : Finset (Fin 2)), (i.val : ℝ) := by norm_num [Fin.sum_univ_two]
    _ ≤ ∫ x in Set.Icc (0 : ℝ) 2, x ∂volume := by
      apply sum_le_setIntegral_of_measure_eq_one (s := Finset.univ) (cell := twoCells)
        (S := Set.Icc (0 : ℝ) 2) (f := fun x : ℝ ↦ x) (w := fun i ↦ (i.val : ℝ))
      · intro i hi
        simp [twoCells]
      · intro i hi j hj hij
        fin_cases i <;> fin_cases j <;> simp_all [twoCells, Set.disjoint_left, Set.mem_Ico]
      · intro i hi
        simp [twoCells]
      · intro i hi x hx
        fin_cases i <;> simp [twoCells, Set.mem_Ico] at hx ⊢ <;> constructor <;> linarith
      · exact measurableSet_Icc
      · exact continuous_id.integrableOn_Icc
      · intro x hx
        exact hx.1
      · intro i hi x hx
        exact hx.1

/-- For the sample `(0, 2)`, the threshold `2` gives the bound `1 ≤ 1 + 1 / 4`. -/
example : 𝔼 i, max (2 - (![0, 2] : Fin 2 → ℚ) i) 0 ≤ 5 / 4 := by
  have hmean : 𝔼 i, (![0, 2] : Fin 2 → ℚ) i = 1 := by
    simp [Finset.expect, Fin.sum_univ_two, NNRat.smul_def]
  have h := Finset.expect_max_sub_zero_le (s := Finset.univ) (![0, 2] : Fin 2 → ℚ) (c := 2)
    hmean (by norm_num)
  have hvar : 𝔼 i, ((![0, 2] : Fin 2 → ℚ) i - 1) ^ 2 = 1 := by
    simp [Finset.expect, Fin.sum_univ_two, NNRat.smul_def]
    norm_num
  rw [hvar] at h
  linarith

private noncomputable def halfProbability : ↥(Set.Icc (0 : ℝ) 1) :=
  ⟨(1 / 2 : ℝ), by norm_num⟩

private noncomputable def twoPointMeasure : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure false true halfProbability

local instance : IsProbabilityMeasure twoPointMeasure := by
  change IsProbabilityMeasure (ProbabilityTheory.bernoulliMeasure false true halfProbability)
  infer_instance

private def twoPointY (b : Bool) : ℝ := if b then 2 else 0

/-- A balanced two-point probability has nonzero variance and satisfies the positive-part bound. -/
example :
    ∫ x, max (2 - twoPointY x) 0 ∂twoPointMeasure ≤
      2 - 1 + (∫ x, (twoPointY x - 1) ^ 2 ∂twoPointMeasure) / (4 * (2 - 1)) := by
  apply MeasureTheory.integral_max_sub_zero_le twoPointMeasure twoPointY 2 1
  · exact Integrable.of_finite
  · rw [twoPointMeasure, ProbabilityTheory.integral_bernoulliMeasure]
    norm_num [twoPointY, halfProbability]
  · exact Integrable.of_finite
  · norm_num

/-- The set-average bound also holds on the full two-point space for a nonconstant function. -/
example :
    ∫ x in (Set.univ : Set Bool), max (2 - twoPointY x) 0 ∂twoPointMeasure ≤
      twoPointMeasure.real Set.univ *
        (2 - 1 + (⨍ x in (Set.univ : Set Bool), (twoPointY x - 1) ^ 2 ∂twoPointMeasure) /
          (4 * (2 - 1))) := by
  apply MeasureTheory.setIntegral_max_sub_zero_le twoPointY
  · rw [integrableOn_univ]
    exact (Integrable.of_finite : Integrable twoPointY twoPointMeasure)
  · rw [setAverage_eq]
    simp only [Measure.restrict_univ, measureReal_def, IsProbabilityMeasure.measure_univ,
      ENNReal.toReal_one, inv_one, one_smul]
    rw [twoPointMeasure, ProbabilityTheory.integral_bernoulliMeasure]
    norm_num [twoPointY, halfProbability]
  · rw [integrableOn_univ]
    exact (Integrable.of_finite :
      Integrable (fun x ↦ (twoPointY x - 1) ^ 2) twoPointMeasure)
  · norm_num

private def twoPointZ (b : Bool) : ℝ := if b then 1 else -1

/-- For a balanced two-point mean-zero variable, the cubic moment lower bound is attained. -/
example :
    1 ^ 3 + 3 * 1 * (∫ x, twoPointZ x ^ 2 ∂twoPointMeasure) -
        ∫ x, twoPointZ x ^ 3 ∂twoPointMeasure ≤
      ∫ x, (max (1 - twoPointZ x) 0) ^ 3 ∂twoPointMeasure := by
  apply MeasureTheory.le_integral_max_sub_zero_pow_three twoPointMeasure twoPointZ 1
  · exact Integrable.of_finite
  · exact Integrable.of_finite
  · rw [twoPointMeasure, ProbabilityTheory.integral_bernoulliMeasure]
    norm_num [twoPointZ, halfProbability]

/-- The Jensen cubic bound has a strict `1 ≤ 4` instance for the same nonconstant variable. -/
example : 1 ^ 3 ≤ ∫ x, (max (1 - twoPointZ x) 0) ^ 3 ∂twoPointMeasure := by
  apply MeasureTheory.pow_three_le_integral_max_sub_zero_pow_three twoPointMeasure twoPointZ 1
  · exact Integrable.of_finite
  · rw [twoPointMeasure, ProbabilityTheory.integral_bernoulliMeasure]
    norm_num [twoPointZ, halfProbability]
  · exact Integrable.of_finite
