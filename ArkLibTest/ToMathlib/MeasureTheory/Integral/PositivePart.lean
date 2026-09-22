/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MeasureTheory.Integral.PositivePart
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Acceptance cases for the positive-part bound by mean and variance

These cases evaluate the finite-average bound on a two-point sample, check that the pointwise bound
is attained at `y = μ` and `y = 2 * c - μ`, show that `μ < c` is needed, check the empty average,
and apply the probability-measure bound to a Dirac measure. For the cube of the positive part they
show the bound is attained by a symmetric two-point variable and that the mean-zero hypothesis is
needed.
-/

open MeasureTheory
open scoped BigOperators

/-- The sample `(0, 2)` has mean `1` and average squared deviation `1`. With threshold `2` the
bound is `1 + 1 / 4`; the actual average of `max (2 - Y) 0` is `1`. -/
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

/-- The pointwise bound is attained at `y = μ` and at `y = 2 * c - μ`; here `μ = 1`, `c = 2`. -/
example : max ((2 : ℚ) - 1) 0 = 2 - 1 + (1 - 1) ^ 2 / (4 * (2 - 1)) ∧
    max ((2 : ℚ) - 3) 0 = 2 - 3 + (3 - 1) ^ 2 / (4 * (2 - 1)) := by
  norm_num

/-- The hypothesis `μ < c` is needed: at `μ = c = 0` and `y = 1` the right side is `-1`. -/
example : ¬ (max ((0 : ℚ) - 1) 0 ≤ 0 - 1 + (1 - 0) ^ 2 / (4 * (0 - 0))) := by
  norm_num

/-- For the empty set every average is zero, so the bound reads `0 ≤ c`. -/
example (c : ℚ) (hc : 0 < c) (Y : ℕ → ℚ) :
    𝔼 i ∈ (∅ : Finset ℕ), max (c - Y i) 0 ≤
      c - 0 + (𝔼 i ∈ (∅ : Finset ℕ), (Y i - 0) ^ 2) / (4 * (c - 0)) :=
  Finset.expect_max_sub_zero_le Y (by simp) hc

/-- For the probability measure `P` with mass `1 / 2` at `0` and at `2`, and `Y = id`, the mean
and the variance are `1`. With threshold `2` the theorem bounds `∫ max (2 - x) 0 ∂P = 1` by
`2 - 1 + 1 / 4`. -/
example : ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ ∫ x, x ∂P = 1 ∧
    ∫ x, (x - 1) ^ 2 ∂P = 1 ∧ ∫ x, max (2 - x) 0 ∂P = 1 ∧
    ∫ x, max (2 - x) 0 ∂P ≤ 2 - 1 + (∫ x, (x - 1) ^ 2 ∂P) / (4 * (2 - 1)) := by
  set P : Measure ℝ := (2 : ENNReal)⁻¹ • (Measure.dirac (0 : ℝ) + Measure.dirac 2)
  have : IsProbabilityMeasure P := ⟨by
    simp only [P, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩
  have hdirac : ∀ (a : ℝ) (f : ℝ → ℝ), Integrable f (Measure.dirac a) :=
    fun a f ↦ integrable_dirac (by simp)
  have hint : ∀ f : ℝ → ℝ, Integrable f P := fun f ↦
    ((hdirac 0 f).add_measure (hdirac 2 f)).smul_measure (by simp)
  have hP : ∀ f : ℝ → ℝ, ∫ x, f x ∂P = (f 0 + f 2) / 2 := by
    intro f
    rw [integral_smul_measure, integral_add_measure (hdirac 0 f) (hdirac 2 f), integral_dirac,
      integral_dirac]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
    ring
  have hmean : ∫ x, x ∂P = 1 := by rw [hP]; norm_num
  refine ⟨P, this, hmean, by rw [hP]; norm_num, by rw [hP]; norm_num, ?_⟩
  exact integral_max_sub_zero_le P id 2 1 (hint _) hmean (hint _) one_lt_two

/-- The cube bound is attained by `z = ±1` with probability `1 / 2` each and `b = 1`: the left side
is `1 + 3 * 1 - 0 = 4`, and `∫ (max (1 - z) 0) ^ 3 = (8 + 0) / 2 = 4`. -/
example : ∃ P : Measure ℝ, IsProbabilityMeasure P ∧
    (1 : ℝ) ^ 3 + 3 * 1 * (∫ x, x ^ 2 ∂P) - ∫ x, x ^ 3 ∂P = 4 ∧
    ∫ x, (max (1 - x) 0) ^ 3 ∂P = 4 ∧
    (1 : ℝ) ^ 3 + 3 * 1 * (∫ x, x ^ 2 ∂P) - ∫ x, x ^ 3 ∂P ≤ ∫ x, (max (1 - x) 0) ^ 3 ∂P := by
  set P : Measure ℝ := (2 : ENNReal)⁻¹ • (Measure.dirac (-1 : ℝ) + Measure.dirac 1)
  have : IsProbabilityMeasure P := ⟨by
    simp only [P, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩
  have hdirac : ∀ (a : ℝ) (f : ℝ → ℝ), Integrable f (Measure.dirac a) :=
    fun a f ↦ integrable_dirac (by simp)
  have hint : ∀ f : ℝ → ℝ, Integrable f P := fun f ↦
    ((hdirac (-1) f).add_measure (hdirac 1 f)).smul_measure (by simp)
  have hP : ∀ f : ℝ → ℝ, ∫ x, f x ∂P = (f (-1) + f 1) / 2 := by
    intro f
    rw [integral_smul_measure, integral_add_measure (hdirac (-1) f) (hdirac 1 f), integral_dirac,
      integral_dirac]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
    ring
  have hmean : ∫ x, x ∂P = 0 := by rw [hP]; norm_num
  refine ⟨P, this, by rw [hP, hP]; norm_num, by rw [hP]; norm_num, ?_⟩
  exact le_integral_max_sub_zero_pow_three P id 1 (hint _) (hint _) hmean

/-- The mean-zero hypothesis of `le_integral_max_sub_zero_pow_three` is needed: for `z = 1` under
a Dirac measure and `b = 1` the left side is `3` and the right side is `0`. -/
example : ¬ ((1 : ℝ) ^ 3 + 3 * 1 * (∫ _x, (1 : ℝ) ^ 2 ∂Measure.dirac (0 : ℝ)) -
      ∫ _x, (1 : ℝ) ^ 3 ∂Measure.dirac (0 : ℝ) ≤
    ∫ _x, (max ((1 : ℝ) - 1) 0) ^ 3 ∂Measure.dirac (0 : ℝ)) := by
  norm_num
