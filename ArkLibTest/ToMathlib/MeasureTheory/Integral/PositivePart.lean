/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MeasureTheory.Integral.PositivePart
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Acceptance cases for the positive-part bound by mean and variance

These cases evaluate the finite-average bound on a two-point sample, check that the pointwise bound
is attained at `y = μ` and `y = 2 * c - μ`, show that `μ < c` is needed, check the empty average,
and apply the probability-measure bound to a Dirac measure. The set-integral form is evaluated on a
measure of total mass `2` and on a set of infinite measure. For the cube of the positive part they
show the bound is attained by a symmetric two-point variable and that the mean-zero hypothesis is
needed. For the Jensen bound they derive the source's `positive_cube_jensen` and
`positive_cube_convex`, evaluate the bound on a two-point variable and at a negative threshold, and
show that `0 ≤ b` is needed in the pointwise tangent bound and the mean-zero hypothesis in the
integral bound.
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

/-- The set-integral form scales by the measure of the set. For `μ = δ₀ + δ₂` (total mass `2`)
and `Y = id`, the average of `Y` is `1` and the average of `(Y - 1) ^ 2` is `1`, so with threshold
`2` the bound is `2 * (1 + 1 / 4) = 5 / 2`; the actual integral of `max (2 - Y) 0` is `2`. -/
example : ∫ x in Set.univ, max (2 - x) 0 ∂(Measure.dirac (0 : ℝ) + Measure.dirac 2) ≤ 5 / 2 := by
  set μ : Measure ℝ := Measure.dirac (0 : ℝ) + Measure.dirac 2
  have hdirac : ∀ (a : ℝ) (f : ℝ → ℝ), Integrable f (Measure.dirac a) :=
    fun a f ↦ integrable_dirac (by simp)
  have hint : ∀ f : ℝ → ℝ, IntegrableOn f Set.univ μ := fun f ↦ by
    rw [IntegrableOn, Measure.restrict_univ]
    exact (hdirac 0 f).add_measure (hdirac 2 f)
  have hμ : ∀ f : ℝ → ℝ, ∫ x in Set.univ, f x ∂μ = f 0 + f 2 := fun f ↦ by
    rw [Measure.restrict_univ, integral_add_measure (hdirac 0 f) (hdirac 2 f), integral_dirac,
      integral_dirac]
  have hreal : μ.real Set.univ = 2 := by
    simp only [μ, measureReal_def, Measure.add_apply, measure_univ]
    norm_num
  have havg : ∀ f : ℝ → ℝ, ⨍ x in Set.univ, f x ∂μ = (f 0 + f 2) / 2 := fun f ↦ by
    rw [setAverage_eq, hreal, hμ, smul_eq_mul]
    ring
  have h := setIntegral_max_sub_zero_le id (hint _) (by rw [havg]; norm_num : _ = (1 : ℝ))
    (hint _) one_lt_two
  rw [havg, hreal] at h
  norm_num at h ⊢
  exact h

/-- A set of infinite measure is allowed. For Lebesgue measure on `ℝ`, `Y = 0` and threshold `1`
the right side is `0`, since `volume.real univ = 0`; the left side is the Bochner integral of the
constant `1` over `ℝ`, which is `0` because the constant is not integrable. -/
example : ∫ x : ℝ in Set.univ, max (1 - (0 : ℝ → ℝ) x) 0 ≤ 0 := by
  have hreal : volume.real (Set.univ : Set ℝ) = 0 := by
    simp [measureReal_def]
  have hmean : ⨍ x : ℝ in Set.univ, (0 : ℝ → ℝ) x = 0 := by simp
  have h := setIntegral_max_sub_zero_le (μ := volume) (s := (Set.univ : Set ℝ)) (0 : ℝ → ℝ)
    integrableOn_zero hmean (by simp) one_pos
  rwa [hreal, zero_mul] at h

/-! ### The Jensen bound for the cube of the positive part -/

/-- The source's `positive_cube_convex`. -/
example (b : ℝ) : ConvexOn ℝ Set.univ (fun z : ℝ ↦ (max (b - z) 0) ^ 3) :=
  convexOn_max_sub_zero_pow b 3

/-- The source's `positive_cube_jensen`, with its unused hypothesis `0 ≤ b`. -/
example {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] (z : X → ℝ)
    (b : ℝ) (_hb : 0 ≤ b) (hz : Integrable z P) (hm : ∫ x, z x ∂P = 0)
    (hf : Integrable (fun x ↦ (max (b - z x) 0) ^ 3) P) :
    b ^ 3 ≤ ∫ x, (max (b - z x) 0) ^ 3 ∂P :=
  pow_three_le_integral_max_sub_zero_pow_three P z b hz hm hf

/-- For `z = ±1` with probability `1 / 2` each and `b = 1`, the Jensen bound gives `1 ≤ 4`; the
moment bound `le_integral_max_sub_zero_pow_three` is attained there. -/
example : ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ ∫ x, (max (1 - x) 0) ^ 3 ∂P = 4 ∧
    (1 : ℝ) ^ 3 ≤ ∫ x, (max (1 - x) 0) ^ 3 ∂P := by
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
  refine ⟨P, this, by rw [hP]; norm_num, ?_⟩
  exact pow_three_le_integral_max_sub_zero_pow_three P id 1 (hint _) (by rw [hP]; norm_num)
    (hint _)

/-- The integral bound needs no sign condition on `b`: at `b = -2` it reads `-8 ≤ ∫ …`. -/
example {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] (z : X → ℝ)
    (hz : Integrable z P) (hm : ∫ x, z x ∂P = 0)
    (hf : Integrable (fun x ↦ (max (-2 - z x) 0) ^ 3) P) :
    (-8 : ℝ) ≤ ∫ x, (max (-2 - z x) 0) ^ 3 ∂P := by
  have h := pow_three_le_integral_max_sub_zero_pow_three P z (-2) hz hm hf
  norm_num at h
  exact h

/-- The hypothesis `0 ≤ b` of the pointwise tangent bound is needed: at `b = -1` and
`z = -3 / 2` the tangent is `7 / 2` and the positive-part cube is `1 / 8`. -/
example : ¬ ((-1 : ℝ) ^ 3 - 3 * (-1) ^ 2 * (-3 / 2) ≤ (max (-1 - (-3 / 2)) 0) ^ 3) := by
  norm_num

/-- The mean-zero hypothesis of the Jensen bound is needed: for `z = 1` under a Dirac measure and
`b = 1` the right side is `0`. -/
example : ¬ ((1 : ℝ) ^ 3 ≤ ∫ _x, (max ((1 : ℝ) - 1) 0) ^ 3 ∂Measure.dirac (0 : ℝ)) := by
  norm_num
