/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.Analysis.Simplex.AffinePushforward
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# First three moments on weighted simplices

We compute moments of `R(u) = Σ_i u_i` by transporting to the ordinary simplex.  Under
`t_i = (i+1)u_i`, the normalized variable `R/W` is the harmonic linear form
`Σ_i t_i/(i+1)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace SimplexIntegration

/-- A finite linear form, written as a function for integration. -/
def simplexLinearForm {n : ℕ} (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, c i * x i

/-- The `q`-th power sum of the coefficients. -/
def coefficientPowerSum {n : ℕ} (c : Fin n → ℝ) (q : ℕ) : ℝ :=
  ∑ i, c i ^ q

private theorem prod_pow_indicator {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (∏ q, x q ^ (if q = i then 1 else 0)) = x i := by
  classical
  rw [show (fun q ↦ x q ^ (if q = i then 1 else 0)) =
      fun q ↦ if q = i then x q else 1 by
    funext q
    by_cases h : q = i <;> simp [h]]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]

private theorem integral_coordinate {n : ℕ} (i : Fin n) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex n L, x i) = L ^ (n + 1) / (n + 1).factorial := by
  let a : Fin n → ℕ := fun j ↦ if j = i then 1 else 0
  have h := integral_standardSimplex_eq n a 0 hL
  have ha : ∑ j, a j = 1 := by simp [a]
  have hp : ∏ j, (a j).factorial = 1 := by
    apply Fintype.prod_eq_one (fun j ↦ (a j).factorial)
    intro j
    by_cases hji : j = i <;> simp [a, hji]
  rw [ha, hp] at h
  calc
    (∫ x in standardSimplex n L, x i) =
        ∫ x in standardSimplex n L, simplexMonomial a 0 L x := by
      apply setIntegral_congr_fun (isClosed_standardSimplex n L).measurableSet
      intro x _
      simp only [simplexMonomial, a, pow_zero, mul_one, prod_pow_indicator]
    _ = L ^ (n + 1) / (n + 1).factorial := by
      simpa [div_eq_mul_inv] using h

private theorem integral_coordinate_mul {n : ℕ} (i j : Fin n) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex n L, x i * x j) =
      L ^ (n + 2) * (if i = j then 2 else 1) / (n + 2).factorial := by
  let a : Fin n → ℕ := fun q ↦ (if q = i then 1 else 0) + (if q = j then 1 else 0)
  have h := integral_standardSimplex_eq n a 0 hL
  have ha : ∑ q, a q = 2 := by simp [a, Finset.sum_add_distrib]
  by_cases hij : i = j
  · subst j
    have hp : ∏ q, (a q).factorial = 2 := by
      rw [Fintype.prod_eq_single i]
      · simp [a]
      · intro q hqi
        norm_num [a, hqi]
    rw [ha, hp] at h
    calc
      (∫ x in standardSimplex n L, x i * x i) =
          ∫ x in standardSimplex n L, simplexMonomial a 0 L x := by
        apply setIntegral_congr_fun (isClosed_standardSimplex n L).measurableSet
        intro x _
        simp only [simplexMonomial, a, pow_zero, mul_one, pow_add,
          Finset.prod_mul_distrib, prod_pow_indicator]
      _ = L ^ (n + 2) * (if i = i then 2 else 1) / (n + 2).factorial := by
        simpa [div_eq_mul_inv, mul_assoc] using h
  · have hp : ∏ q, (a q).factorial = 1 := by
      apply Fintype.prod_eq_one (fun q ↦ (a q).factorial)
      intro q
      by_cases hqi : q = i <;> by_cases hqj : q = j <;>
        simp [a, hqi, hqj, hij, Ne.symm hij] at *
    rw [ha, hp] at h
    calc
      (∫ x in standardSimplex n L, x i * x j) =
          ∫ x in standardSimplex n L, simplexMonomial a 0 L x := by
        apply setIntegral_congr_fun (isClosed_standardSimplex n L).measurableSet
        intro x _
        simp only [simplexMonomial, a, pow_zero, mul_one, pow_add,
          Finset.prod_mul_distrib, prod_pow_indicator]
      _ = L ^ (n + 2) * (if i = j then 2 else 1) / (n + 2).factorial := by
        simpa [hij, div_eq_mul_inv, mul_assoc] using h

private theorem integral_coordinate_mul_mul {n : ℕ} (i j k : Fin n)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex n L, x i * x j * x k) =
      L ^ (n + 3) * (1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
        (if j = k then 1 else 0) + (if i = j ∧ j = k then 2 else 0)) /
          (n + 3).factorial := by
  let a : Fin n → ℕ := fun q ↦
    (if q = i then 1 else 0) + (if q = j then 1 else 0) + (if q = k then 1 else 0)
  have h := integral_standardSimplex_eq n a 0 hL
  have ha : ∑ q, a q = 3 := by simp [a, Finset.sum_add_distrib]
  have hprod : ∏ q, (a q).factorial =
      1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
        (if j = k then 1 else 0) + (if i = j ∧ j = k then 2 else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        rw [Fintype.prod_eq_single i]
        · norm_num [a]
        · intro q hqi
          norm_num [a, hqi]
      · have hp : ∏ q, (a q).factorial = 2 := by
          rw [Fintype.prod_eq_single i]
          · norm_num [a, hik]
          · intro q hqi
            by_cases hqk : q = k
            · subst q
              norm_num [a, hik, Ne.symm hik]
            · norm_num [a, hqi, hqk]
        rw [hp]
        simp [hik]
    · by_cases hik : i = k
      · subst k
        have hp : ∏ q, (a q).factorial = 2 := by
          rw [Fintype.prod_eq_single i]
          · norm_num [a, hij, Ne.symm hij]
          · intro q hqi
            by_cases hqj : q = j
            · subst q
              norm_num [a, hij, Ne.symm hij]
            · norm_num [a, hqi, hqj]
        rw [hp]
        simp [hij, Ne.symm hij]
      · by_cases hjk : j = k
        · subst k
          have hp : ∏ q, (a q).factorial = 2 := by
            rw [Fintype.prod_eq_single j]
            · norm_num [a, hij, Ne.symm hij]
            · intro q hqj
              by_cases hqi : q = i
              · subst q
                norm_num [a, hij, Ne.symm hij]
              · norm_num [a, hqj, hqi]
          rw [hp]
          simp [hij]
        · have hp : ∏ q, (a q).factorial = 1 := by
            apply Fintype.prod_eq_one (fun q ↦ (a q).factorial)
            intro q
            by_cases hqi : q = i <;> by_cases hqj : q = j <;>
              by_cases hqk : q = k <;>
                simp [a, hqi, hqj, hqk, hij, hik, hjk, Ne.symm hij, Ne.symm hik,
                  Ne.symm hjk] at *
          rw [hp]
          simp [hij, hik, hjk]
  rw [ha, hprod] at h
  calc
    (∫ x in standardSimplex n L, x i * x j * x k) =
        ∫ x in standardSimplex n L, simplexMonomial a 0 L x := by
      apply setIntegral_congr_fun (isClosed_standardSimplex n L).measurableSet
      intro x _
      simp only [simplexMonomial, a, pow_zero, mul_one, pow_add,
        Finset.prod_mul_distrib, prod_pow_indicator]
    _ = _ := by simpa [div_eq_mul_inv, mul_assoc] using h

/-- The first raw moment of a linear form on the standard simplex. -/
theorem integral_standardSimplex_linearForm (n : ℕ) (c : Fin n → ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex n L, simplexLinearForm c x) =
      L ^ (n + 1) * coefficientPowerSum c 1 / (n + 1).factorial := by
  unfold simplexLinearForm
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul, integral_coordinate _ hL]
    simp only [coefficientPowerSum, pow_one]
    rw [← Finset.sum_mul]
    ring
  · intro i _
    exact (continuous_const.mul (continuous_apply i)).continuousOn.integrableOn_compact
      (isCompact_standardSimplex n hL)

private theorem sum_pair_multiplicity {n : ℕ} (c : Fin n → ℝ) :
    (∑ i, ∑ j, c i * c j * (if i = j then 2 else 1)) =
      (∑ i, c i) ^ 2 + ∑ i, c i ^ 2 := by
  classical
  calc
    (∑ i, ∑ j, c i * c j * (if i = j then 2 else 1)) =
        ∑ i, ∑ j, (c i * c j + if i = j then c i * c j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simp [hij]
        ring
      · simp [hij]
    _ = (∑ i, c i) ^ 2 + ∑ i, c i ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      have hdiag : (∑ i, ∑ j, if i = j then c i * c j else 0) = ∑ i, c i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · simp [pow_two]
        · intro j _ hji
          simp [Ne.symm hji]
        · simp
      rw [hdiag]
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

/-- The second raw moment of a linear form on the standard simplex. -/
theorem integral_standardSimplex_linearForm_sq (n : ℕ) (c : Fin n → ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex n L, simplexLinearForm c x ^ 2) =
      L ^ (n + 2) *
        (coefficientPowerSum c 1 ^ 2 + coefficientPowerSum c 2) /
          (n + 2).factorial := by
  have hexpand : ∀ x : Fin n → ℝ,
      simplexLinearForm c x ^ 2 =
        ∑ i, ∑ j, (c i * c j) * (x i * x j) := by
    intro x
    unfold simplexLinearForm
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand]
  rw [MeasureTheory.integral_finsetSum]
  · have hinter :
        (∑ i, ∫ x in standardSimplex n L, ∑ j, (c i * c j) * (x i * x j)) =
          ∑ i, ∑ j, ∫ x in standardSimplex n L, (c i * c j) * (x i * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.integral_finsetSum]
      intro j _
      exact (continuous_const.mul ((continuous_apply i).mul (continuous_apply j))).continuousOn
        |>.integrableOn_compact (isCompact_standardSimplex n hL)
    rw [hinter]
    simp_rw [MeasureTheory.integral_const_mul, integral_coordinate_mul _ _ hL]
    simp only [coefficientPowerSum, pow_one]
    rw [← sum_pair_multiplicity]
    calc
      (∑ i, ∑ j, c i * c j *
          ((L ^ (n + 2) * (if i = j then 2 else 1)) / (n + 2).factorial)) =
          ∑ i, ∑ j, (c i * c j * (if i = j then 2 else 1)) *
            (L ^ (n + 2) / (n + 2).factorial) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ i, ∑ j, c i * c j * (if i = j then 2 else 1)) *
          (L ^ (n + 2) / (n + 2).factorial) := by
        simp_rw [← Finset.sum_mul]
      _ = _ := by ring
  · intro i _
    exact MeasureTheory.integrable_finsetSum _ fun j _ ↦
      (continuous_const.mul ((continuous_apply i).mul (continuous_apply j))).continuousOn
        |>.integrableOn_compact (isCompact_standardSimplex n hL)

private theorem sum_triple_multiplicity {n : ℕ} (c : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, c i * c j * c k *
      (1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
        (if j = k then 1 else 0) + (if i = j ∧ j = k then 2 else 0))) =
      (∑ i, c i) ^ 3 + 3 * (∑ i, c i) * (∑ i, c i ^ 2) +
        2 * ∑ i, c i ^ 3 := by
  classical
  calc
    _ = ∑ i, ∑ j, ∑ k,
        (c i * c j * c k +
          (if i = j then c i * c j * c k else 0) +
          (if i = k then c i * c j * c k else 0) +
          (if j = k then c i * c j * c k else 0) +
          (if i = j ∧ j = k then 2 * (c i * c j * c k) else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hjk : j = k <;>
        simp_all <;> ring
    _ = (∑ i, c i) ^ 3 + 3 * (∑ i, c i) * (∑ i, c i ^ 2) +
        2 * ∑ i, c i ^ 3 := by
      have hbase : (∑ i, ∑ j, ∑ k, c i * c j * c k) = (∑ i, c i) ^ 3 := by
        rw [pow_three]
        symm
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      have hij_sum :
          (∑ i, ∑ j, ∑ k, if i = j then c i * c j * c k else 0) =
            (∑ i, c i) * (∑ i, c i ^ 2) := by
        simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        rw [Finset.mul_sum]
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hik_sum :
          (∑ i, ∑ j, ∑ k, if i = k then c i * c j * c k else 0) =
            (∑ i, c i) * (∑ i, c i ^ 2) := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.mul_sum]
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hjk_sum :
          (∑ i, ∑ j, ∑ k, if j = k then c i * c j * c k else 0) =
            (∑ i, c i) * (∑ i, c i ^ 2) := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.mul_sum]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hall :
          (∑ i, ∑ j, ∑ k,
            if i = j ∧ j = k then 2 * (c i * c j * c k) else 0) =
              2 * ∑ i, c i ^ 3 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single i]
          · simp
            ring
          · intro k _ hki
            simp [Ne.symm hki]
          · simp
        · intro j _ hji
          simp [Ne.symm hji]
        · simp
      simp_rw [Finset.sum_add_distrib]
      rw [hbase, hij_sum, hik_sum, hjk_sum, hall]
      ring

/-- The third raw moment of a linear form on the standard simplex. -/
theorem integral_standardSimplex_linearForm_cube (n : ℕ) (c : Fin n → ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex n L, simplexLinearForm c x ^ 3) =
      L ^ (n + 3) *
        (coefficientPowerSum c 1 ^ 3 +
          3 * coefficientPowerSum c 1 * coefficientPowerSum c 2 +
          2 * coefficientPowerSum c 3) /
            (n + 3).factorial := by
  have hexpand : ∀ x : Fin n → ℝ,
      simplexLinearForm c x ^ 3 =
        ∑ i, ∑ j, ∑ k, (c i * c j * c k) * (x i * x j * x k) := by
    intro x
    unfold simplexLinearForm
    calc
      (∑ i, c i * x i) ^ 3 =
          (∑ i, c i * x i) * (∑ j, c j * x j) * (∑ k, c k * x k) := by ring
      _ = _ := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  simp_rw [hexpand]
  rw [MeasureTheory.integral_finsetSum]
  · have hmiddle :
        (∑ i, ∫ x in standardSimplex n L,
          ∑ j, ∑ k, (c i * c j * c k) * (x i * x j * x k)) =
          ∑ i, ∑ j, ∫ x in standardSimplex n L,
            ∑ k, (c i * c j * c k) * (x i * x j * x k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.integral_finsetSum]
      intro j _
      exact MeasureTheory.integrable_finsetSum _ fun k _ ↦
        (continuous_const.mul
          (((continuous_apply i).mul (continuous_apply j)).mul (continuous_apply k))).continuousOn
            |>.integrableOn_compact (isCompact_standardSimplex n hL)
    rw [hmiddle]
    have hinner :
        (∑ i, ∑ j, ∫ x in standardSimplex n L,
          ∑ k, (c i * c j * c k) * (x i * x j * x k)) =
          ∑ i, ∑ j, ∑ k, ∫ x in standardSimplex n L,
            (c i * c j * c k) * (x i * x j * x k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [MeasureTheory.integral_finsetSum]
      intro k _
      exact (continuous_const.mul
        (((continuous_apply i).mul (continuous_apply j)).mul (continuous_apply k))).continuousOn
          |>.integrableOn_compact (isCompact_standardSimplex n hL)
    rw [hinner]
    simp_rw [MeasureTheory.integral_const_mul, integral_coordinate_mul_mul _ _ _ hL]
    simp only [coefficientPowerSum, pow_one]
    rw [← sum_triple_multiplicity]
    calc
      (∑ i, ∑ j, ∑ k, c i * c j * c k *
          ((L ^ (n + 3) *
            (1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
              (if j = k then 1 else 0) + (if i = j ∧ j = k then 2 else 0))) /
                (n + 3).factorial)) =
          ∑ i, ∑ j, ∑ k,
            (c i * c j * c k *
              (1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
                (if j = k then 1 else 0) + (if i = j ∧ j = k then 2 else 0))) *
                  (L ^ (n + 3) / (n + 3).factorial) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (∑ i, ∑ j, ∑ k, c i * c j * c k *
          (1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) +
            (if j = k then 1 else 0) + (if i = j ∧ j = k then 2 else 0))) *
              (L ^ (n + 3) / (n + 3).factorial) := by
        simp_rw [← Finset.sum_mul]
      _ = _ := by ring
  · intro i _
    exact MeasureTheory.integrable_finsetSum _ fun j _ ↦
      MeasureTheory.integrable_finsetSum _ fun k _ ↦
        (continuous_const.mul
          (((continuous_apply i).mul (continuous_apply j)).mul (continuous_apply k))).continuousOn
            |>.integrableOn_compact (isCompact_standardSimplex n hL)

/-- The reciprocal coordinate weights `1, 1/2, ..., 1/n`. -/
noncomputable def harmonicCoefficient {n : ℕ} (i : Fin n) : ℝ :=
  1 / coordinateWeight i

/-- The `q`-th harmonic power sum on the first `n` positive integers. -/
noncomputable def harmonicPowerSum (n q : ℕ) : ℝ :=
  coefficientPowerSum (n := n) harmonicCoefficient q

/-- The unweighted radius `R(u) = Σ_i u_i` on a weighted simplex. -/
def weightedRadius {n : ℕ} (u : Fin n → ℝ) : ℝ :=
  ∑ i, u i

theorem weightedRadius_standardToWeighted {n : ℕ} (t : Fin n → ℝ) :
    weightedRadius (standardToWeighted t) = simplexLinearForm harmonicCoefficient t := by
  unfold weightedRadius simplexLinearForm standardToWeighted harmonicCoefficient
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem continuous_weightedRadius {n : ℕ} :
    Continuous (weightedRadius : (Fin n → ℝ) → ℝ) := by
  unfold weightedRadius
  fun_prop

/-- Every positive part of a continuous residual is integrable on a weighted simplex. -/
theorem Continuous.integrableOn_weightedSimplex_posPart {n : ℕ} {W : ℝ}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (hW : 0 ≤ W) :
    IntegrableOn (fun u ↦ max (f u) 0) (weightedSimplex n W) :=
  SimplexIntegration.Continuous.integrableOn_weightedSimplex
    (hf.max continuous_const) hW

theorem integrableOn_weightedRadius (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    IntegrableOn (weightedRadius : (Fin n → ℝ) → ℝ) (weightedSimplex n W) :=
  SimplexIntegration.Continuous.integrableOn_weightedSimplex continuous_weightedRadius hW

theorem integrableOn_weightedRadius_sq (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    IntegrableOn (fun u : Fin n → ℝ ↦ weightedRadius u ^ 2) (weightedSimplex n W) :=
  SimplexIntegration.Continuous.integrableOn_weightedSimplex
    (continuous_weightedRadius.pow 2) hW

theorem integrableOn_weightedRadius_cube (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    IntegrableOn (fun u : Fin n → ℝ ↦ weightedRadius u ^ 3) (weightedSimplex n W) :=
  SimplexIntegration.Continuous.integrableOn_weightedSimplex
    (continuous_weightedRadius.pow 3) hW

/-- The unnormalized first radius moment on a weighted simplex. -/
theorem integral_weightedSimplex_radius (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ u in weightedSimplex n W, weightedRadius u) =
      (1 / n.factorial) *
        (W ^ (n + 1) * harmonicPowerSum n 1 / (n + 1).factorial) := by
  rw [integral_weightedSimplex_eq_standardSimplex]
  simp_rw [weightedRadius_standardToWeighted]
  simpa [harmonicPowerSum] using congrArg (fun x : ℝ ↦ (1 / n.factorial) * x)
    (integral_standardSimplex_linearForm n harmonicCoefficient hW)

/-- The unnormalized second radius moment on a weighted simplex. -/
theorem integral_weightedSimplex_radius_sq (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ u in weightedSimplex n W, weightedRadius u ^ 2) =
      (1 / n.factorial) *
        (W ^ (n + 2) *
          (harmonicPowerSum n 1 ^ 2 + harmonicPowerSum n 2) /
            (n + 2).factorial) := by
  rw [integral_weightedSimplex_eq_standardSimplex]
  simp_rw [weightedRadius_standardToWeighted]
  simpa [harmonicPowerSum] using congrArg (fun x : ℝ ↦ (1 / n.factorial) * x)
    (integral_standardSimplex_linearForm_sq n harmonicCoefficient hW)

/-- The unnormalized third radius moment on a weighted simplex. -/
theorem integral_weightedSimplex_radius_cube (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ u in weightedSimplex n W, weightedRadius u ^ 3) =
      (1 / n.factorial) *
        (W ^ (n + 3) *
          (harmonicPowerSum n 1 ^ 3 +
            3 * harmonicPowerSum n 1 * harmonicPowerSum n 2 +
            2 * harmonicPowerSum n 3) /
              (n + 3).factorial) := by
  rw [integral_weightedSimplex_eq_standardSimplex]
  simp_rw [weightedRadius_standardToWeighted]
  simpa [harmonicPowerSum] using congrArg (fun x : ℝ ↦ (1 / n.factorial) * x)
    (integral_standardSimplex_linearForm_cube n harmonicCoefficient hW)

/-- Normalized expectation over a weighted simplex. -/
noncomputable def weightedSimplexExpectation (n : ℕ) (W : ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ⨍ u in weightedSimplex n W, f u

/-- Lebesgue measure restricted to a weighted simplex, packaged as a finite measure. -/
noncomputable def weightedSimplexFiniteMeasure (n : ℕ) (W : ℝ) :
    MeasureTheory.FiniteMeasure (Fin n → ℝ) :=
  ⟨volume.restrict (weightedSimplex n W),
    ⟨by
      rw [Measure.restrict_apply_univ]
      by_cases hW : 0 ≤ W
      · exact (isCompact_weightedSimplex n hW).measure_lt_top
      · have hempty : weightedSimplex n W = ∅ := by
          ext u
          simp only [weightedSimplex, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hu, hle⟩
          have hsum : 0 ≤ ∑ i, coordinateWeight i * u i :=
            Finset.sum_nonneg fun i _ ↦ mul_nonneg (by unfold coordinateWeight; positivity) (hu i)
          exact hW (hsum.trans hle)
        rw [hempty, measure_empty]
        exact ENNReal.zero_lt_top⟩⟩

/-- The uniform probability measure on a positive-radius weighted simplex.  The definition uses
finite-measure normalization; positivity ensures this is the intended normalized restriction. -/
noncomputable def weightedSimplexProbabilityMeasure (n : ℕ) (W : ℝ) :
    MeasureTheory.ProbabilityMeasure (Fin n → ℝ) :=
  (weightedSimplexFiniteMeasure n W).normalize

theorem weightedSimplexFiniteMeasure_ne_zero (n : ℕ) {W : ℝ} (hW : 0 < W) :
    weightedSimplexFiniteMeasure n W ≠ 0 := by
  intro hzero
  have hz : volume.real (weightedSimplex n W) = 0 := by
    rw [← MeasureTheory.measureReal_restrict_apply_univ]
    change (weightedSimplexFiniteMeasure n W : Measure (Fin n → ℝ)).real Set.univ = 0
    rw [hzero]
    simp
  rw [volume_weightedSimplex n hW.le] at hz
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hpow : 0 < W ^ n := by positivity
  exact (div_pos hpow (sq_pos_of_pos (by positivity))).ne' hz

/-- The set-average API agrees with integration against the uniform probability measure. -/
theorem weightedSimplexExpectation_eq_integral_probability (n : ℕ) {W : ℝ}
    (hW : 0 < W) (f : (Fin n → ℝ) → ℝ) :
    weightedSimplexExpectation n W f =
      ∫ u, f u ∂(weightedSimplexProbabilityMeasure n W : Measure (Fin n → ℝ)) := by
  simpa [weightedSimplexExpectation, weightedSimplexFiniteMeasure,
    weightedSimplexProbabilityMeasure] using
      (MeasureTheory.FiniteMeasure.average_eq_integral_normalize
        (weightedSimplexFiniteMeasure n W) (weightedSimplexFiniteMeasure_ne_zero n hW) f)

/-- The normalized mean of the weighted-simplex radius. -/
theorem weightedSimplexExpectation_radius (n : ℕ) {W : ℝ} (hW : 0 < W) :
    weightedSimplexExpectation n W weightedRadius =
      W * harmonicPowerSum n 1 / (n + 1) := by
  rw [weightedSimplexExpectation, MeasureTheory.setAverage_eq,
    volume_weightedSimplex n hW.le, integral_weightedSimplex_radius n hW.le]
  simp only [smul_eq_mul]
  have hnfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hsucc : (((n + 1).factorial : ℕ) : ℝ) = (n + 1) * n.factorial := by
    norm_num [Nat.factorial_succ]
  rw [hsucc]
  field_simp
  ring

/-- The normalized second radius moment. -/
theorem weightedSimplexExpectation_radius_sq (n : ℕ) {W : ℝ} (hW : 0 < W) :
    weightedSimplexExpectation n W (fun u ↦ weightedRadius u ^ 2) =
      W ^ 2 * (harmonicPowerSum n 1 ^ 2 + harmonicPowerSum n 2) /
        ((n + 1) * (n + 2)) := by
  rw [weightedSimplexExpectation, MeasureTheory.setAverage_eq,
    volume_weightedSimplex n hW.le, integral_weightedSimplex_radius_sq n hW.le]
  simp only [smul_eq_mul]
  have hfac1 : (((n + 1).factorial : ℕ) : ℝ) = (n + 1) * n.factorial := by
    norm_num [Nat.factorial_succ]
  have hfac2 : (((n + 2).factorial : ℕ) : ℝ) =
      (n + 2) * (n + 1) * n.factorial := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
    norm_num [Nat.cast_mul, hfac1]
    ring
  rw [hfac2]
  field_simp
  ring

/-- The normalized third radius moment. -/
theorem weightedSimplexExpectation_radius_cube (n : ℕ) {W : ℝ} (hW : 0 < W) :
    weightedSimplexExpectation n W (fun u ↦ weightedRadius u ^ 3) =
      W ^ 3 *
        (harmonicPowerSum n 1 ^ 3 +
          3 * harmonicPowerSum n 1 * harmonicPowerSum n 2 +
          2 * harmonicPowerSum n 3) /
            ((n + 1) * (n + 2) * (n + 3)) := by
  rw [weightedSimplexExpectation, MeasureTheory.setAverage_eq,
    volume_weightedSimplex n hW.le, integral_weightedSimplex_radius_cube n hW.le]
  simp only [smul_eq_mul]
  have hfac3 : (((n + 3).factorial : ℕ) : ℝ) =
      (n + 3) * (n + 2) * (n + 1) * n.factorial := by
    rw [show n + 3 = (n + 2) + 1 by omega, Nat.factorial_succ,
      show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    norm_num [Nat.cast_mul]
    ring
  rw [hfac3]
  field_simp
  ring

/-- The weighted-simplex harmonic coefficient sum agrees with its range-sum form. -/
theorem harmonicPowerSum_eq_range (n q : ℕ) :
    harmonicPowerSum n q = ∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ q := by
  unfold harmonicPowerSum coefficientPowerSum harmonicCoefficient coordinateWeight
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (1 / (i + 1 : ℝ)) ^ q) n

/-- The first coefficient power sum is the usual harmonic number. -/
theorem harmonicPowerSum_one (n : ℕ) : harmonicPowerSum n 1 = (harmonic n : ℝ) := by
  rw [harmonicPowerSum_eq_range]
  simp [harmonic]

end SimplexIntegration
