/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.Simplex.Moments

/-!
# Acceptance cases for simplex moments

Concrete moments computed by the general theorems, the source-shaped power-sum statements
derived from the general ones, the source's weighted-radius expectations through the
conditional probability measure, and the necessity of `0 ≤ L`, `0 < L`, and positive weights.
-/

open MeasureTheory Set Finset MvPolynomial
open scoped ProbabilityTheory

/-- `∫₀¹ x² dx = 1 / 3`: the second moment on the one-dimensional simplex. -/
example : (∫ x in standardSimplex (Fin 1) 1, (∑ i, (1 : ℝ) * x i) ^ 2) = 1 / 3 := by
  rw [integral_standardSimplex_linearForm_pow _ _ (by norm_num)]
  have h := two_mul_eval_hsymm_two (fun _ : Fin 1 ↦ (1 : ℝ))
  simp only [Fin.sum_univ_one, one_pow] at h
  have h1 : eval (fun _ : Fin 1 ↦ (1 : ℝ)) (hsymm (Fin 1) ℝ 2) = 1 := by linarith
  rw [h1]
  norm_num [Nat.factorial]

/-- The first coordinate on the triangle `x₀ + x₁ ≤ 1` integrates to `1 / 6`. -/
example : (∫ x in standardSimplex (Fin 2) 1, (∑ i, (![1, 0] : Fin 2 → ℝ) i * x i) ^ 1) =
    1 / 6 := by
  rw [integral_standardSimplex_linearForm_pow _ _ (by norm_num)]
  simp [Fin.sum_univ_two, Nat.factorial]

/-- The source's `integral_standardSimplex_linearForm_sq`, derived from the degree-`k` formula
and Newton's identity in degree `2`. -/
example (n : ℕ) (c : Fin n → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex (Fin n) L, (∑ i, c i * x i) ^ 2) =
      L ^ (n + 2) * ((∑ i, c i) ^ 2 + ∑ i, c i ^ 2) / (n + 2).factorial := by
  rw [integral_standardSimplex_linearForm_pow c 2 hL, ← two_mul_eval_hsymm_two,
    Fintype.card_fin]
  norm_num [Nat.factorial]
  ring

/-- The source's `integral_standardSimplex_linearForm_cube`, from Newton's identity in
degree `3`. -/
example (n : ℕ) (c : Fin n → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in standardSimplex (Fin n) L, (∑ i, c i * x i) ^ 3) =
      L ^ (n + 3) * ((∑ i, c i) ^ 3 + 3 * (∑ i, c i) * (∑ i, c i ^ 2) + 2 * ∑ i, c i ^ 3) /
        (n + 3).factorial := by
  rw [integral_standardSimplex_linearForm_pow c 3 hL, ← six_mul_eval_hsymm_three,
    Fintype.card_fin]
  norm_num [Nat.factorial]
  ring

/-- The source's `integral_weightedSimplex_radius`: the Jacobian of the weights `1, …, n` is
`1 / n!`. -/
example (n : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ u in weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W, ∑ i, u i) =
      (1 / n.factorial) * (W ^ (n + 1) * (∑ i : Fin n, 1 / ((i : ℝ) + 1)) / (n + 1).factorial) := by
  have h := integral_weightedSimplex_linearForm_pow (w := fun i : Fin n ↦ (i : ℝ) + 1)
    (fun i ↦ by positivity) 1 1 hW
  have hprod : ∏ i : Fin n, ((i : ℝ) + 1) = n.factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun k : ℕ ↦ (k : ℝ) + 1) n]
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  simp only [Pi.one_apply, one_mul, pow_one, hsymm_one, map_sum, eval_X, Fintype.card_fin,
    hprod] at h
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [h, Nat.factorial_one, Nat.factorial_succ]
  push_cast
  field_simp

/-- A mean on a weighted triangle: on `2 u₀ + 3 u₁ ≤ 6`, the form `2 u₀ + 3 u₁` has mean
`6 * 2 / 3 = 4`. -/
example : ⨍ u in weightedSimplex (![2, 3] : Fin 2 → ℝ) 6,
    ∑ i, (![2, 3] : Fin 2 → ℝ) i * u i = 4 := by
  rw [setAverage_weightedSimplex_linearForm (by intro i; fin_cases i <;> norm_num) _
    (by norm_num)]
  norm_num [Fin.sum_univ_two]

/-- The mean of `u₀ + u₁` on the triangle `u₀ + 2 u₁ ≤ 6`: `6 * (1 + 1 / 2) / 3 = 3`, both from
the weights `1, …, n` specialization and from the harmonic number. -/
example : ⨍ u in weightedSimplex (fun i : Fin 2 ↦ (i : ℝ) + 1) 6, ∑ i, u i = 3 := by
  rw [setAverage_weightedSimplex_succ_sum 2 (by norm_num)]
  norm_num [harmonic, Finset.sum_range_succ]

/-- The source's `weightedSimplexExpectation_radius` in probabilistic form: the mean of the
coordinate sum under the uniform probability measure `volume[|weightedSimplex w W]`. -/
example (n : ℕ) {W : ℝ} (hW : 0 < W) :
    (∫ u, ∑ i, u i ∂volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W]) =
      W * (harmonic n : ℝ) / (n + 1) := by
  rw [ProbabilityTheory.cond, ← setAverage_eq', setAverage_weightedSimplex_succ_sum n hW]

/-- The uniform measure on a weighted simplex with positive budget has total mass `1`. -/
example (n : ℕ) {W : ℝ} (hW : 0 < W) :
    volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W] univ = 1 :=
  haveI := isProbabilityMeasure_cond_weightedSimplex (w := fun i : Fin n ↦ (i : ℝ) + 1)
    (fun i ↦ by positivity) hW
  measure_univ

/-- The source's `weightedSimplexExpectation_radius_sq` for `n = 1`: on `[0, W]` the mean of
`u²` is `W² / 3`. -/
example {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) W, (∑ i, u i) ^ 2 = W ^ 2 / 3 := by
  rw [setAverage_weightedSimplex_succ_sum_sq 1 hW]
  norm_num
  ring

/-- The third moment for `n = 1`: on `[0, W]` the mean of `u³` is `W³ / 4`. -/
example {W : ℝ} (hW : 0 < W) :
    ⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) W, (∑ i, u i) ^ 3 = W ^ 3 / 4 := by
  rw [setAverage_weightedSimplex_succ_sum_cube 1 hW]
  norm_num
  ring

/-- The degree-`0` case of the weighted moment is the weighted volume. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → ℝ} (hw : ∀ i, 0 < w i) {W : ℝ}
    (hW : 0 ≤ W) :
    volume.real (weightedSimplex w W) =
      W ^ Fintype.card ι / ((Fintype.card ι).factorial * ∏ i, w i) := by
  have h := integral_weightedSimplex_linearForm_pow hw 0 0 hW
  simp only [pow_zero, integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
    hsymm_zero, map_one, add_zero, Nat.factorial_zero, Nat.cast_one] at h
  rw [h]
  have hn : ((Fintype.card ι).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- `0 ≤ L` is needed in `integral_standardSimplex_linearForm_pow`: for `L = -1` the simplex is
empty, while the formula for `k = 0` and no coordinates gives `1`. -/
example : (∫ x in standardSimplex (Fin 0) (-1), (∑ i, (0 : Fin 0 → ℝ) i * x i) ^ 0) ≠
    (-1 : ℝ) ^ (Fintype.card (Fin 0) + 0) *
      ((Nat.factorial 0 : ℝ) / (Fintype.card (Fin 0) + 0).factorial) *
        eval (0 : Fin 0 → ℝ) (hsymm (Fin 0) ℝ 0) := by
  rw [standardSimplex_eq_empty (by norm_num)]
  simp

/-- `0 < L` is needed in `setAverage_standardSimplex_linearForm_pow`: for `L = 0` the segment
`[0, 0]` is a null set, so the average of `1` is `0`, while the formula gives `1`. -/
example : ⨍ x in standardSimplex (Fin 1) 0, (∑ i, (1 : Fin 1 → ℝ) i * x i) ^ 0 ≠
    (0 : ℝ) ^ 0 * eval (1 : Fin 1 → ℝ) (hsymm (Fin 1) ℝ 0) /
      (Fintype.card (Fin 1) + 0).choose 0 := by
  rw [setAverage_eq, volume_real_standardSimplex _ le_rfl]
  simp

/-- Positive weights are needed in `integral_weightedSimplex_linearForm_pow`: with the single
weight `-1`, the integral of `1` is a nonnegative real volume, while the formula gives `-1`. -/
example : (∫ u in weightedSimplex (fun _ : Fin 1 ↦ (-1 : ℝ)) 1,
      (∑ i, (0 : Fin 1 → ℝ) i * u i) ^ 0) ≠
    (∏ _ : Fin 1, (-1 : ℝ))⁻¹ * ((1 : ℝ) ^ (Fintype.card (Fin 1) + 0) *
      ((Nat.factorial 0 : ℝ) / (Fintype.card (Fin 1) + 0).factorial) *
        eval (fun i ↦ (0 : Fin 1 → ℝ) i / (-1)) (hsymm (Fin 1) ℝ 0)) := by
  have h := measureReal_nonneg (μ := volume) (s := weightedSimplex (fun _ : Fin 1 ↦ (-1 : ℝ)) 1)
  simp only [pow_zero, integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]
  norm_num
  linarith
