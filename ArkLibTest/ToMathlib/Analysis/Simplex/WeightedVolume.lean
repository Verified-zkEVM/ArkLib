/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.Simplex.WeightedVolume

/-!
# Acceptance cases for weighted simplices

Concrete weighted volumes and a weighted Dirichlet integral, the consecutive-weight
specialization cross-checked against the general formula, and the necessity of positive weights
and a nonnegative budget.
-/

open MeasureTheory Set

/-- The triangle `2 u₀ + 3 u₁ ≤ 6` with vertices `(3, 0)` and `(0, 2)` has area `3`. -/
example : volume.real (weightedSimplex (![2, 3] : Fin 2 → ℝ) 6) = 3 := by
  rw [volume_real_weightedSimplex (by intro i; fin_cases i <;> norm_num) (by norm_num)]
  simp [Fin.prod_univ_two]
  norm_num

/-- Weights `1, 2` and budget `4`: the triangle with vertices `(4, 0)` and `(0, 2)` has area
`4 = 4² / (2!)²`, from both the specialization and the general formula. -/
example : volume.real (weightedSimplex (fun i : Fin 2 ↦ (i : ℝ) + 1) 4) = 4 := by
  rw [volume_real_weightedSimplex_succ 2 (by norm_num)]
  norm_num [Nat.factorial]

example : volume.real (weightedSimplex (fun i : Fin 2 ↦ (i : ℝ) + 1) 4) = 4 := by
  rw [volume_real_weightedSimplex (fun i ↦ by positivity) (by norm_num)]
  simp [Fin.prod_univ_two]
  norm_num

/-- The weighted Dirichlet integral `∫₀¹ u du = 1 / 2` on `2 u ≤ 2`. -/
example : (∫ u in weightedSimplex (fun _ : Fin 1 ↦ (2 : ℝ)) 2,
    (∏ i, u i ^ (fun _ : Fin 1 ↦ 1) i) * (2 - ∑ i, (2 : ℝ) * u i) ^ 0) = 1 / 2 := by
  rw [integral_weightedSimplex_prod_pow_mul_pow (fun _ ↦ by norm_num) _ _ (by norm_num)]
  norm_num [Nat.factorial]

/-- The change of variables with a non-polynomial integrand keeps the Jacobian `(2 · 3)⁻¹`. -/
example (f : (Fin 2 → ℝ) → ℝ) :
    (∫ u in weightedSimplex (![2, 3] : Fin 2 → ℝ) 1, f u) =
      6⁻¹ * ∫ t in standardSimplex (Fin 2) 1, f (fun i ↦ t i / (![2, 3] : Fin 2 → ℝ) i) := by
  rw [setIntegral_weightedSimplex (by intro i; fin_cases i <;> norm_num)]
  norm_num [Fin.prod_univ_two]

/-- Positive weights are needed: with the single weight `-1` the set `{u | 0 ≤ u 0}` has
nonnegative real volume, while the formula `1 ^ 1 / (1! * (-1))` is `-1`. -/
example : volume.real (weightedSimplex (fun _ : Fin 1 ↦ (-1 : ℝ)) 1) ≠
    1 ^ Fintype.card (Fin 1) /
      ((Fintype.card (Fin 1)).factorial * ∏ _ : Fin 1, (-1 : ℝ)) := by
  have h := measureReal_nonneg (μ := volume) (s := weightedSimplex (fun _ : Fin 1 ↦ (-1 : ℝ)) 1)
  norm_num
  linarith

/-- A nonnegative budget is needed: unit weights at `W = -1` give the empty simplex, of volume
`0`, while `W ^ 0 / (0! * 1) = 1`. -/
example : volume.real (weightedSimplex (1 : Fin 0 → ℝ) (-1)) = 0 := by
  rw [weightedSimplex_one, standardSimplex_eq_empty (by norm_num)]
  simp
