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
and a nonnegative budget. The exponential bound for an enlarged budget is evaluated on a segment,
and its hypothesis `0 < W` is shown to be needed.
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

/-- Enlarging the segment `[0, 1]` to `[0, 2]` doubles its length, and the exponential bound gives
`2 ≤ exp 1`. -/
example : (2 : ℝ) ≤ Real.exp 1 := by
  have h := volume_real_weightedSimplex_add_le_mul_exp (w := fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ ↦ one_pos) one_pos 1
  rw [volume_real_weightedSimplex (fun _ ↦ one_pos) (by norm_num),
    volume_real_weightedSimplex (fun _ ↦ one_pos) (by norm_num)] at h
  norm_num at h
  exact h

/-- `0 < W` is needed in `volume_real_weightedSimplex_add_le_mul_exp`: at `W = 0`, `r = 1` with one
unit weight the left side is `1`, while the right side is `0 * exp (1 * 1 / 0) = 0`. -/
example : ¬ (volume.real (weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) (0 + 1)) ≤
    volume.real (weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) 0) *
      Real.exp (Fintype.card (Fin 1) * 1 / 0)) := by
  rw [volume_real_weightedSimplex (fun _ ↦ one_pos) (by norm_num),
    volume_real_weightedSimplex (fun _ ↦ one_pos) le_rfl]
  norm_num

/-- Dilating by `2` doubles both sides of the triangle with weights `1, 2` and budget `2`, of area
`1`, so the triangle of budget `4` has area `2 ^ 2 * 1 = 4`, as computed above. -/
example : volume.real (weightedSimplex (fun i : Fin 2 ↦ (i : ℝ) + 1) (2 * 2)) = 4 := by
  rw [volume_real_weightedSimplex_mul _ (by norm_num : (0 : ℝ) < 2),
    volume_real_weightedSimplex_succ 2 (by norm_num)]
  norm_num [Nat.factorial]

/-- For every `f`, the integral of `f` over the segment `[0, 2]` is twice the integral of
`f (2 • u)` over `[0, 1]`. -/
example (f : (Fin 1 → ℝ) → ℝ) :
    (∫ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) (2 * 1), f u) =
      2 * ∫ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) 1, f ((2 : ℝ) • u) := by
  rw [setIntegral_weightedSimplex_mul _ (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- `0 < c` is needed in `setAverage_weightedSimplex_mul`: at `c = 0` the constant `1` has
average `0` over the null set `weightedSimplex w 0 = {0}`, and average `1` over
`weightedSimplex w 1`. -/
example : (⨍ _u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) (0 * 1), (1 : ℝ)) ≠
    ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) 1, (fun _ ↦ (1 : ℝ)) ((0 : ℝ) • u) := by
  rw [zero_mul, setAverage_eq, setAverage_eq,
    volume_real_weightedSimplex (fun _ ↦ one_pos) le_rfl,
    volume_real_weightedSimplex (fun _ ↦ one_pos) zero_le_one]
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]
  rw [volume_real_weightedSimplex (fun _ ↦ one_pos) zero_le_one]
  norm_num
