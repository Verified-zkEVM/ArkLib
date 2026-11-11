/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.Simplex.CenteredMoments
import ArkLib.ToMathlib.Analysis.Simplex.MaxCoordinate
import ArkLib.ToMathlib.Analysis.Simplex.Moments
import ArkLib.ToMathlib.Analysis.Simplex.MonomialIntegral
import ArkLib.ToMathlib.Analysis.Simplex.OrderedSimplex
import ArkLib.ToMathlib.Analysis.Simplex.VolumeIntegral
import ArkLib.ToMathlib.Analysis.Simplex.WeightedVolume

/-!
# Concrete simplex integrals, volumes, and moments

Small examples check simplex volume and integral formulas, ordered-simplex symmetry, and concrete
moments of coordinates and linear forms.
-/

open MeasureTheory Set Finset
open scoped ProbabilityTheory

/-- On `[0, 2]`, `u₀ - 1` has mean `0`. -/
example : ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) 2, (u 0 - 1) = 0 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean (w := fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ ↦ one_pos) 1 2
  norm_num at h
  simpa [div_eq_mul_inv] using h

/-- The variance of the uniform distribution on `[0, 2]` is `1 / 3`. -/
example : ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) 2, (u 0 - 1) ^ 2 = 1 / 3 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_sq (w := fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ ↦ one_pos) 1 (W := 2) (by norm_num)
  norm_num at h
  exact h

/-- On the same triangle, the third central moment of `2 u₀ + 3 u₁` is `-8 / 5`. -/
example : ⨍ u in weightedSimplex (![2, 3] : Fin 2 → ℝ) 6,
    (∑ i, (![2, 3] : Fin 2 → ℝ) i * u i - 4) ^ 3 = -8 / 5 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_cube (w := ![2, 3])
    (by intro i; fin_cases i <;> norm_num) (![2, 3] : Fin 2 → ℝ) (W := 6) (by norm_num)
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h

/-- On the triangle `x₀ + x₁ ≤ 1`, the part where `1 / 2 ≤ x₀` has area `1 / 8`. -/
example : volume.real (standardSimplex (Fin 2) 1 ∩ {x | 1 / 2 ≤ x 0}) = 1 / 8 := by
  rw [volume_real_standardSimplex_inter_le_apply 0 (by norm_num) (by norm_num)]
  norm_num [Nat.factorial]

/-- The union bound on `x₀ + x₁ ≤ 1` bounds the largest-coordinate tail area by `1 / 4`. -/
example : volume.real (standardSimplex (Fin 2) 1 ∩ {x | 1 / 2 ≤ univ.sup' univ_nonempty x}) ≤
    1 / 4 := by
  refine (volume_real_standardSimplex_inter_le_sup'_le (by norm_num) (by norm_num)).trans ?_
  norm_num [Nat.factorial]

/-- The larger coordinate on the unit triangle has mean `1 / 2`. -/
example : ⨍ x in standardSimplex (Fin 2) 1, univ.sup' univ_nonempty x = 1 / 2 := by
  rw [setAverage_standardSimplex_sup' 2 one_pos]
  norm_num [harmonic, Finset.sum_range_succ]

/-- `∫₀¹ x² dx = 1 / 3`: the second moment on the one-dimensional simplex. -/
example : (∫ x in standardSimplex (Fin 1) 1, (∑ i, (1 : ℝ) * x i) ^ 2) = 1 / 3 := by
  rw [integral_standardSimplex_linearForm_pow _ _ (by norm_num)]
  have h := MvPolynomial.two_mul_eval_hsymm_two (fun _ : Fin 1 ↦ (1 : ℝ))
  simp only [Fin.sum_univ_one, one_pow] at h
  have h1 : MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℝ))
      (MvPolynomial.hsymm (Fin 1) ℝ 2) = 1 := by nlinarith [h]
  rw [h1]
  norm_num [Nat.factorial]

/-- On `2 u₀ + 3 u₁ ≤ 6`, the form `2 u₀ + 3 u₁` has mean `4`. -/
example : ⨍ u in weightedSimplex (![2, 3] : Fin 2 → ℝ) 6,
    ∑ i, (![2, 3] : Fin 2 → ℝ) i * u i = 4 := by
  rw [setAverage_weightedSimplex_linearForm (by intro i; fin_cases i <;> norm_num) _
    (by norm_num)]
  norm_num [Fin.sum_univ_two]

/-- The coordinate sum on weights `1, 2` with budget `6` has mean `3`. -/
example : ⨍ u in weightedSimplex (fun i : Fin 2 ↦ (i : ℝ) + 1) 6, ∑ i, u i = 3 := by
  rw [setAverage_weightedSimplex_succ_sum 2 (by norm_num)]
  norm_num [harmonic, Finset.sum_range_succ]

/-- The second and third moments of the coordinate on `[0, 2]` are `4 / 3` and `2`. -/
example :
    (⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) 2, (∑ i, u i) ^ 2 = 4 / 3) ∧
    (⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) 2, (∑ i, u i) ^ 3 = 2) := by
  have h2 := setAverage_weightedSimplex_succ_sum_sq 1 (by norm_num : (0 : ℝ) < 2)
  have h3 := setAverage_weightedSimplex_succ_sum_cube 1 (by norm_num : (0 : ℝ) < 2)
  norm_num at h2 h3 ⊢
  exact ⟨h2, h3⟩

/-- `∫₀¹ x (1 - x) dx = 1 / 6`. -/
example : (∫ x : ℝ in (0 : ℝ)..1, x ^ 1 * (1 - x) ^ 1) = 1 / 6 := by
  rw [integral_pow_mul_one_sub_pow]
  norm_num [Nat.factorial]

/-- `∫₀³ x² dx = 9` from the beta formula. -/
example : (∫ x : ℝ in (0 : ℝ)..3, x ^ 2 * (3 - x) ^ 0) = 9 := by
  rw [integral_pow_mul_sub_pow]
  norm_num [Nat.factorial]

/-- The suffix-sum map transports a nonconstant coordinate integral on the weighted triangle. -/
example : (∫ u in weightedSimplex (fun i : Fin 2 ↦ (i : ℝ) + 1) 1,
    ∑ j ∈ Ici (0 : Fin 2), u j) = ∫ v in orderedSimplex 2 1, v 0 := by
  simpa using setIntegral_weightedSimplex_succ_comp_suffixSum (n := 2) 1
    (fun v : Fin 2 → ℝ ↦ v 0)

/-- The Dirichlet integral on the unit triangle is `1 / 24`. -/
example : (∫ x in standardSimplex (Fin 2) 1,
    (∏ i, x i ^ (![1, 0] : Fin 2 → ℕ) i) * (1 - ∑ i, x i) ^ 1) = 1 / 24 := by
  rw [integral_standardSimplex_prod_pow_mul_pow _ _ zero_le_one]
  simp [Fin.sum_univ_two, Fin.prod_univ_two, Nat.factorial]

/-- The tetrahedron of side `2` has volume `4 / 3`. -/
example : volume.real (standardSimplex (Fin 3) 2) = 4 / 3 := by
  rw [volume_real_standardSimplex _ zero_le_two, Fintype.card_fin]
  norm_num [Nat.factorial]

/-- The triangle `2 u₀ + 3 u₁ ≤ 6` has area `3`. -/
example : volume.real (weightedSimplex (![2, 3] : Fin 2 → ℝ) 6) = 3 := by
  rw [volume_real_weightedSimplex (by intro i; fin_cases i <;> norm_num) (by norm_num)]
  simp [Fin.prod_univ_two]
  norm_num

/-- The weighted Dirichlet integral `∫₀¹ u du = 1 / 2` on `2 u ≤ 2`. -/
example : (∫ u in weightedSimplex (fun _ : Fin 1 ↦ (2 : ℝ)) 2,
    (∏ i, u i ^ (fun _ : Fin 1 ↦ 1) i) * (2 - ∑ i, (2 : ℝ) * u i) ^ 0) = 1 / 2 := by
  rw [integral_weightedSimplex_prod_pow_mul_pow (fun _ ↦ by norm_num) _ _ (by norm_num)]
  norm_num [Nat.factorial]

/-- Weights `1, 2` and budget `4` give a triangle of area `4`. -/
example : volume.real (weightedSimplex (fun i : Fin 2 ↦ (i : ℝ) + 1) 4) = 4 := by
  rw [volume_real_weightedSimplex_succ 2 (by norm_num)]
  norm_num [Nat.factorial]

/-- Weighted change of variables for the first coordinate on a one-dimensional simplex. -/
example : (∫ u in weightedSimplex (fun _ : Fin 1 ↦ (2 : ℝ)) 2, u 0) =
    (1 / 2 : ℝ) * ∫ t in standardSimplex (Fin 1) 2, t 0 / 2 := by
  simpa using setIntegral_weightedSimplex (fun _ : Fin 1 ↦ (by norm_num : 0 < (2 : ℝ))) 2
    (fun u : Fin 1 → ℝ ↦ u 0)

/-- A positive dilation transports the first-coordinate integral on `[0, 1]` to `[0, 2]`. -/
example : (∫ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) (2 * 1), u 0) =
    (2 : ℝ) ^ Fintype.card (Fin 1) *
      ∫ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) 1, ((2 : ℝ) • u) 0 := by
  simpa using setIntegral_weightedSimplex_mul (fun _ : Fin 1 ↦ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 2) 1 (fun u : Fin 1 → ℝ ↦ u 0)

/-- Enlarging the unit interval's budget to `2` obeys the exponential volume bound. -/
example : volume.real (weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) (1 + 1)) ≤
    volume.real (weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) 1) * Real.exp (1 * 1 / 1) := by
  simpa using volume_real_weightedSimplex_add_le_mul_exp
    (w := fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ ↦ by norm_num) (W := 1) (by norm_num) 1
