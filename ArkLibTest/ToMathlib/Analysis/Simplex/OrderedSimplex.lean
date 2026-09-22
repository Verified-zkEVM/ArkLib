/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.Simplex.Moments
import ArkLib.ToMathlib.Analysis.Simplex.OrderedSimplex

/-!
# Acceptance cases for the ordered simplex

Membership and volume of concrete ordered simplices, the necessity of `0 ≤ W` for the volume, the
sorting identity for a constant, the need for permutation invariance in the sorting identity, and
the law of the largest coordinate in the ordered-simplex form.
-/

open MeasureTheory Set Finset

/-- `(2, 1, 0)` has nonnegative decreasing coordinates with total `3`. -/
example : (![2, 1, 0] : Fin 3 → ℝ) ∈ orderedSimplex 3 3 := by
  refine mem_orderedSimplex.2 ⟨fun i ↦ by fin_cases i <;> norm_num, ?_, by
    simp [Fin.sum_univ_three]; norm_num⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]

/-- `(0, 1)` is not decreasing. -/
example : (![0, 1] : Fin 2 → ℝ) ∉ orderedSimplex 2 3 := by
  intro h
  have h' := (mem_orderedSimplex.1 h).2.1 (Fin.zero_le (1 : Fin 2))
  norm_num at h'

/-- The triangle `v₀ ≥ v₁ ≥ 0`, `v₀ + v₁ ≤ 2`, with vertices `0`, `(2, 0)`, `(1, 1)`, has area
`2 ^ 2 / (2!) ^ 2 = 1`. -/
example : volume.real (orderedSimplex 2 2) = 1 := by
  rw [volume_real_orderedSimplex 2 (by norm_num)]
  norm_num [Nat.factorial]

/-- `0 ≤ W` is needed: with no coordinates, `orderedSimplex 0 (-1)` is empty (the total `0` is not
at most `-1`), while `(-1) ^ 0 / (0!) ^ 2 = 1`. -/
example : orderedSimplex 0 (-1) = ∅ := by
  ext v
  simp

/-- Sorting the constant `1`: the triangle `x₀ + x₁ ≤ 1`, of area `1 / 2`, is two copies of the
ordered triangle of area `1 / 4`. -/
example : volume.real (standardSimplex (Fin 2) 1) =
    2 * volume.real (orderedSimplex 2 1) := by
  have h := setIntegral_standardSimplex_of_comp_perm (n := 2) (f := fun _ ↦ (1 : ℝ))
    (fun _ _ ↦ rfl) 1
  simpa [Nat.factorial] using h

/-- Permutation invariance is needed in `setIntegral_standardSimplex_of_comp_perm`: the first
coordinate integrates to `1 / 6` over the triangle `x₀ + x₁ ≤ 1` and to `1 / 8` over the ordered
triangle, and `1 / 6 ≠ 2 * (1 / 8)`. The second integral is the area `1 / 4` of the ordered
triangle times the average of `v₀`, which is the mean `1 / 2` of `u₀ + u₁` on the weighted
triangle `u₀ + 2 u₁ ≤ 1`. -/
example : (∫ x in standardSimplex (Fin 2) 1, x 0) ≠
    (Nat.factorial 2 : ℝ) * ∫ v in orderedSimplex 2 1, v 0 := by
  have hstd : (∫ x in standardSimplex (Fin 2) 1, x 0) = 1 / 6 := by
    have h := integral_standardSimplex_prod_pow_mul_pow (ι := Fin 2) ![1, 0] 0 zero_le_one
    norm_num [Fin.prod_univ_two, Fin.sum_univ_two, Nat.factorial] at h
    exact h
  have hord : (∫ v in orderedSimplex 2 1, v 0) = 1 / 8 := by
    have hlaw := setAverage_weightedSimplex_succ_sum_eq_orderedSimplex (n := 2) 1 fun m ↦ m
    have hvol' : volume.real (orderedSimplex 2 1) = 1 / 4 := by
      rw [volume_real_orderedSimplex 2 zero_le_one]
      norm_num [Nat.factorial]
    have hmean := setAverage_weightedSimplex_succ_sum 2 one_pos
    rw [hlaw] at hmean
    have hH : (harmonic 2 : ℝ) = 3 / 2 := by
      norm_num [harmonic, Finset.sum_range_succ]
    rw [hH, setAverage_eq, hvol', smul_eq_mul] at hmean
    norm_num at hmean
    linarith
  rw [hstd, hord]
  norm_num [Nat.factorial]

/-- The law of the largest coordinate in the ordered-simplex form: for every `g`, the integral
of `g (maxᵢ x i)` over the standard simplex is `n!` times the integral of `g (v 0)` over the
ordered simplex. -/
example (n : ℕ) [NeZero n] (W : ℝ) (g : ℝ → ℝ) :
    ∫ x in standardSimplex (Fin n) W, g (univ.sup' univ_nonempty x) =
      n.factorial * ∫ v in orderedSimplex n W, g (v 0) := by
  rw [setIntegral_standardSimplex_of_comp_perm (f := fun x ↦ g (univ.sup' univ_nonempty x))
    (fun σ x ↦ by rw [sup'_univ_comp_perm]) W]
  congr 1
  refine setIntegral_congr_fun (measurableSet_orderedSimplex n W) fun v hv ↦ ?_
  rw [sup'_univ_eq_apply_zero_of_antitone hv.2.1]

/-- The largest coordinate of `(0, 1, 3)` is `3`, the first coordinate after sorting. -/
example : univ.sup' univ_nonempty (![0, 1, 3] : Fin 3 → ℝ) = 3 := by
  have h := sup'_univ_comp_perm (Equiv.swap 0 2) (![0, 1, 3] : Fin 3 → ℝ)
  rw [← h, sup'_univ_eq_apply_zero_of_antitone]
  · simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def, Equiv.swap_apply_def]
