/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Analysis.Simplex.CenteredMoments

/-!
# Acceptance cases for centered simplex moments

The uniform distribution on `[0, W]` (one coordinate, unit weight) has mean `W / 2`, variance
`W ^ 2 / 12` and third central moment `0`; the linear form `2 u₀ + 3 u₁` on the triangle
`2 u₀ + 3 u₁ ≤ 6` has variance `2` and third central moment `-8 / 5`. Further cases: the mean
statement at a negative budget, the necessity of `0 ≤ W` for the variance, and integrability of
continuous functions under the uniform probability measure without a budget hypothesis. The
variance bound by the power sum `∑ (c i / w i) ^ 2` is checked on the triangle, compared with the
exact variance on a segment (where it is twice the variance), and applied at a negative budget.
-/

open MeasureTheory Set Finset
open scoped ProbabilityTheory

/-- On `[0, W]`, `u₀ - W / 2` has mean `0`, for every real `W`. -/
example (W : ℝ) : ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) W, (u 0 - W / 2) = 0 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean (w := fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ ↦ one_pos) 1 W
  norm_num at h
  simpa [div_eq_mul_inv] using h

/-- The variance of the uniform distribution on `[0, W]` is `W ^ 2 / 12`. -/
example {W : ℝ} (hW : 0 ≤ W) :
    ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) W, (u 0 - W / 2) ^ 2 = W ^ 2 / 12 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_sq (w := fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ ↦ one_pos) 1 hW
  norm_num at h
  exact h

/-- The third central moment of the uniform distribution on `[0, W]` is `0`. -/
example {W : ℝ} (hW : 0 ≤ W) :
    ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) W, (u 0 - W / 2) ^ 3 = 0 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_cube (w := fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ ↦ one_pos) 1 hW
  norm_num at h
  exact h

/-- On the triangle `2 u₀ + 3 u₁ ≤ 6`, the form `2 u₀ + 3 u₁` has mean `4` and variance `2`
(its density on `[0, 6]` is `x / 18`). -/
example : ⨍ u in weightedSimplex (![2, 3] : Fin 2 → ℝ) 6,
    (∑ i, (![2, 3] : Fin 2 → ℝ) i * u i - 4) ^ 2 = 2 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_sq (w := ![2, 3])
    (by intro i; fin_cases i <;> norm_num) (![2, 3] : Fin 2 → ℝ) (W := 6) (by norm_num)
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h

/-- On the same triangle, the third central moment of `2 u₀ + 3 u₁` is `-8 / 5`. -/
example : ⨍ u in weightedSimplex (![2, 3] : Fin 2 → ℝ) 6,
    (∑ i, (![2, 3] : Fin 2 → ℝ) i * u i - 4) ^ 3 = -8 / 5 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_cube (w := ![2, 3])
    (by intro i; fin_cases i <;> norm_num) (![2, 3] : Fin 2 → ℝ) (W := 6) (by norm_num)
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h

/-- `0 ≤ W` is needed in `setAverage_weightedSimplex_linearForm_sub_mean_sq`: for `W = -1` the
simplex is empty, so the average is `0`, while the formula gives `(-1) ^ 2 / 12`. -/
example : ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) (-1),
      (∑ i, (1 : Fin 1 → ℝ) i * u i - (-1) * (∑ i, (1 : Fin 1 → ℝ) i / 1) /
        (Fintype.card (Fin 1) + 1)) ^ 2 ≠
    (-1) ^ 2 * ((Fintype.card (Fin 1) + 1) * ∑ i, ((1 : Fin 1 → ℝ) i / 1) ^ 2 -
      (∑ i, (1 : Fin 1 → ℝ) i / 1) ^ 2) / ((Fintype.card (Fin 1) + 1) ^ 2 *
        (Fintype.card (Fin 1) + 2)) := by
  have he : weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) (-1) = ∅ := by
    ext u
    simp only [mem_weightedSimplex, one_mul, Fin.sum_univ_one, mem_empty_iff_false, iff_false,
      not_and, not_le]
    intro h
    linarith [h 0]
  rw [he]
  norm_num

/-- The source's `integrable_weighted_probability`: a continuous function is integrable for the
uniform measure on the weighted simplex. No budget hypothesis is needed. -/
example (n : ℕ) (W : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W] :=
  (hf.continuousOn.integrableOn_weightedSimplex fun i ↦ by positivity).integrable_cond

/-- The variance bound on the triangle `2 u₀ + 3 u₁ ≤ 6`: the exact variance is `2`, and the bound
`6 ^ 2 * (1 + 1) / (3 * 4)` is `6`. -/
example : ⨍ u in weightedSimplex (![2, 3] : Fin 2 → ℝ) 6,
    (∑ i, (![2, 3] : Fin 2 → ℝ) i * u i - 4) ^ 2 ≤ 6 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_sq_le (w := ![2, 3])
    (by intro i; fin_cases i <;> norm_num) (![2, 3] : Fin 2 → ℝ) 6
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h

/-- With one coordinate the bound is twice the variance: on `[0, W]` the variance of `u₀` is
`W ^ 2 / 12` and the bound is `W ^ 2 / 6`. -/
example (W : ℝ) (hW : 0 ≤ W) :
    ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) W, (u 0 - W / 2) ^ 2 = W ^ 2 / 12 ∧
      ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) W, (u 0 - W / 2) ^ 2 ≤ W ^ 2 / 6 := by
  have heq := setAverage_weightedSimplex_linearForm_sub_mean_sq (w := fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ ↦ one_pos) 1 hW
  have hle := setAverage_weightedSimplex_linearForm_sub_mean_sq_le
    (w := fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ ↦ one_pos) 1 W
  norm_num at heq hle
  refine ⟨?_, ?_⟩
  · rw [heq]
  · refine hle.trans_eq ?_; ring

/-- The variance bound needs no budget hypothesis: at `W = -1` it reads `0 ≤ 1 / 6` on the empty
segment. -/
example : ⨍ u in weightedSimplex (fun _ : Fin 1 ↦ (1 : ℝ)) (-1), (u 0 - (-1) / 2) ^ 2 ≤ 1 / 6 := by
  have h := setAverage_weightedSimplex_linearForm_sub_mean_sq_le
    (w := fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ ↦ one_pos) 1 (-1)
  norm_num at h ⊢
  exact h
