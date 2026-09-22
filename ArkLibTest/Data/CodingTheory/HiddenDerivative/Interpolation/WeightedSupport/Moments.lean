/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Moments

/-!
# Acceptance cases for the centered radius moments and the cubic contribution

Concrete moments of the normalized radius for `n = 0, 1, 2`; the moments and the contribution
bound as integrals against the uniform probability measure, derived from the set-average
statements; and the sharpness of the threshold `s ≤ 10 / 27` in the numeric step.
-/

open MeasureTheory Set Finset ReedSolomon.HiddenDerivative
open scoped ProbabilityTheory

/-- With no coordinates the radius and its mean are both `0`. -/
example (W t : ℝ) (u : Fin 0 → ℝ) : normalizedRadius W t u = 0 := by
  simp [normalizedRadius]

/-- For `n = 1` the radius is uniform on `[0, W]`, so `normalizedRadius W t` has variance
`W ^ 2 / (12 * t ^ 2)`. -/
example {W : ℝ} (hW : 0 ≤ W) (t : ℝ) :
    ⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) W, normalizedRadius W t u ^ 2 =
      W ^ 2 / (12 * t ^ 2) := by
  rw [setAverage_normalizedRadius_sq 1 hW t]
  norm_num [harmonic]
  ring

/-- For `n = 1` the third moment is `0`, since the uniform distribution is symmetric. -/
example {W : ℝ} (hW : 0 ≤ W) (t : ℝ) :
    ⨍ u in weightedSimplex (fun i : Fin 1 ↦ (i : ℝ) + 1) W, normalizedRadius W t u ^ 3 = 0 := by
  rw [setAverage_normalizedRadius_cube 1 hW t]
  norm_num [harmonic]

/-- For `n = 2` (the triangle `u₀ + 2 u₁ ≤ W`), `H = 3 / 2` and `H₂ = 5 / 4`, so the variance of
`normalizedRadius W t` is `W ^ 2 / (24 * t ^ 2)`. -/
example {W : ℝ} (hW : 0 ≤ W) (t : ℝ) :
    ⨍ u in weightedSimplex (fun i : Fin 2 ↦ (i : ℝ) + 1) W, normalizedRadius W t u ^ 2 =
      W ^ 2 / (24 * t ^ 2) := by
  rw [setAverage_normalizedRadius_sq 2 hW t]
  norm_num [harmonic, Fin.sum_univ_two, Finset.sum_range_succ]
  ring

/-- The normalized radius has mean `0` under the uniform probability measure. -/
example (n : ℕ) {W : ℝ} (t : ℝ) :
    (∫ u, normalizedRadius W t u ∂volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W]) =
      0 := by
  rw [ProbabilityTheory.cond, ← setAverage_eq', setAverage_normalizedRadius]

/-- The second moment of the normalized radius under the uniform probability measure. -/
example (n : ℕ) {W : ℝ} (hW : 0 < W) (t : ℝ) :
    (∫ u, normalizedRadius W t u ^ 2
        ∂volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W]) =
      (W / ((n + 1) * t)) ^ 2 * (n + 1) / (n + 2) *
        (∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2 - (harmonic n : ℝ) ^ 2 / (n + 1)) := by
  rw [ProbabilityTheory.cond, ← setAverage_eq', setAverage_normalizedRadius_sq n hW.le]

/-- The third moment of the normalized radius under the uniform probability measure. -/
example (n : ℕ) {W : ℝ} (hW : 0 < W) (t : ℝ) :
    (∫ u, normalizedRadius W t u ^ 3
        ∂volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W]) =
      2 * (W / ((n + 1) * t)) ^ 3 *
        ((n + 1) ^ 2 * ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 3 -
          3 * (n + 1) * (harmonic n : ℝ) * ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2 +
          2 * (harmonic n : ℝ) ^ 3) / ((n + 2) * (n + 3)) := by
  rw [ProbabilityTheory.cond, ← setAverage_eq', setAverage_normalizedRadius_cube n hW.le]

/-- `normalizedRadius_contribution_lower` as an integral against the uniform probability measure,
with the extra hypotheses `0 < t` and `48000 ≤ n + 1` (the latter unused). -/
example (n : ℕ) {W t : ℝ} (hW : 0 < W) (ht : 0 < t) (_hd : 48000 ≤ (n : ℝ) + 1)
    (hHsq : (harmonic n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) / 100)
    (hH₂ : 38 / 25 ≤ ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 2)
    (hH₃ : ∑ i : Fin n, 1 / ((i : ℝ) + 1) ^ 3 ≤ 12021 / 10000)
    (hs : W / (((n : ℝ) + 1) * t) ≤ 10 / 27) :
    (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (W / (((n : ℝ) + 1) * t)) ^ 2 ≤
      ∫ u, (max (5 / 8 - normalizedRadius W t u) 0) ^ 3
        ∂volume[|weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1) W] := by
  rw [ProbabilityTheory.cond, ← setAverage_eq']
  exact normalizedRadius_contribution_lower n hW ht.le hHsq hH₂ hH₃ hs

/-- The threshold `10 / 27` in `cubic_contribution_numeric` is sharp: at `s = 1 / 2`, with
`v₂ = 3 / 2 * s ^ 2` and `v₃ = 241 / 100 * s ^ 3`, the conclusion fails. -/
example : ¬ ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (1 / 2) ^ 2 ≤
    (5 / 8 : ℝ) ^ 3 + 3 * (5 / 8) * (3 / 2 * (1 / 2) ^ 2) - 241 / 100 * (1 / 2) ^ 3) := by
  norm_num

/-- At the threshold `s = 10 / 27` the numeric step is an equality for the extreme moments. -/
example : (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (10 / 27) ^ 2 =
    (5 / 8 : ℝ) ^ 3 + 3 * (5 / 8) * (3 / 2 * (10 / 27) ^ 2) - 241 / 100 * (10 / 27) ^ 3 := by
  norm_num

/-- `contribution_integral_lower` for the zero variable under a Dirac measure and `s = 0`: the
bound `(5 / 8) ^ 3` is the value of the integral. -/
example : (5 / 8 : ℝ) ^ 3 + (4147 / 2160) * 0 ^ 2 ≤
    ∫ _x, (max (5 / 8 - (0 : ℝ)) 0) ^ 3 ∂Measure.dirac (0 : ℝ) :=
  contribution_integral_lower (Measure.dirac (0 : ℝ)) (fun _ ↦ 0) 0 (integrable_const _)
    (by simp) (by simp) (by norm_num) (by simp) (by simp)
