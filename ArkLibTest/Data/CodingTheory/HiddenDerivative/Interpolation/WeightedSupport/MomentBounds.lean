/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.MomentBounds
import Mathlib.Analysis.Real.Sqrt

/-!
# Acceptance cases for the weighted-support moment bounds

These cases show that the weakened dimension hypotheses are sharp or needed, derive the source
statements with `10000 ≤ d` and `48000 ≤ d`, and combine the two third-moment bounds.
-/

open ReedSolomon.HiddenDerivative

/-- The bound `150 < d` in `weightedSupport_variance_factor_gt` is sharp: at `d = 150`,
`H = √(3 / 2)` and `H₂ = 38 / 25` the other hypotheses hold with equality and the factor equals
`3 / 2`. -/
example : ∃ H : ℝ, H ^ 2 ≤ 150 / 100 ∧
    (150 : ℝ) / (150 + 1) * (38 / 25 - H ^ 2 / 150) = 3 / 2 := by
  refine ⟨√(3 / 2), ?_, ?_⟩ <;> rw [Real.sq_sqrt (by norm_num)] <;> norm_num

/-- The source's `weightedSupport_variance_factor_gt`, with `10000 ≤ d`. -/
example {d H H₂ : ℝ} (hd : 10000 ≤ d) (hH : H ^ 2 ≤ d / 100) (h₂ : 38 / 25 ≤ H₂) :
    (3 / 2 : ℝ) < d / (d + 1) * (H₂ - H ^ 2 / d) :=
  weightedSupport_variance_factor_gt (by linarith) hH h₂

/-- A lower bound on `d` is needed in `weightedSupport_third_factor_numeric`: at
`d = H = 1 / 100` and `H₃ = 12021 / 10000` the other hypotheses hold and the bound fails. -/
example : ((1 : ℝ) / 100) ^ 2 ≤ (1 / 100) / 100 ∧
    ¬ (2 * ((12021 : ℝ) / 10000 + 2 * (1 / 100) ^ 3 / (1 / 100) ^ 2) ≤ 241 / 100) := by
  norm_num

/-- The source's `weightedSupport_third_factor_numeric`, with `48000 ≤ d`. -/
example {d H H₃ : ℝ} (hd : 48000 ≤ d) (hH : 0 ≤ H) (hHsq : H ^ 2 ≤ d / 100)
    (h₃ : H₃ ≤ 12021 / 10000) :
    2 * (H₃ + 2 * H ^ 3 / d ^ 2) ≤ (241 / 100 : ℝ) :=
  weightedSupport_third_factor_numeric (by linarith) hH hHsq h₃

/-- The two third-moment bounds combine: for `1 ≤ d` and the harmonic hypotheses, the third
centered moment factor is at most `241 / 100`. -/
example {d H H₂ H₃ : ℝ} (hd : 1 ≤ d) (hH : 0 ≤ H) (hHsq : H ^ 2 ≤ d / 100) (h₂ : 0 ≤ H₂)
    (h₃0 : 0 ≤ H₃) (h₃ : H₃ ≤ 12021 / 10000) :
    2 * (d ^ 2 * H₃ - 3 * d * H * H₂ + 2 * H ^ 3) / ((d + 1) * (d + 2)) ≤ 241 / 100 :=
  (weightedSupport_third_factor_le (by linarith) hH h₂ h₃0).trans
    (weightedSupport_third_factor_numeric hd hH hHsq h₃)

/-- At `d = 1`, `H = H₂ = 0` and `H₃ = 1` the third-moment factor is `2 / 6`, below its bound
`2`. -/
example : 2 * ((1 : ℝ) ^ 2 * 1 - 3 * 1 * 0 * 0 + 2 * 0 ^ 3) / ((1 + 1) * (1 + 2)) = 1 / 3 ∧
    2 * ((1 : ℝ) + 2 * 0 ^ 3 / 1 ^ 2) = 2 := by
  norm_num
