/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite estimates for the centered simplex moments

Once simplex integration supplies the moment identities, their estimates are elementary real
inequalities. This module isolates that arithmetic from integration: the variance uses a lower
bound on the second harmonic sum, and the third moment uses upper harmonic bounds.
The identities themselves are separate obligations; these lemmas do not assume a probability
model or claim to construct one.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- The normalized variance is strictly larger than `3/2` at every allowed dimension. -/
theorem weightedSupport_variance_factor_gt {d H H₂ : ℝ}
    (hd : 10000 ≤ d) (hH : H ^ 2 ≤ d / 100) (h₂ : 38 / 25 ≤ H₂) :
    (3 / 2 : ℝ) < d / (d + 1) * (H₂ - H ^ 2 / d) := by
  have hd0 : 0 < d := by linarith
  have hden : 0 < d + 1 := by linarith
  have hid : d / (d + 1) * (H₂ - H ^ 2 / d) =
      (d * H₂ - H ^ 2) / (d + 1) := by field_simp
  rw [hid, lt_div_iff₀ hden]
  nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr h₂)]

/-- Dropping the negative mixed term bounds the third centered moment factor. -/
theorem weightedSupport_third_factor_le {d H H₂ H₃ : ℝ}
    (hd : 0 < d) (hH : 0 ≤ H) (h₂ : 0 ≤ H₂) (h₃ : 0 ≤ H₃) :
    2 * (d ^ 2 * H₃ - 3 * d * H * H₂ + 2 * H ^ 3) / ((d + 1) * (d + 2)) ≤
      2 * (H₃ + 2 * H ^ 3 / d ^ 2) := by
  have hden : 0 < (d + 1) * (d + 2) := by positivity
  have hneg : 0 ≤ 3 * d * H * H₂ := by positivity
  have hright : 0 ≤ 2 * (H₃ + 2 * H ^ 3 / d ^ 2) := by positivity
  have he : 2 * (d ^ 2 * H₃ + 2 * H ^ 3) = (2 * (H₃ + 2 * H ^ 3 / d ^ 2)) * d ^ 2 := by field_simp
  rw [div_le_iff₀ hden]
  have hp := mul_le_mul_of_nonneg_left (show d ^ 2 ≤ (d + 1) * (d + 2) by nlinarith) hright
  nlinarith

/-- Finite harmonic bounds give the third-moment coefficient `2.41`. -/
theorem weightedSupport_third_factor_numeric {d H H₃ : ℝ}
    (hd : 48000 ≤ d) (hH : 0 ≤ H) (hHsq : H ^ 2 ≤ d / 100)
    (h₃ : H₃ ≤ 12021 / 10000) :
    2 * (H₃ + 2 * H ^ 3 / d ^ 2) ≤ (241 / 100 : ℝ) := by
  have hd0 : 0 < d := by linarith
  have hHlin : H ≤ d / 100 := by
    nlinarith [sq_nonneg (H - d / 100)]
  have hprod := mul_le_mul hHsq hHlin hH (by positivity : (0:ℝ) ≤ d / 100)
  have hcube : H ^ 3 / d ^ 2 ≤ (1 / 10000:ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos hd0)]
    nlinarith
  rw [mul_div_assoc]
  linarith
end ReedSolomon.HiddenDerivative
