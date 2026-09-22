/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Numerical bounds for the centered weighted-support moments

The hidden-derivative dimension estimate normalizes the total degree of a random point of the
weighted simplex. Its second and third centered moments are expressed through the dimension `d`
and harmonic-type sums `H`, `H₂`, `H₃`: the variance factor is `d / (d + 1) * (H₂ - H ^ 2 / d)`
and the third-moment factor is
`2 * (d ^ 2 * H₃ - 3 * d * H * H₂ + 2 * H ^ 3) / ((d + 1) * (d + 2))`. This file proves the real
inequalities that turn bounds on the harmonic sums into the constants `3 / 2` and `2.41` used by
the estimate. It does not prove the moment identities themselves.

## Main statements

* `ReedSolomon.HiddenDerivative.weightedSupport_variance_factor_gt`: the variance factor exceeds
  `3 / 2` when `150 < d`, `H ^ 2 ≤ d / 100` and `38 / 25 ≤ H₂`.
* `ReedSolomon.HiddenDerivative.weightedSupport_third_factor_le`: dropping the negative mixed term
  bounds the third-moment factor by `2 * (H₃ + 2 * H ^ 3 / d ^ 2)`.
* `ReedSolomon.HiddenDerivative.weightedSupport_third_factor_numeric`: that bound is at most
  `241 / 100` when `1 ≤ d`, `H ^ 2 ≤ d / 100` and `H₃ ≤ 12021 / 10000`.

## References

Ports `weightedSupport_variance_factor_gt`, `weightedSupport_third_factor_le` and
`weightedSupport_third_factor_numeric` from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`MomentBounds.lean` at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The dimension
hypotheses are weakened to what the arithmetic needs: `10000 ≤ d` becomes `150 < d`, which is sharp,
and `48000 ≤ d` becomes `1 ≤ d`. The acceptance tests derive the source statements.

Deferred: the moment identities (`normalizedRadius` and its first three moments in the source's
`WeightedSupport/Moments.lean`), which need the continuous simplex moments of P9 slice 4, and the
harmonic-sum bounds that supply `H`, `H₂` and `H₃`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- The variance factor `d / (d + 1) * (H₂ - H ^ 2 / d)` is strictly larger than `3 / 2` when
`150 < d`, `H ^ 2 ≤ d / 100` and `38 / 25 ≤ H₂`. The factor equals `(d * H₂ - H ^ 2) / (d + 1)`,
and the hypotheses bound its numerator below by `151 * d / 100`, which exceeds `3 * (d + 1) / 2`
exactly when `150 < d`. The bound is sharp: at `d = 150`, `H ^ 2 = 3 / 2` and `H₂ = 38 / 25` the
factor equals `3 / 2`. -/
theorem weightedSupport_variance_factor_gt {d H H₂ : ℝ}
    (hd : 150 < d) (hH : H ^ 2 ≤ d / 100) (h₂ : 38 / 25 ≤ H₂) :
    (3 / 2 : ℝ) < d / (d + 1) * (H₂ - H ^ 2 / d) := by
  have hd0 : 0 < d := by linarith
  have hden : 0 < d + 1 := by linarith
  have hid : d / (d + 1) * (H₂ - H ^ 2 / d) = (d * H₂ - H ^ 2) / (d + 1) := by
    field_simp
  rw [hid, lt_div_iff₀ hden]
  nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr h₂)]

/-- Dropping the negative mixed term `-3 * d * H * H₂` and using `d ^ 2 ≤ (d + 1) * (d + 2)`
bounds the third-moment factor
`2 * (d ^ 2 * H₃ - 3 * d * H * H₂ + 2 * H ^ 3) / ((d + 1) * (d + 2))` by
`2 * (H₃ + 2 * H ^ 3 / d ^ 2)`. The nonnegativity hypotheses make the dropped term nonpositive and
the right side nonnegative; `0 < d` makes the division by `d ^ 2` meaningful. -/
theorem weightedSupport_third_factor_le {d H H₂ H₃ : ℝ}
    (hd : 0 < d) (hH : 0 ≤ H) (h₂ : 0 ≤ H₂) (h₃ : 0 ≤ H₃) :
    2 * (d ^ 2 * H₃ - 3 * d * H * H₂ + 2 * H ^ 3) / ((d + 1) * (d + 2)) ≤
      2 * (H₃ + 2 * H ^ 3 / d ^ 2) := by
  have hden : 0 < (d + 1) * (d + 2) := by positivity
  have hneg : 0 ≤ 3 * d * H * H₂ := by positivity
  have hright : 0 ≤ 2 * (H₃ + 2 * H ^ 3 / d ^ 2) := by positivity
  have he : 2 * (d ^ 2 * H₃ + 2 * H ^ 3) = (2 * (H₃ + 2 * H ^ 3 / d ^ 2)) * d ^ 2 := by
    field_simp
  rw [div_le_iff₀ hden]
  have hp := mul_le_mul_of_nonneg_left (show d ^ 2 ≤ (d + 1) * (d + 2) by nlinarith) hright
  nlinarith

/-- The bound `2 * (H₃ + 2 * H ^ 3 / d ^ 2)` is at most `241 / 100` when `1 ≤ d`, `0 ≤ H`,
`H ^ 2 ≤ d / 100` and `H₃ ≤ 12021 / 10000`. For `1 ≤ d` the second hypothesis gives
`H ≤ d / 10`, hence `H ^ 3 ≤ d ^ 2 / 1000`, and the total is at most
`2 * (12021 / 10000 + 2 / 1000) < 241 / 100`. Some lower bound on `d` is needed: at
`d = H = 1 / 100` and `H₃ = 12021 / 10000` the left side is `24442 / 10000`. -/
theorem weightedSupport_third_factor_numeric {d H H₃ : ℝ}
    (hd : 1 ≤ d) (hH : 0 ≤ H) (hHsq : H ^ 2 ≤ d / 100) (h₃ : H₃ ≤ 12021 / 10000) :
    2 * (H₃ + 2 * H ^ 3 / d ^ 2) ≤ (241 / 100 : ℝ) := by
  have hd0 : 0 < d := by linarith
  have hHlin : H ≤ d / 10 := by
    nlinarith [sq_nonneg (H - d / 10)]
  have hprod := mul_le_mul hHsq hHlin hH (by positivity : (0 : ℝ) ≤ d / 100)
  have hcube : H ^ 3 / d ^ 2 ≤ (1 / 1000 : ℝ) := by
    rw [div_le_iff₀ (pow_pos hd0 2)]
    nlinarith
  rw [mul_div_assoc]
  linarith

end ReedSolomon.HiddenDerivative
