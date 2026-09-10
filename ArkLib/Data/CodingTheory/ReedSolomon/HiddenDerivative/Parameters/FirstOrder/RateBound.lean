/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Basic

/-!
# The clean first-order rate threshold

This file proves the real-variable calculation behind the first-order interpolation recipe.
For a code-rate upper bound `R` and an agreement fraction `a`, the capped first-order support is
tuned with

```text
beta = 3 * (1 - a) / (2 * (2 - R)).
```

The source density exceeds the local-rank density whenever `a` lies above

```text
a₁(R) = (3 * R + 2 * sqrt (R * (5 - R) * (2 - R))) / (8 - R).
```

The curve is a globally sufficient threshold for this support family.  No optimality claim is
made: the cubic rank envelope deliberately discards part of the sharper piecewise rank formula.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- Clean sufficient agreement threshold for first-order interpolation. -/
def firstOrderRateThreshold (R : ℝ) : ℝ :=
  (3 * R + 2 * Real.sqrt (R * (5 - R) * (2 - R))) / (8 - R)

/-- Derivative-degree ratio used at the clean first-order threshold. -/
def firstOrderRateBeta (R a : ℝ) : ℝ :=
  3 * (1 - a) / (2 * (2 - R))

/-- Limiting normalized source count for the capped first-order support. -/
def firstOrderSourceDensity (R a beta : ℝ) : ℝ :=
  beta * a ^ 2 / (2 * R) - a * beta ^ 2 / 2 + R * beta ^ 3 / 6

/-- Exact limiting local-rank density on the range needed by the construction. -/
def firstOrderRankDensity (beta : ℝ) : ℝ :=
  if beta ≤ 1 / 2 then beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3
  else beta / 4 + 1 / 24

/-- A single cubic envelope for both branches of `firstOrderRankDensity`. -/
def firstOrderRankCubicEnvelope (beta : ℝ) : ℝ :=
  beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3

/-- Scalar inequality whose positive root is `firstOrderRateThreshold`. -/
def firstOrderCleanExpression (R a : ℝ) : ℝ :=
  a ^ 2 / R + 3 * (1 - a) ^ 2 / (4 * (2 - R))

theorem firstOrderRateBeta_pos {R a : ℝ} (ha : a < 1) (hR : R < 1) :
    0 < firstOrderRateBeta R a := by
  rw [firstOrderRateBeta]
  apply div_pos
  · nlinarith
  · nlinarith

theorem firstOrderRateBeta_lt_three_four {R a : ℝ} (hR : 0 < R) (hRa : R < a)
    (ha : a < 1) :
    firstOrderRateBeta R a < 3 / 4 := by
  rw [firstOrderRateBeta]
  have hden : 0 < 2 * (2 - R) := by nlinarith
  rw [div_lt_iff₀ hden]
  nlinarith

theorem firstOrderRateBeta_lt_agreement_div_rate {R a : ℝ}
    (hR : 0 < R) (hRa : R < a) (ha : a < 1) :
    firstOrderRateBeta R a < a / R := by
  rw [firstOrderRateBeta]
  have hden : 0 < 2 * (2 - R) := by nlinarith
  have hprod : 0 < R * (2 * (2 - R)) := mul_pos hR hden
  rw [div_lt_div_iff₀ hden hR]
  nlinarith

/-- On the upper branch, the cubic envelope exceeds the exact rank density by a cube. -/
theorem firstOrderRankCubicEnvelope_sub_rankDensity {beta : ℝ} (hbeta : 1 / 2 ≤ beta) :
    firstOrderRankCubicEnvelope beta - firstOrderRankDensity beta =
      (beta - 1 / 2) ^ 3 / 3 := by
  by_cases heq : beta = 1 / 2
  · subst beta
    norm_num [firstOrderRankDensity, firstOrderRankCubicEnvelope]
  · rw [firstOrderRankDensity, if_neg (not_le.mpr (lt_of_le_of_ne hbeta (Ne.symm heq))),
      firstOrderRankCubicEnvelope]
    ring

theorem firstOrderRankDensity_le_cubicEnvelope (beta : ℝ) :
    firstOrderRankDensity beta ≤ firstOrderRankCubicEnvelope beta := by
  by_cases h : beta ≤ 1 / 2
  · rw [firstOrderRankDensity, if_pos h, firstOrderRankCubicEnvelope]
  · have hh : 1 / 2 ≤ beta := le_of_not_ge h
    have hcube : 0 ≤ (beta - 1 / 2) ^ 3 := pow_nonneg (sub_nonneg.mpr hh) _
    nlinarith [firstOrderRankCubicEnvelope_sub_rankDensity hh]

/-- Factoring the source-minus-envelope surplus isolates the optimized quadratic bracket. -/
theorem firstOrderSourceDensity_sub_cubicEnvelope (R a beta : ℝ) (hR : R ≠ 0) :
    firstOrderSourceDensity R a beta - firstOrderRankCubicEnvelope beta =
      beta / 2 * (a ^ 2 / R - 1 + (1 - a) * beta - (2 - R) * beta ^ 2 / 3) := by
  rw [firstOrderSourceDensity, firstOrderRankCubicEnvelope]
  field_simp
  ring

/-- Substituting the maximizing `beta` turns the bracket into the clean inequality. -/
theorem firstOrderRateBeta_bracket (R a : ℝ) (hR : R ≠ 0) (hRtwo : R ≠ 2) :
    a ^ 2 / R - 1 + (1 - a) * firstOrderRateBeta R a -
        (2 - R) * firstOrderRateBeta R a ^ 2 / 3 =
      firstOrderCleanExpression R a - 1 := by
  rw [firstOrderRateBeta, firstOrderCleanExpression]
  field_simp
  ring

private theorem firstOrderRateThreshold_radicand_pos {R : ℝ} (hR : 0 < R) (hRone : R < 1) :
    0 < R * (5 - R) * (2 - R) := by
  exact mul_pos (mul_pos hR (by linarith)) (by linarith)

/-- The displayed threshold is the positive root of the clean quadratic equation. -/
theorem firstOrderCleanExpression_threshold_eq_one {R : ℝ} (hR : 0 < R)
    (hRone : R < 1) :
    firstOrderCleanExpression R (firstOrderRateThreshold R) = 1 := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have h2R : 2 - R ≠ 0 := by nlinarith
  have h8R : 8 - R ≠ 0 := by nlinarith
  have hsquare :
      (Real.sqrt (R * (5 - R) * (2 - R))) ^ 2 = R * (5 - R) * (2 - R) :=
    Real.sq_sqrt (firstOrderRateThreshold_radicand_pos hR hRone).le
  rw [firstOrderCleanExpression, firstOrderRateThreshold]
  field_simp
  nlinarith

/-- The first-order threshold lies strictly above capacity. -/
theorem rate_lt_firstOrderRateThreshold {R : ℝ} (hR : 0 < R) (hRone : R < 1) :
    R < firstOrderRateThreshold R := by
  let s := Real.sqrt (R * (5 - R) * (2 - R))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsquare : s ^ 2 = R * (5 - R) * (2 - R) :=
    Real.sq_sqrt (firstOrderRateThreshold_radicand_pos hR hRone).le
  have hfactor :
      s ^ 2 - (R * (5 - R) / 2) ^ 2 =
        R * (5 - R) * ((1 - R) * (8 - R)) / 4 := by
    rw [hsquare]
    ring
  have hfactorpos : 0 < R * (5 - R) * ((1 - R) * (8 - R)) / 4 := by
    exact div_pos (mul_pos (mul_pos hR (by linarith))
      (mul_pos (by linarith) (by linarith))) (by norm_num)
  have hauxsq : (R * (5 - R) / 2) ^ 2 < s ^ 2 := by
    linarith
  have haux : R * (5 - R) / 2 < s := by
    have hleft : 0 ≤ R * (5 - R) / 2 := by
      apply div_nonneg <;> nlinarith
    nlinarith
  rw [firstOrderRateThreshold]
  have hden : 0 < 8 - R := by linarith
  rw [lt_div_iff₀ hden]
  dsimp only [s] at haux
  nlinarith

/-- The clean first-order threshold strictly improves the Johnson agreement `sqrt R`. -/
theorem firstOrderRateThreshold_lt_sqrt {R : ℝ} (hR : 0 < R) (hRone : R < 1) :
    firstOrderRateThreshold R < Real.sqrt R := by
  let x := Real.sqrt R
  let s := Real.sqrt (R * (5 - R) * (2 - R))
  have hx0 : 0 < x := Real.sqrt_pos.2 hR
  have hx1 : x < 1 := by
    have hxnonneg : 0 ≤ x := hx0.le
    have : x ^ 2 < 1 := by rw [show x ^ 2 = R from Real.sq_sqrt hR.le]; exact hRone
    nlinarith
  have hxsquare : x ^ 2 = R := Real.sq_sqrt hR.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsquare : s ^ 2 = R * (5 - R) * (2 - R) :=
    Real.sq_sqrt (firstOrderRateThreshold_radicand_pos hR hRone).le
  have hright : 0 < x * (8 - R) - 3 * R := by
    dsimp only [x] at hx0 hx1 hxsquare ⊢
    nlinarith [sq_nonneg (x - 1)]
  have hdiff :
      (x * (8 - R) - 3 * R) ^ 2 - (2 * s) ^ 2 =
        3 * R * (1 - x) ^ 2 * (8 - R) := by
    have htwos : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
    rw [htwos, hsquare, ← hxsquare]
    ring
  have hdiffpos : 0 < 3 * R * (1 - x) ^ 2 * (8 - R) := by
    apply mul_pos
    · apply mul_pos
      · positivity
      · exact sq_pos_of_pos (sub_pos.mpr hx1)
    · linarith
  have hsquarelt : (2 * s) ^ 2 < (x * (8 - R) - 3 * R) ^ 2 := by
    linarith
  have hroot : 2 * s < x * (8 - R) - 3 * R := by nlinarith
  rw [firstOrderRateThreshold]
  have hden : 0 < 8 - R := by linarith
  rw [div_lt_iff₀ hden]
  dsimp only [x, s] at hroot ⊢
  nlinarith

/-- Above the displayed root, the clean scalar inequality is strict. -/
theorem firstOrderCleanExpression_gt_one {R a : ℝ} (hR : 0 < R) (hRone : R < 1)
    (ha : firstOrderRateThreshold R < a) :
    1 < firstOrderCleanExpression R a := by
  let b := firstOrderRateThreshold R
  have hbR : R < b := rate_lt_firstOrderRateThreshold hR hRone
  have hbase : firstOrderCleanExpression R b = 1 :=
    firstOrderCleanExpression_threshold_eq_one hR hRone
  have hdenR : 0 < R := hR
  have hden2 : 0 < 4 * (2 - R) := mul_pos (by norm_num) (by linarith)
  rw [firstOrderCleanExpression] at hbase ⊢
  have hcoef : 0 < (a + b) / R + 3 * (a + b - 2) / (4 * (2 - R)) := by
    let c := (a + b) / R + 3 * (a + b - 2) / (4 * (2 - R))
    let q := R * (4 * (2 - R))
    have hq : 0 < q := mul_pos hR hden2
    have heq : c * q =
        (a + b) * (4 * (2 - R)) + 3 * (a + b - 2) * R := by
      dsimp only [c, q]
      field_simp [ne_of_gt hR, ne_of_gt (show 0 < 2 - R by linarith)]
    have hrhs : 0 < (a + b) * (4 * (2 - R)) + 3 * (a + b - 2) * R := by
      nlinarith [mul_pos (sub_pos.mpr hRone)
        (sub_pos.mpr (show R < 8 by linarith))]
    have hcq : 0 < c * q := heq.symm ▸ hrhs
    exact (mul_pos_iff_of_pos_right hq).mp hcq
  have hid :
      (a ^ 2 / R + 3 * (1 - a) ^ 2 / (4 * (2 - R))) -
          (b ^ 2 / R + 3 * (1 - b) ^ 2 / (4 * (2 - R))) =
        (a - b) * ((a + b) / R + 3 * (a + b - 2) / (4 * (2 - R))) := by
    field_simp
    ring
  nlinarith

/-- The optimized source density strictly exceeds the exact rank density above the curve. -/
theorem firstOrderRate_surplus_pos {R a : ℝ} (hR : 0 < R) (hRa : R < a)
    (haone : a < 1) (hthreshold : firstOrderRateThreshold R < a) :
    firstOrderRankDensity (firstOrderRateBeta R a) <
      firstOrderSourceDensity R a (firstOrderRateBeta R a) := by
  have hRone : R < 1 := hRa.trans haone
  have hbeta : 0 < firstOrderRateBeta R a := firstOrderRateBeta_pos haone hRone
  have henv := firstOrderRankDensity_le_cubicEnvelope (firstOrderRateBeta R a)
  have hclean := firstOrderCleanExpression_gt_one hR hRone hthreshold
  have hbracket := firstOrderRateBeta_bracket R a (ne_of_gt hR) (by linarith)
  have hfactor := firstOrderSourceDensity_sub_cubicEnvelope
    R a (firstOrderRateBeta R a) (ne_of_gt hR)
  nlinarith

end

end ReedSolomon.HiddenDerivative
