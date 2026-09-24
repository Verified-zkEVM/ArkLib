/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The first-order rate threshold

This file proves the real-variable calculation behind the first-order interpolation recipe. For a
code rate `R` and an agreement fraction `a`, the capped first-order support is tuned with the
derivative-degree ratio

```text
β = 3(1 - a) / (2(2 - R)).
```

In the limit of large length, the support has normalized source count
`S(β) = β a²/(2R) - a β²/2 + R β³/6` and local rank at most the cubic envelope
`E(β) = β/2 - β²/2 + β³/3`. The choice of `β` maximizes the bracket in
`S(β) - E(β) = (β/2)(a²/R - 1 + (1 - a)β - (2 - R)β²/3)`, and at that `β` the bracket equals
`Q(R, a) - 1` with `Q(R, a) = a²/R + 3(1 - a)²/(4(2 - R))`. The positive root of `Q(R, a) = 1` is

```text
a₁(R) = (3R + 2√(R(5 - R)(2 - R))) / (8 - R),
```

and for `0 < R < 1` it satisfies `R < a₁(R) < √R`. Hence source density exceeds rank density
whenever `a₁(R) < a < 1`. The curve `a₁` is sufficient for this support family; it is not claimed
optimal, since the cubic envelope discards part of the exact piecewise rank density.

## Main statements

* `firstOrderRankDensity_le_cubicEnvelope`: the exact rank density is below the cubic envelope.
* `firstOrderSourceDensity_sub_cubicEnvelope`, `firstOrderRateBeta_bracket`: the factorization
  of `S - E` and the value of its bracket at the chosen `β`.
* `firstOrderCleanExpression_threshold_eq_one`: `Q(R, a₁(R)) = 1`.
* `rate_lt_firstOrderRateThreshold`, `firstOrderRateThreshold_lt_sqrt`: `R < a₁(R) < √R`.
* `firstOrderCleanExpression_gt_one`: `1 < Q(R, a)` for `a > a₁(R)`.
* `firstOrderRate_surplus_pos`: the exact rank density is strictly below the source density at
  the chosen `β`, for `a₁(R) < a < 1`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The first-order agreement threshold `a₁(R) = (3R + 2√(R(5 - R)(2 - R))) / (8 - R)`, the
positive root of `firstOrderCleanExpression R a = 1` for `0 < R < 2`. -/
def firstOrderRateThreshold (R : ℝ) : ℝ :=
  (3 * R + 2 * Real.sqrt (R * (5 - R) * (2 - R))) / (8 - R)

/-- The derivative-degree ratio `β = 3(1 - a) / (2(2 - R))`, which maximizes the bracket in
`firstOrderSourceDensity_sub_cubicEnvelope`. -/
def firstOrderRateBeta (R a : ℝ) : ℝ :=
  3 * (1 - a) / (2 * (2 - R))

/-- The limiting normalized source count `β a²/(2R) - a β²/2 + R β³/6` of the capped first-order
support at rate `R`, agreement `a` and derivative-degree ratio `β`. -/
def firstOrderSourceDensity (R a beta : ℝ) : ℝ :=
  beta * a ^ 2 / (2 * R) - a * beta ^ 2 / 2 + R * beta ^ 3 / 6

/-- The exact limiting local-rank density, `β/2 - β²/2 + β³/3` for `β ≤ 1/2` and `β/4 + 1/24`
beyond. The construction only uses `β < 3/4`. -/
def firstOrderRankDensity (beta : ℝ) : ℝ :=
  if beta ≤ 1 / 2 then beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3
  else beta / 4 + 1 / 24

/-- The cubic `β/2 - β²/2 + β³/3`, which agrees with `firstOrderRankDensity` for `β ≤ 1/2` and
bounds it above everywhere. -/
def firstOrderRankCubicEnvelope (beta : ℝ) : ℝ :=
  beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3

/-- The scalar expression `Q(R, a) = a²/R + 3(1 - a)²/(4(2 - R))`. When the chosen `β` is
positive, source density exceeds the cubic envelope at it exactly when `Q(R, a) > 1`. -/
def firstOrderCleanExpression (R a : ℝ) : ℝ :=
  a ^ 2 / R + 3 * (1 - a) ^ 2 / (4 * (2 - R))

/-- `β > 0` for `a < 1` and `R < 2`. At `a = 1` the ratio is `0`. -/
theorem firstOrderRateBeta_pos {R a : ℝ} (ha : a < 1) (hR : R < 2) :
    0 < firstOrderRateBeta R a := by
  rw [firstOrderRateBeta]
  apply div_pos
  · linarith
  · linarith

/-- `β < 3/4` for `R < 2` and `R < 2a`; the second condition is equivalent to the bound once the
denominator is positive. In particular it holds for `0 < R < a`. -/
theorem firstOrderRateBeta_lt_three_four {R a : ℝ} (hR : R < 2) (hRa : R < 2 * a) :
    firstOrderRateBeta R a < 3 / 4 := by
  rw [firstOrderRateBeta]
  have hden : 0 < 2 * (2 - R) := by linarith
  rw [div_lt_iff₀ hden]
  linarith

/-- `β < a / R` for `0 < R < 2` and `R ≤ a`. The exact condition is `3R < a(4 + R)`, which
`R ≤ a` implies because `R(4 + R) > 3R`. This keeps the support below the degree cap. -/
theorem firstOrderRateBeta_lt_agreement_div_rate {R a : ℝ}
    (hR : 0 < R) (hRtwo : R < 2) (hRa : R ≤ a) :
    firstOrderRateBeta R a < a / R := by
  rw [firstOrderRateBeta]
  have hden : 0 < 2 * (2 - R) := by linarith
  rw [div_lt_div_iff₀ hden hR]
  nlinarith

/-- For `β ≥ 1/2`, the cubic envelope exceeds the exact rank density by `(β - 1/2)³/3`. -/
theorem firstOrderRankCubicEnvelope_sub_rankDensity {beta : ℝ} (hbeta : 1 / 2 ≤ beta) :
    firstOrderRankCubicEnvelope beta - firstOrderRankDensity beta =
      (beta - 1 / 2) ^ 3 / 3 := by
  unfold firstOrderRankDensity firstOrderRankCubicEnvelope
  split_ifs with h
  · obtain rfl : beta = 1 / 2 := le_antisymm h hbeta
    norm_num
  · ring

/-- The exact rank density is at most the cubic envelope, with equality for `β ≤ 1/2`. -/
theorem firstOrderRankDensity_le_cubicEnvelope (beta : ℝ) :
    firstOrderRankDensity beta ≤ firstOrderRankCubicEnvelope beta := by
  by_cases h : beta ≤ 1 / 2
  · unfold firstOrderRankDensity firstOrderRankCubicEnvelope
    simp only [h, ite_true, le_refl]
  · have hh : 1 / 2 ≤ beta := le_of_not_ge h
    have hcube : 0 ≤ (beta - 1 / 2) ^ 3 := pow_nonneg (sub_nonneg.mpr hh) _
    nlinarith [firstOrderRankCubicEnvelope_sub_rankDensity hh]

/-- The factorization
`S(β) - E(β) = (β/2)(a²/R - 1 + (1 - a)β - (2 - R)β²/3)` for `R ≠ 0`. The bracket is a concave
quadratic in `β` for `R < 2`, maximized at `firstOrderRateBeta R a`. -/
theorem firstOrderSourceDensity_sub_cubicEnvelope (R a beta : ℝ) (hR : R ≠ 0) :
    firstOrderSourceDensity R a beta - firstOrderRankCubicEnvelope beta =
      beta / 2 * (a ^ 2 / R - 1 + (1 - a) * beta - (2 - R) * beta ^ 2 / 3) := by
  rw [firstOrderSourceDensity, firstOrderRankCubicEnvelope]
  field_simp
  ring

/-- At `β = firstOrderRateBeta R a` the bracket of `firstOrderSourceDensity_sub_cubicEnvelope`
equals `Q(R, a) - 1`. The hypotheses `R ≠ 0` and `R ≠ 2` keep both denominators nonzero. -/
theorem firstOrderRateBeta_bracket (R a : ℝ) (hR : R ≠ 0) (hRtwo : R ≠ 2) :
    a ^ 2 / R - 1 + (1 - a) * firstOrderRateBeta R a -
        (2 - R) * firstOrderRateBeta R a ^ 2 / 3 =
      firstOrderCleanExpression R a - 1 := by
  have h2R : (2 : ℝ) - R ≠ 0 := sub_ne_zero.mpr (Ne.symm hRtwo)
  rw [firstOrderRateBeta, firstOrderCleanExpression]
  field_simp
  ring

/-- The radicand `R(5 - R)(2 - R)` of `firstOrderRateThreshold` is positive for `0 < R < 2`. -/
theorem firstOrderRateThreshold_radicand_pos {R : ℝ} (hR : 0 < R) (hRtwo : R < 2) :
    0 < R * (5 - R) * (2 - R) :=
  mul_pos (mul_pos hR (by linarith)) (by linarith)

/-- `Q(R, a₁(R)) = 1` for `0 < R < 2`: the threshold is a root of the clean quadratic
equation. On this range the square root is of a positive number and `8 - R ≠ 0`. -/
theorem firstOrderCleanExpression_threshold_eq_one {R : ℝ} (hR : 0 < R)
    (hRtwo : R < 2) :
    firstOrderCleanExpression R (firstOrderRateThreshold R) = 1 := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have h2R : 2 - R ≠ 0 := by linarith
  have h8R : 8 - R ≠ 0 := by linarith
  have hsquare :
      (Real.sqrt (R * (5 - R) * (2 - R))) ^ 2 = R * (5 - R) * (2 - R) :=
    Real.sq_sqrt (firstOrderRateThreshold_radicand_pos hR hRtwo).le
  rw [firstOrderCleanExpression, firstOrderRateThreshold]
  field_simp
  nlinarith

/-- `R < a₁(R)` for `0 < R < 1`: the threshold is strictly above capacity. At `R = 1` both
sides equal `1`. -/
theorem rate_lt_firstOrderRateThreshold {R : ℝ} (hR : 0 < R) (hRone : R < 1) :
    R < firstOrderRateThreshold R := by
  let s := Real.sqrt (R * (5 - R) * (2 - R))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsquare : s ^ 2 = R * (5 - R) * (2 - R) :=
    Real.sq_sqrt (firstOrderRateThreshold_radicand_pos hR (by linarith)).le
  have hfactor :
      s ^ 2 - (R * (5 - R) / 2) ^ 2 =
        R * (5 - R) * ((1 - R) * (8 - R)) / 4 := by
    rw [hsquare]
    ring
  have hfactorpos : 0 < R * (5 - R) * ((1 - R) * (8 - R)) / 4 := by
    have h5R : 0 < 5 - R := by linarith
    have h1R : 0 < 1 - R := by linarith
    have h8R : 0 < 8 - R := by linarith
    exact div_pos (mul_pos (mul_pos hR h5R) (mul_pos h1R h8R)) (by norm_num)
  have hauxsq : (R * (5 - R) / 2) ^ 2 < s ^ 2 := by
    linarith
  have haux : R * (5 - R) / 2 < s := by
    have hleft : 0 ≤ R * (5 - R) / 2 := by
      apply div_nonneg
      · exact mul_nonneg hR.le (by linarith)
      · norm_num
    exact (sq_lt_sq₀ hleft hs0).mp hauxsq
  rw [firstOrderRateThreshold]
  have hden : 0 < 8 - R := by linarith
  rw [lt_div_iff₀ hden]
  have hscaled : R * (5 - R) < 2 * s := by
    calc
      R * (5 - R) = 2 * (R * (5 - R) / 2) := by ring
      _ < 2 * s := mul_lt_mul_of_pos_left haux (by norm_num)
  dsimp only [s] at hscaled ⊢
  ring_nf at hscaled ⊢
  linarith

/-- `a₁(R) < √R` for `0 < R < 1`: the first-order threshold strictly improves the Johnson
agreement. At `R = 1` both sides equal `1`. -/
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
    Real.sq_sqrt (firstOrderRateThreshold_radicand_pos hR (by linarith)).le
  have hright : 0 < x * (8 - R) - 3 * R := by
    rw [← hxsquare]
    have hfactor : x * (8 - x ^ 2) - 3 * x ^ 2 =
        x * (1 - x) * (x + 4) + 4 * x := by ring
    rw [hfactor]
    positivity
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
  have hroot : 2 * s < x * (8 - R) - 3 * R :=
    (sq_lt_sq₀ (by positivity) hright.le).mp hsquarelt
  rw [firstOrderRateThreshold]
  have hden : 0 < 8 - R := by linarith
  rw [div_lt_iff₀ hden]
  dsimp only [x, s] at hroot ⊢
  linarith

/-- `1 < Q(R, a)` for `0 < R < 1` and `a > a₁(R)`. The proof writes
`Q(R, a) - Q(R, a₁) = (a - a₁)((a + a₁)/R + 3(a + a₁ - 2)/(4(2 - R)))` and shows the second
factor is positive using `a₁ > R`. -/
theorem firstOrderCleanExpression_gt_one {R a : ℝ} (hR : 0 < R) (hRone : R < 1)
    (ha : firstOrderRateThreshold R < a) :
    1 < firstOrderCleanExpression R a := by
  let b := firstOrderRateThreshold R
  have hbR : R < b := rate_lt_firstOrderRateThreshold hR hRone
  have hbase : firstOrderCleanExpression R b = 1 :=
    firstOrderCleanExpression_threshold_eq_one hR (by linarith)
  have hden2 : 0 < 4 * (2 - R) := mul_pos (by norm_num) (by linarith)
  rw [firstOrderCleanExpression] at hbase ⊢
  have hcoef : 0 < (a + b) / R + 3 * (a + b - 2) / (4 * (2 - R)) := by
    let c := (a + b) / R + 3 * (a + b - 2) / (4 * (2 - R))
    let q := R * (4 * (2 - R))
    have hq : 0 < q := mul_pos hR hden2
    have heq : c * q = (a + b) * (8 - R) - 6 * R := by
      dsimp only [c, q]
      field_simp [ne_of_gt hR, ne_of_gt (show 0 < 2 - R by linarith)]
      ring
    have hsum : 2 * R < a + b := by linarith [hbR, ha]
    have h8R : 0 < 8 - R := by linarith
    have h5R : 0 < 5 - R := by linarith
    have hrhs : 0 < (a + b) * (8 - R) - 6 * R := by
      calc
        0 < 2 * R * (5 - R) := mul_pos (mul_pos (by norm_num) hR) h5R
        _ = 2 * R * (8 - R) - 6 * R := by ring
        _ < (a + b) * (8 - R) - 6 * R :=
          sub_lt_sub_right (mul_lt_mul_of_pos_right hsum h8R) _
    have hcq : 0 < c * q := heq.symm ▸ hrhs
    exact (mul_pos_iff_of_pos_right hq).mp hcq
  have hid :
      (a ^ 2 / R + 3 * (1 - a) ^ 2 / (4 * (2 - R))) -
          (b ^ 2 / R + 3 * (1 - b) ^ 2 / (4 * (2 - R))) =
        (a - b) * ((a + b) / R + 3 * (a + b - 2) / (4 * (2 - R))) := by
    field_simp
    ring
  have hdiffpos :
      0 < (a - b) * ((a + b) / R + 3 * (a + b - 2) / (4 * (2 - R))) :=
    mul_pos (sub_pos.mpr ha) hcoef
  rw [← hid] at hdiffpos
  calc
    1 = b ^ 2 / R + 3 * (1 - b) ^ 2 / (4 * (2 - R)) := hbase.symm
    _ < a ^ 2 / R + 3 * (1 - a) ^ 2 / (4 * (2 - R)) := sub_pos.mp hdiffpos

/-- For `0 < R < a < 1` with `a₁(R) < a`, the exact rank density at the chosen `β` is strictly
below the source density. The strict inequality comes from `1 < Q(R, a)` and `β > 0`; at `a = 1`
the ratio `β` is `0` and both densities vanish. The hypothesis `R < a` is used only to get
`R < 1`. -/
theorem firstOrderRate_surplus_pos {R a : ℝ} (hR : 0 < R) (hRa : R < a)
    (haone : a < 1) (hthreshold : firstOrderRateThreshold R < a) :
    firstOrderRankDensity (firstOrderRateBeta R a) <
      firstOrderSourceDensity R a (firstOrderRateBeta R a) := by
  have hRone : R < 1 := hRa.trans haone
  have hbeta : 0 < firstOrderRateBeta R a := firstOrderRateBeta_pos haone (by linarith)
  have henv := firstOrderRankDensity_le_cubicEnvelope (firstOrderRateBeta R a)
  have hclean := firstOrderCleanExpression_gt_one hR hRone hthreshold
  have hbracket := firstOrderRateBeta_bracket R a (ne_of_gt hR) (by linarith)
  have hfactor := firstOrderSourceDensity_sub_cubicEnvelope
    R a (firstOrderRateBeta R a) (ne_of_gt hR)
  nlinarith

end

end ReedSolomon.HiddenDerivative
