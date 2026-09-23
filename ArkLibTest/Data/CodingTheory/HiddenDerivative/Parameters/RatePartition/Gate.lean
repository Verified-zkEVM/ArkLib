/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Gate

/-!
# Rate-partition gate acceptance tests

Concrete values of `rateGamma` and `fixedRateCoefficient`, cases showing that the kept
hypotheses are needed, and the forms with the stronger hypotheses `0 < R`, `0 < δ` and `R < 1`
derived from the stated theorems.
-/

namespace ReedSolomon.HiddenDerivative.RatePartition

/-! ### Concrete values -/

/-- `Γ(1, 1, 1) = (27/20) · 2 / 6 = 9/20`. -/
private theorem test_rateGamma_one : rateGamma 1 1 1 = 9 / 20 := by
  norm_num [rateGamma]

/-- `c(40/9) = (40/9) log 1 = 0`. -/
private theorem test_fixedRateCoefficient_boundary : fixedRateCoefficient (40 / 9) = 0 := by
  norm_num [fixedRateCoefficient]

/-- The logarithm identity at `R = 1`, `a = 1`, `d = 1` agrees with `log(9/20)`. -/
example : Real.log (27 * 1 / 20) + Real.log ((1 : ℕ) + 1 : ℝ) -
    1 / 1 * Real.log (6 * ((1 : ℕ) : ℝ)) = Real.log (9 / 20) := by
  rw [← log_rateGamma one_ne_zero one_pos, test_rateGamma_one]

/-- The logarithmic identity in the form with separate `log 6` and `log d` terms. -/
example {rate agreement : ℝ} {order : ℕ} (hrate : 0 < rate) (horder : 0 < order) :
    Real.log (rateGamma rate agreement order) =
      Real.log ((27 / 20 : ℝ) * rate) + Real.log ((order : ℝ) + 1) -
        rate / agreement * (Real.log 6 + Real.log order) := by
  rw [log_rateGamma hrate.ne' horder]
  have hcoefficient : (27 * rate / 20 : ℝ) = (27 / 20 : ℝ) * rate := by ring
  rw [hcoefficient]
  have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
  rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) horderReal.ne']

/-- The fixed-rate coefficient with the factor written as `(27/20) * rate`. -/
example {rate : ℝ} (hrate : 0 < rate) :
    fixedRateCoefficient rate =
      rate * (Real.log 6 - Real.log ((27 / 20 : ℝ) * rate)) := by
  rw [fixedRateCoefficient_eq hrate]
  have hcoefficient : (27 * rate / 20 : ℝ) = (27 / 20 : ℝ) * rate := by ring
  rw [hcoefficient]

/-! ### The kept hypotheses are needed -/

/-- `rateGamma_pos` needs `0 < d`: `Γ(1, 1, 0) = 0`. -/
example : rateGamma 1 1 0 = 0 := by
  norm_num [rateGamma]

/-- `rateGamma_pos` needs `0 < R`: `Γ(-1, 1, 1) = -81/5`. -/
example : rateGamma (-1) 1 1 = -81 / 5 := by
  norm_num [rateGamma, Real.rpow_neg_one]

/-- `fixedRateCoefficient_pos` needs `R < 40/9`: the coefficient is `0` there. -/
example : ¬ 0 < fixedRateCoefficient (40 / 9) := by
  rw [test_fixedRateCoefficient_boundary]
  exact lt_irrefl 0

/-- `fixed_rate_log_identity` needs `R + δ ≠ 0`: at `R = 1`, `δ = -1`, `d = 1` the left side is
`0` and the right side is `-log 6`. -/
example : ¬ ((1 + -1 : ℝ) * Real.log (rateGamma 1 (1 + -1) 1) =
    -1 * Real.log ((1 : ℕ) : ℝ) - fixedRateCoefficient 1 + -1 * Real.log (27 * 1 / 20) +
      (1 + -1) * Real.log (1 + 1 / ((1 : ℕ) : ℝ))) := by
  have h6 := complementary_rate_logs (rate := 1) one_ne_zero
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  simp only [fixedRateCoefficient] at *
  norm_num at h6 ⊢
  intro h
  linarith

/-- `exists_small_gap_rate_gate` needs `R < 1`: at `R = 1` no positive gap gives `R + δ < 1`. -/
example : ¬ ∃ gapBound : ℝ, 0 < gapBound ∧ ∀ gap : ℝ, 0 < gap → gap < gapBound →
    (1 : ℝ) + gap < 1 := by
  rintro ⟨gapBound, hpos, h⟩
  have := h (gapBound / 2) (by positivity) (by linarith)
  linarith

/-! ### Forms with stronger hypotheses -/

/-- `log_rateGamma` under `0 < R`. -/
example {rate agreement : ℝ} {order : ℕ} (hrate : 0 < rate) (horder : 0 < order) :
    Real.log (rateGamma rate agreement order) = Real.log (27 * rate / 20) +
      Real.log ((order : ℝ) + 1) - rate / agreement * Real.log (6 * (order : ℝ)) :=
  log_rateGamma hrate.ne' horder

/-- `complementary_rate_logs` under `0 < R`. -/
example {rate : ℝ} (hrate : 0 < rate) :
    Real.log (40 / (9 * rate)) + Real.log (27 * rate / 20) = Real.log 6 :=
  complementary_rate_logs hrate.ne'

/-- `fixed_rate_log_identity` under `0 < R` and `0 < δ`. -/
example {rate gap : ℝ} {order : ℕ} (hrate : 0 < rate) (hgap : 0 < gap) (horder : 0 < order) :
    (rate + gap) * Real.log (rateGamma rate (rate + gap) order) =
      gap * Real.log order - fixedRateCoefficient rate + gap * Real.log (27 * rate / 20) +
        (rate + gap) * Real.log (1 + 1 / (order : ℝ)) :=
  fixed_rate_log_identity hrate.ne' (add_pos hrate hgap).ne' horder

/-- `fixedRateCoefficient_pos` for a code rate `R < 1`. -/
example {rate : ℝ} (hrate : 0 < rate) (hrateOne : rate < 1) :
    0 < fixedRateCoefficient rate :=
  fixedRateCoefficient_pos hrate (by linarith)

/-- The gate at rate `1/2` and `ε = 1`. -/
example : ∃ gapBound : ℝ, 0 < gapBound ∧ ∀ gap : ℝ, 0 < gap → gap < gapBound →
    let order := ⌈Real.exp ((fixedRateCoefficient (1 / 2) + 1) / gap)⌉₊
    (1 / 2 : ℝ) + gap < 1 ∧ 500 ≤ order ∧ 1 < rateGamma (1 / 2) (1 / 2 + gap) order :=
  exists_small_gap_rate_gate (by norm_num) (by norm_num) one_pos

/-! ### A strict gate from an exponent margin -/

/-- At rate `1`, gap `1` and order `5`, the fixed-rate exponent margin gives `rateGamma > 1`. -/
example : 1 < rateGamma 1 2 5 := by
  have hcoef : fixedRateCoefficient 1 ≤ Real.log 5 := by
    rw [fixedRateCoefficient]
    norm_num only [one_mul, mul_one, mul_zero, add_zero]
    apply Real.log_le_log <;> norm_num
  have horder : fixedRateCoefficient 1 + 0 ≤ 1 * Real.log (5 : ℝ) := by
    nlinarith [hcoef]
  have hmargin : 0 < 0 + 1 * Real.log (27 * 1 / 20) := by
    norm_num only [zero_add, one_mul]
    exact Real.log_pos (by norm_num)
  have h := rateGamma_gt_one_of_exponent_margin (rate := 1) (gap := 1) (epsilon := 0)
    (order := 5) (by norm_num) (by norm_num) (by norm_num) horder hmargin
  have hsum : (1 : ℝ) + 1 = 2 := by norm_num
  rw [← hsum]
  exact h

end ReedSolomon.HiddenDerivative.RatePartition
