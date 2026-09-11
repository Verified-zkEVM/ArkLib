/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.LowRateStationary

/-!
# Branchwise first-order rate parameters

This module joins the stationary low-rate optimizer to the existing clean upper branch.  The
agreement threshold depends only on the source-rate bound.  The derivative-degree ratio is
stationary on the low branch and is tuned to the certified agreement on the upper branch.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- The full piecewise first-order agreement threshold from the rate calculation. -/
def firstOrderBranchThreshold (rho : ℝ) : ℝ :=
  if rho < firstOrderRateSwitch then firstOrderLowRateThreshold rho
  else firstOrderRateThreshold rho

/-- The piecewise derivative-degree ratio at a certified agreement `a`. -/
def firstOrderBranchBeta (rho a : ℝ) : ℝ :=
  if rho < firstOrderRateSwitch then firstOrderLowRateBeta rho
  else firstOrderRateBeta rho a

theorem firstOrderBranchThreshold_eq_low {rho : ℝ} (hlow : rho < firstOrderRateSwitch) :
    firstOrderBranchThreshold rho = firstOrderLowRateThreshold rho := by
  rw [firstOrderBranchThreshold, if_pos hlow]

theorem firstOrderBranchThreshold_eq_clean {rho : ℝ} (hlow : firstOrderRateSwitch ≤ rho) :
    firstOrderBranchThreshold rho = firstOrderRateThreshold rho := by
  rw [firstOrderBranchThreshold, if_neg (not_lt.mpr hlow)]

theorem firstOrderBranchBeta_eq_low {rho a : ℝ} (hlow : rho < firstOrderRateSwitch) :
    firstOrderBranchBeta rho a = firstOrderLowRateBeta rho := by
  rw [firstOrderBranchBeta, if_pos hlow]

theorem firstOrderBranchBeta_eq_clean {rho a : ℝ} (hlow : firstOrderRateSwitch ≤ rho) :
    firstOrderBranchBeta rho a = firstOrderRateBeta rho a := by
  rw [firstOrderBranchBeta, if_neg (not_lt.mpr hlow)]

/-- Both branches select a strictly positive derivative-degree ratio above their threshold. -/
theorem firstOrderBranchBeta_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (_ha : firstOrderBranchThreshold rho < a) (haOne : a < 1) :
    0 < firstOrderBranchBeta rho a := by
  by_cases hlow : rho < firstOrderRateSwitch
  · rw [firstOrderBranchBeta_eq_low hlow]
    exact firstOrderLowRateBeta_pos hrho
  · rw [firstOrderBranchBeta_eq_clean (not_lt.mp hlow)]
    exact firstOrderRateBeta_pos haOne hrhoOne

/-- The selected derivative cap lies strictly inside the coefficient cutoff `a/rho`. -/
theorem firstOrderBranchBeta_lt_agreement_div_rate {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderBranchThreshold rho < a) (haOne : a < 1) :
    firstOrderBranchBeta rho a < a / rho := by
  by_cases hlow : rho < firstOrderRateSwitch
  · rw [firstOrderBranchBeta_eq_low hlow]
    have hthreshold : firstOrderLowRateThreshold rho < a := by
      simpa [firstOrderBranchThreshold_eq_low hlow] using ha
    exact (firstOrderLowRateBeta_lt_threshold_div_rate hrho).trans
      (div_lt_div_of_pos_right hthreshold hrho)
  · have hthreshold : firstOrderRateThreshold rho < a := by
      simpa [firstOrderBranchThreshold_eq_clean (not_lt.mp hlow)] using ha
    have hRa : rho < a := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans hthreshold
    rw [firstOrderBranchBeta_eq_clean (not_lt.mp hlow)]
    exact firstOrderRateBeta_lt_agreement_div_rate hrho hRa haOne

/-- Above the full piecewise curve, the exact limiting coefficient-minus-rank margin is positive. -/
theorem firstOrderBranch_surplus_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : firstOrderBranchThreshold rho < a) (haOne : a < 1) :
    firstOrderRankDensity (firstOrderBranchBeta rho a) <
      firstOrderSourceDensity rho a (firstOrderBranchBeta rho a) := by
  by_cases hlow : rho < firstOrderRateSwitch
  · have hregime : FirstOrderLowRateRegime rho :=
      (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
    have hthreshold : firstOrderLowRateThreshold rho < a := by
      simpa [firstOrderBranchThreshold_eq_low hlow] using ha
    rw [firstOrderBranchBeta_eq_low hlow]
    exact sub_pos.mp (firstOrderLowRate_margin_pos hrho hregime hthreshold)
  · have hthreshold : firstOrderRateThreshold rho < a := by
      simpa [firstOrderBranchThreshold_eq_clean (not_lt.mp hlow)] using ha
    have hRa : rho < a := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans hthreshold
    rw [firstOrderBranchBeta_eq_clean (not_lt.mp hlow)]
    exact firstOrderRate_surplus_pos hrho hRa haOne hthreshold

end

end ReedSolomon.HiddenDerivative
