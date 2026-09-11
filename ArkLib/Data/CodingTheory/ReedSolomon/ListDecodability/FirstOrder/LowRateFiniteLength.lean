/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.BranchwiseRate
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthSelectors

/-!
# Finite-length parameters on the stationary low-rate branch

The derivative-degree ratio is fixed at the stationary optimizer for `rho`, while the source
density is evaluated at `rho - 1/n`.  This file proves the exact analytic finite-slack margin
needed before integer rounding.  The literal selectors retain the manuscript's floors and
ceilings, including the `M = 0` endpoint.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder

open ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- The low-rate agreement clipped halfway between the curve and one. -/
def lowRateFiniteLengthCertifiedAgreement (rho eta : ℝ) : ℝ :=
  min (firstOrderLowRateThreshold rho + eta) ((1 + firstOrderLowRateThreshold rho) / 2)

/-- The exact low-rate density margin at the saved rate `rho - 1/n`. -/
def lowRateFiniteLengthDensityMargin (rho eta : ℝ) (n : ℕ) : ℝ :=
  firstOrderSourceDensity (finiteLengthRate rho n)
      (lowRateFiniteLengthCertifiedAgreement rho eta) (firstOrderLowRateBeta rho) -
    firstOrderRankDensity (firstOrderLowRateBeta rho)

/-- Fixed-rate slope supplied by the stationary-margin factorization. -/
def lowRateEtaSlope (rho : ℝ) : ℝ :=
  firstOrderLowRateBeta rho / 4 *
    (2 * firstOrderLowRateThreshold rho / rho - firstOrderLowRateBeta rho)

/-- Rate-saving slope supplied by evaluating the source density at `rho - 1/n`. -/
def lowRateInverseLengthSlope (rho : ℝ) : ℝ :=
  firstOrderLowRateBeta rho * firstOrderLowRateThreshold rho ^ 2 / (3 * rho ^ 2)

/-- One positive rate-only slope controlling both pieces of `eta + 1/n`. -/
def lowRateFiniteLengthSlope (rho : ℝ) : ℝ :=
  min (lowRateEtaSlope rho) (lowRateInverseLengthSlope rho)

theorem lowRateFiniteLengthCertifiedAgreement_ge_half_slack
    {rho eta : ℝ} (heta : 0 ≤ eta)
    (haOne : firstOrderLowRateThreshold rho + eta ≤ 1) :
    firstOrderLowRateThreshold rho + eta / 2 ≤
      lowRateFiniteLengthCertifiedAgreement rho eta := by
  rw [lowRateFiniteLengthCertifiedAgreement]
  apply le_min
  · linarith
  · linarith

theorem lowRateFiniteLengthCertifiedAgreement_lt_one
    {rho eta : ℝ} (haOne : firstOrderLowRateThreshold rho + eta < 1) :
    lowRateFiniteLengthCertifiedAgreement rho eta < 1 := by
  unfold lowRateFiniteLengthCertifiedAgreement
  exact (min_le_left _ _).trans_lt haOne

theorem lowRateFiniteLengthCertifiedAgreement_pos
    {rho eta : ℝ} (hrho : 0 < rho) (heta : 0 ≤ eta) :
    0 < lowRateFiniteLengthCertifiedAgreement rho eta := by
  have hthreshold : 0 < firstOrderLowRateThreshold rho := by
    unfold firstOrderLowRateThreshold
    exact add_pos (firstOrderLowRateScale_pos hrho)
      (mul_pos hrho (firstOrderLowRateBeta_pos hrho))
  unfold lowRateFiniteLengthCertifiedAgreement
  exact lt_min (by linarith) (by linarith)

theorem lowRateFiniteLengthSlope_pos {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch) :
    0 < lowRateFiniteLengthSlope rho := by
  have hregime : FirstOrderLowRateRegime rho :=
    (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
  have hbeta := firstOrderLowRateBeta_pos hrho
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime
  have hcut := firstOrderLowRateBeta_lt_threshold_div_rate hrho
  unfold lowRateFiniteLengthSlope lowRateEtaSlope lowRateInverseLengthSlope
  apply lt_min
  · have : 0 < 2 * firstOrderLowRateThreshold rho / rho -
        firstOrderLowRateBeta rho := by
      have : firstOrderLowRateBeta rho <
          2 * firstOrderLowRateThreshold rho / rho := by
        calc
          firstOrderLowRateBeta rho < firstOrderLowRateThreshold rho / rho := hcut
          _ < 2 * firstOrderLowRateThreshold rho / rho := by
            exact div_lt_div_of_pos_right (by linarith) hrho
      linarith
    positivity
  · exact div_pos (mul_pos hbeta (sq_pos_of_pos (hrho.trans hthreshold)))
      (mul_pos (by norm_num) (sq_pos_of_pos hrho))

/-- The fixed-rate low-branch margin is at least linear in the clipped agreement slack. -/
theorem lowRateEtaSlope_mul_eta_le_fixed_margin
    {rho eta : ℝ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1) :
    lowRateEtaSlope rho * eta ≤
      firstOrderSourceDensity rho (lowRateFiniteLengthCertifiedAgreement rho eta)
          (firstOrderLowRateBeta rho) - firstOrderRankDensity (firstOrderLowRateBeta rho) := by
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let T := firstOrderLowRateThreshold rho
  let beta := firstOrderLowRateBeta rho
  have hregime : FirstOrderLowRateRegime rho :=
    (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
  have haLower : T + eta / 2 ≤ a := by
    dsimp only [T, a]
    exact lowRateFiniteLengthCertifiedAgreement_ge_half_slack heta.le haOne.le
  have hbeta : 0 < beta := by
    dsimp only [beta]
    exact firstOrderLowRateBeta_pos hrho
  have hcut : beta < T / rho := by
    dsimp only [beta, T]
    exact firstOrderLowRateBeta_lt_threshold_div_rate hrho
  have hbracket : 2 * T / rho - beta ≤ (a + T) / rho - beta := by
    have hTa : T ≤ a := by linarith
    have := div_le_div_of_nonneg_right (add_le_add_right hTa T) hrho.le
    simpa only [two_mul, add_comm] using sub_le_sub_right this beta
  have hbracketPos : 0 < 2 * T / rho - beta := by
    have hTpos : 0 < T := by
      dsimp only [T, firstOrderLowRateThreshold]
      exact add_pos (firstOrderLowRateScale_pos hrho)
        (mul_pos hrho (firstOrderLowRateBeta_pos hrho))
    have : T / rho < 2 * T / rho := div_lt_div_of_pos_right (by linarith) hrho
    linarith
  rw [firstOrderLowRate_margin_factor hrho hregime]
  dsimp only [lowRateEtaSlope, beta, T, a]
  have hgap : eta / 2 ≤ lowRateFiniteLengthCertifiedAgreement rho eta -
      firstOrderLowRateThreshold rho := by
    dsimp only [T, a] at haLower
    linarith
  have hgap0 : 0 ≤ lowRateFiniteLengthCertifiedAgreement rho eta -
      firstOrderLowRateThreshold rho := by linarith
  have hprod : eta / 2 *
        (2 * firstOrderLowRateThreshold rho / rho - firstOrderLowRateBeta rho) ≤
      (lowRateFiniteLengthCertifiedAgreement rho eta - firstOrderLowRateThreshold rho) *
        ((lowRateFiniteLengthCertifiedAgreement rho eta + firstOrderLowRateThreshold rho) /
          rho - firstOrderLowRateBeta rho) := by
    calc
      eta / 2 * (2 * firstOrderLowRateThreshold rho / rho -
          firstOrderLowRateBeta rho) ≤
          (lowRateFiniteLengthCertifiedAgreement rho eta -
            firstOrderLowRateThreshold rho) *
              (2 * firstOrderLowRateThreshold rho / rho -
                firstOrderLowRateBeta rho) := by gcongr
      _ ≤ (lowRateFiniteLengthCertifiedAgreement rho eta -
            firstOrderLowRateThreshold rho) *
          ((lowRateFiniteLengthCertifiedAgreement rho eta +
              firstOrderLowRateThreshold rho) / rho -
            firstOrderLowRateBeta rho) := by gcongr
  calc
    firstOrderLowRateBeta rho / 4 *
          (2 * firstOrderLowRateThreshold rho / rho - firstOrderLowRateBeta rho) * eta =
        firstOrderLowRateBeta rho / 2 *
          (eta / 2 * (2 * firstOrderLowRateThreshold rho / rho -
            firstOrderLowRateBeta rho)) := by ring
    _ ≤ firstOrderLowRateBeta rho / 2 *
        ((lowRateFiniteLengthCertifiedAgreement rho eta -
            firstOrderLowRateThreshold rho) *
          ((lowRateFiniteLengthCertifiedAgreement rho eta +
              firstOrderLowRateThreshold rho) / rho -
            firstOrderLowRateBeta rho)) := by gcongr
    _ = _ := by ring

/-- The `1/n` rate saving contributes the second part of the finite-length slack. -/
theorem lowRateInverseLengthSlope_div_length_le_gain
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    lowRateInverseLengthSlope rho / n ≤
      firstOrderSourceDensity (finiteLengthRate rho n)
          (lowRateFiniteLengthCertifiedAgreement rho eta) (firstOrderLowRateBeta rho) -
        firstOrderSourceDensity rho (lowRateFiniteLengthCertifiedAgreement rho eta)
          (firstOrderLowRateBeta rho) := by
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let T := firstOrderLowRateThreshold rho
  let beta := firstOrderLowRateBeta rho
  have hregime : FirstOrderLowRateRegime rho :=
    (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
  have ha0 : 0 < a := by
    dsimp only [a]
    exact lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le
  have hTa : T ≤ a := by
    have := lowRateFiniteLengthCertifiedAgreement_ge_half_slack
      (rho := rho) heta.le haOne.le
    change T + eta / 2 ≤ a at this
    linarith
  have hT0 : 0 < T := hrho.trans
    (by simpa only [T] using rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime)
  have hb0 : 0 ≤ beta := by
    dsimp only [beta]
    exact (firstOrderLowRateBeta_pos hrho).le
  have hbcut : beta < a / rho := by
    have hfixed : beta < T / rho := by
      dsimp only [beta, T]
      exact firstOrderLowRateBeta_lt_threshold_div_rate hrho
    exact hfixed.trans_le (div_le_div_of_nonneg_right hTa hrho.le)
  have hgain := sourceDensity_gain_at_finiteLengthRate hrho hn ha0 hb0 hbcut
  have hsq : T ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg (a - T)]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast length_pos_of_two_le_rate_mul_length hn
  have hcoef : lowRateInverseLengthSlope rho / n ≤
      beta * a ^ 2 / (3 * rho ^ 2 * n) := by
    change (beta * T ^ 2 / (3 * rho ^ 2)) / n ≤
      beta * a ^ 2 / (3 * rho ^ 2 * n)
    calc
      beta * T ^ 2 / (3 * rho ^ 2) / (n : ℝ) =
          beta * T ^ 2 / (3 * rho ^ 2 * n) := by ring
      _ ≤ beta * a ^ 2 / (3 * rho ^ 2 * n) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq hb0) (by positivity)
  exact hcoef.trans hgain

/-- Exact analytic finite-length margin, linear in `eta + 1/n`, on the stationary branch. -/
theorem lowRateFiniteLengthSlope_mul_slack_le_margin
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    lowRateFiniteLengthSlope rho * finiteLengthSlack eta n ≤
      lowRateFiniteLengthDensityMargin rho eta n := by
  have hetaPart := lowRateEtaSlope_mul_eta_le_fixed_margin hrho hlow heta haOne
  have hnPart := lowRateInverseLengthSlope_div_length_le_gain
    hrho hrhoOne hlow heta haOne hn
  have hsEta : lowRateFiniteLengthSlope rho ≤ lowRateEtaSlope rho := min_le_left _ _
  have hsN : lowRateFiniteLengthSlope rho ≤ lowRateInverseLengthSlope rho := min_le_right _ _
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast length_pos_of_two_le_rate_mul_length hn
  have hleft : lowRateFiniteLengthSlope rho * eta ≤ lowRateEtaSlope rho * eta := by
    gcongr
  have hright : lowRateFiniteLengthSlope rho / n ≤ lowRateInverseLengthSlope rho / n := by
    gcongr
  unfold lowRateFiniteLengthDensityMargin finiteLengthSlack
  calc
    lowRateFiniteLengthSlope rho * (eta + 1 / (n : ℝ)) =
        lowRateFiniteLengthSlope rho * eta + lowRateFiniteLengthSlope rho / n := by ring
    _ ≤ lowRateEtaSlope rho * eta + lowRateInverseLengthSlope rho / n :=
      add_le_add hleft hright
    _ ≤ (firstOrderSourceDensity rho (lowRateFiniteLengthCertifiedAgreement rho eta)
          (firstOrderLowRateBeta rho) - firstOrderRankDensity (firstOrderLowRateBeta rho)) +
        (firstOrderSourceDensity (finiteLengthRate rho n)
            (lowRateFiniteLengthCertifiedAgreement rho eta) (firstOrderLowRateBeta rho) -
          firstOrderSourceDensity rho (lowRateFiniteLengthCertifiedAgreement rho eta)
            (firstOrderLowRateBeta rho)) := add_le_add hetaPart hnPart
    _ = firstOrderSourceDensity (finiteLengthRate rho n)
          (lowRateFiniteLengthCertifiedAgreement rho eta) (firstOrderLowRateBeta rho) -
        firstOrderRankDensity (firstOrderLowRateBeta rho) := by ring

end

end ReedSolomon.FirstOrder
