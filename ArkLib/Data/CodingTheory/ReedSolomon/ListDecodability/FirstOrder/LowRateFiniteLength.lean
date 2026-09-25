/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.LowRateStationary
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthSelectors

/-!
# Finite-length parameters for the low-rate first-order branch

This module bounds the exact source-density margin when the derivative ratio is fixed at the
stationary low-rate value and the source density is evaluated at the finite-length rate.
It defines the corresponding agreement and interpolation selectors, and proves a finite count
gap after rank rounding.

## Main statements

* `lowRateFiniteLengthSlope_mul_slack_le_margin` gives a rate-only linear lower bound on the
  finite-length density margin.
* `lowRateFiniteLengthSourceDensity_mul_cube_le_sourceCount` bounds the rounded source count, and
  `firstOrderRankCount_floor_le_density_add_rounding` bounds the rounded rank count.
* `lowRateFiniteLength_count_gap` gives a positive finite count gap for the literal selectors.

## References

* [DKT26]
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

/-- The rate-only slope controlling the agreement slack on the stationary branch. -/
def lowRateAgreementSlackSlope (rho : ℝ) : ℝ :=
  firstOrderLowRateBeta rho / 4 *
    (2 * firstOrderLowRateThreshold rho / rho - firstOrderLowRateBeta rho)

/-- The rate-only slope contributed by evaluating the source density at `rho - 1/n`. -/
def lowRateInverseLengthSlope (rho : ℝ) : ℝ :=
  firstOrderLowRateBeta rho * firstOrderLowRateThreshold rho ^ 2 / (3 * rho ^ 2)

/-- The smaller rate-only slope controls both terms of the finite-length slack. -/
def lowRateFiniteLengthSlope (rho : ℝ) : ℝ :=
  min (lowRateAgreementSlackSlope rho) (lowRateInverseLengthSlope rho)

/-- The clipped agreement retains at least half of the positive slack above the threshold. -/
theorem lowRateFiniteLengthCertifiedAgreement_ge_half_slack
    {rho eta : ℝ} (heta : 0 ≤ eta)
    (haOne : firstOrderLowRateThreshold rho + eta ≤ 1) :
    firstOrderLowRateThreshold rho + eta / 2 ≤
      lowRateFiniteLengthCertifiedAgreement rho eta := by
  rw [lowRateFiniteLengthCertifiedAgreement]
  apply le_min
  · linarith
  · linarith

/-- The clipped agreement is below one when the untruncated value is below one. -/
theorem lowRateFiniteLengthCertifiedAgreement_lt_one
    {rho eta : ℝ} (haOne : firstOrderLowRateThreshold rho + eta < 1) :
    lowRateFiniteLengthCertifiedAgreement rho eta < 1 := by
  unfold lowRateFiniteLengthCertifiedAgreement
  exact (min_le_left _ _).trans_lt haOne

/-- The clipped low-rate agreement is positive for a positive rate and nonnegative slack. -/
theorem lowRateFiniteLengthCertifiedAgreement_pos
    {rho eta : ℝ} (hrho : 0 < rho) (heta : 0 ≤ eta) :
    0 < lowRateFiniteLengthCertifiedAgreement rho eta := by
  have hthreshold : 0 < firstOrderLowRateThreshold rho := by
    unfold firstOrderLowRateThreshold
    exact add_pos (firstOrderLowRateScale_pos hrho)
      (mul_pos hrho (firstOrderLowRateBeta_pos hrho))
  unfold lowRateFiniteLengthCertifiedAgreement
  exact lt_min (by linarith) (by linarith)

/-- The low-rate finite-length slope is positive below the branch switch. -/
theorem lowRateFiniteLengthSlope_pos {rho : ℝ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch) :
    0 < lowRateFiniteLengthSlope rho := by
  have hregime : FirstOrderLowRateRegime rho :=
    (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
  have hbeta := firstOrderLowRateBeta_pos hrho
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hregime
  have hcut := firstOrderLowRateBeta_lt_threshold_div_rate hrho
  unfold lowRateFiniteLengthSlope lowRateAgreementSlackSlope lowRateInverseLengthSlope
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

/-- The fixed-rate density margin is at least the agreement slope times `eta`. -/
theorem lowRateAgreementSlackSlope_mul_slack_le_fixed_margin
    {rho eta : ℝ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1) :
    lowRateAgreementSlackSlope rho * eta ≤
      firstOrderSourceDensity rho (lowRateFiniteLengthCertifiedAgreement rho eta)
          (firstOrderLowRateBeta rho) - firstOrderRankDensity (firstOrderLowRateBeta rho) := by
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let T := firstOrderLowRateThreshold rho
  let beta := firstOrderLowRateBeta rho
  have hregime : FirstOrderLowRateRegime rho :=
    (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
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
  dsimp only [lowRateAgreementSlackSlope, beta, T, a]
  have hgap : eta / 2 ≤ lowRateFiniteLengthCertifiedAgreement rho eta -
      firstOrderLowRateThreshold rho := by
    dsimp only [T, a] at haLower
    linarith
  have hgap0 : 0 ≤ lowRateFiniteLengthCertifiedAgreement rho eta -
      firstOrderLowRateThreshold rho := by linarith
  have hprod : eta / 2 *
        (2 * firstOrderLowRateThreshold rho / rho - firstOrderLowRateBeta rho) ≤
      (lowRateFiniteLengthCertifiedAgreement rho eta -
        firstOrderLowRateThreshold rho) *
        ((lowRateFiniteLengthCertifiedAgreement rho eta +
          firstOrderLowRateThreshold rho) / rho - firstOrderLowRateBeta rho) := by
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

/-- The rate decrease contributes the inverse-length slope to the source-density margin. -/
theorem lowRateInverseLengthSlope_div_length_le_gain
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (heta : 0 < eta)
    (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    lowRateInverseLengthSlope rho / n ≤
      firstOrderSourceDensity (finiteLengthRate rho n)
          (lowRateFiniteLengthCertifiedAgreement rho eta) (firstOrderLowRateBeta rho) -
        firstOrderSourceDensity rho (lowRateFiniteLengthCertifiedAgreement rho eta)
          (firstOrderLowRateBeta rho) := by
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let T := firstOrderLowRateThreshold rho
  let beta := firstOrderLowRateBeta rho
  have ha0 : 0 < a := by
    dsimp only [a]
    exact lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le
  have hTa : T ≤ a := by
    have := lowRateFiniteLengthCertifiedAgreement_ge_half_slack
      (rho := rho) heta.le haOne.le
    change T + eta / 2 ≤ a at this
    linarith
  have hb0 : 0 ≤ beta := by
    dsimp only [beta]
    exact (firstOrderLowRateBeta_pos hrho).le
  have hbcut : beta < a / rho := by
    have hfixed : beta < T / rho := by
      dsimp only [beta, T]
      exact firstOrderLowRateBeta_lt_threshold_div_rate hrho
    exact hfixed.trans_le (div_le_div_of_nonneg_right hTa hrho.le)
  have hgain := sourceDensity_gain_at_finiteLengthRate hrho hn ha0 hb0 hbcut
  have hsq : T ^ 2 ≤ a ^ 2 := by
    have hTnonneg : 0 ≤ T := by
      dsimp only [T, firstOrderLowRateThreshold]
      positivity [firstOrderLowRateScale_pos hrho, firstOrderLowRateBeta_pos hrho]
    nlinarith [sq_nonneg (a - T)]
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

/-- The finite-length density margin is bounded below by the slope times `eta + 1/n`. -/
theorem lowRateFiniteLengthSlope_mul_slack_le_margin
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    lowRateFiniteLengthSlope rho * finiteLengthSlack eta n ≤
      lowRateFiniteLengthDensityMargin rho eta n := by
  have hetaPart := lowRateAgreementSlackSlope_mul_slack_le_fixed_margin
    hrho hlow heta haOne
  have hnPart := lowRateInverseLengthSlope_div_length_le_gain
    hrho heta haOne hn
  have hsEta : lowRateFiniteLengthSlope rho ≤ lowRateAgreementSlackSlope rho := min_le_left _ _
  have hsN : lowRateFiniteLengthSlope rho ≤ lowRateInverseLengthSlope rho := min_le_right _ _
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast length_pos_of_two_le_rate_mul_length hn
  have hleft : lowRateFiniteLengthSlope rho * eta ≤
      lowRateAgreementSlackSlope rho * eta := by
    gcongr
  have hright : lowRateFiniteLengthSlope rho / n ≤ lowRateInverseLengthSlope rho / n := by
    gcongr
  unfold lowRateFiniteLengthDensityMargin finiteLengthSlack
  calc
    lowRateFiniteLengthSlope rho * (eta + 1 / (n : ℝ)) =
        lowRateFiniteLengthSlope rho * eta + lowRateFiniteLengthSlope rho / n := by ring
    _ ≤ lowRateAgreementSlackSlope rho * eta + lowRateInverseLengthSlope rho / n :=
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

/-! ## Low-rate interpolation selectors and count estimates -/

/-- The rank-rounding coefficient for the stationary low-rate derivative ratio. -/
def lowRateFiniteLengthRankRoundingConstant (rho : ℝ) : ℝ :=
  2 * firstOrderLowRateBeta rho + 3

/-- The multiplicity selected from the low-rate density margin. -/
def lowRateFiniteLengthMultiplicity (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌈4 * lowRateFiniteLengthRankRoundingConstant rho /
    lowRateFiniteLengthDensityMargin rho eta n⌉₊

/-- The derivative cap is the floor of the stationary ratio times the multiplicity. -/
def lowRateFiniteLengthDerivativeCap (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌊firstOrderLowRateBeta rho * lowRateFiniteLengthMultiplicity rho eta n⌋₊

/-- The total jet degree selected from the agreement and exact finite rate. -/
def lowRateFiniteLengthJetDegree (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌈lowRateFiniteLengthMultiplicity rho eta n *
    lowRateFiniteLengthCertifiedAgreement rho eta / finiteLengthRate rho n⌉₊

/-- The exact source count for the low-rate finite-length selectors. -/
def lowRateFiniteLengthSourceCount (rho eta : ℝ) (n : ℕ) : ℝ :=
  firstOrderSourceCount (finiteLengthRate rho n)
    (lowRateFiniteLengthCertifiedAgreement rho eta)
    (lowRateFiniteLengthMultiplicity rho eta n)
    (lowRateFiniteLengthDerivativeCap rho eta n)
    (lowRateFiniteLengthJetDegree rho eta n)

/-- The exact local-rank count for the low-rate finite-length selectors. -/
def lowRateFiniteLengthRankCount (rho eta : ℝ) (n : ℕ) : ℕ :=
  firstOrderRankCount (lowRateFiniteLengthMultiplicity rho eta n)
    (lowRateFiniteLengthDerivativeCap rho eta n)

/-- The low-rate finite-length density margin is positive in the stated parameter range. -/
theorem lowRateFiniteLengthDensityMargin_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    0 < lowRateFiniteLengthDensityMargin rho eta n := by
  have hc := lowRateFiniteLengthSlope_pos hrho hlow
  have hs := finiteLengthSlack_pos (n := n) heta
  exact (mul_pos hc hs).trans_le
    (lowRateFiniteLengthSlope_mul_slack_le_margin hrho hlow heta haOne hn)

/-- The selected low-rate multiplicity is positive. -/
theorem lowRateFiniteLengthMultiplicity_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    0 < lowRateFiniteLengthMultiplicity rho eta n := by
  unfold lowRateFiniteLengthMultiplicity
  apply Nat.ceil_pos.mpr
  have hmargin := lowRateFiniteLengthDensityMargin_pos
    hrho hlow heta haOne hn
  have hbeta := firstOrderLowRateBeta_pos hrho
  unfold lowRateFiniteLengthRankRoundingConstant
  positivity

/-- The rounded source count covers the low-rate source-density cubic. -/
theorem lowRateFiniteLengthSourceDensity_mul_cube_le_sourceCount
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthMultiplicity rho eta n : ℝ) ^ 3 *
        firstOrderSourceDensity (finiteLengthRate rho n)
          (lowRateFiniteLengthCertifiedAgreement rho eta) (firstOrderLowRateBeta rho) ≤
      lowRateFiniteLengthSourceCount rho eta n := by
  let R := finiteLengthRate rho n
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let beta := firstOrderLowRateBeta rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  have hregime : FirstOrderLowRateRegime rho :=
    (firstOrderLowRateRegime_iff_lt_rateSwitch rho).2 hlow
  have hR : 0 < R := finiteLengthRate_pos hrho hn
  have hRrho : R < rho := finiteLengthRate_lt_rate
    (length_pos_of_two_le_rate_mul_length hn)
  have hTa : firstOrderLowRateThreshold rho ≤ a := by
    have h := lowRateFiniteLengthCertifiedAgreement_ge_half_slack
      (rho := rho) heta.le haOne.le
    dsimp only [a] at h ⊢
    linarith
  have hRa : R ≤ a := (hRrho.trans
    ((rate_lt_firstOrderLowRateThreshold hrho hregime).trans_le hTa)).le
  have hb0 : 0 ≤ beta := by
    dsimp only [beta]
    exact (firstOrderLowRateBeta_pos hrho).le
  have hbcut : beta < a / R := by
    have hfixed : beta < firstOrderLowRateThreshold rho / rho := by
      dsimp only [beta]
      exact firstOrderLowRateBeta_lt_threshold_div_rate hrho
    have hfirst : firstOrderLowRateThreshold rho / rho ≤ a / rho :=
      div_le_div_of_nonneg_right hTa hrho.le
    have hsecond : a / rho ≤ a / R := by
      exact div_le_div_of_nonneg_left
        (lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le).le hR hRrho.le
    exact hfixed.trans_le (hfirst.trans hsecond)
  have hm : 0 < m := by
    dsimp only [m]
    exact lowRateFiniteLengthMultiplicity_pos hrho hlow heta haOne hn
  have hmu : ⌊(m : ℝ) * a / R⌋₊ ≤ lowRateFiniteLengthJetDegree rho eta n := by
    dsimp only [a, R, m, lowRateFiniteLengthJetDegree]
    exact Nat.floor_le_ceil _
  have hsource := cube_mul_sourceDensity_le_firstOrderSourceCount
    (rate := R) (a := a) (beta := beta) (m := m)
    (mu := lowRateFiniteLengthJetDegree rho eta n) hR hRa hb0 hbcut.le hmu
  dsimp only [firstOrderSourceDensity, R, a, beta, m] at hsource ⊢
  simpa only [lowRateFiniteLengthSourceCount, lowRateFiniteLengthDerivativeCap,
    lowRateFiniteLengthJetDegree] using hsource

/-- The multiplicity ceiling absorbs rank rounding and leaves the stated finite count gap. -/
theorem lowRateFiniteLength_count_gap
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    3 * (lowRateFiniteLengthMultiplicity rho eta n : ℝ) ^ 3 *
        lowRateFiniteLengthDensityMargin rho eta n / 4 ≤
      lowRateFiniteLengthSourceCount rho eta n - lowRateFiniteLengthRankCount rho eta n := by
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let delta := lowRateFiniteLengthDensityMargin rho eta n
  let crank := lowRateFiniteLengthRankRoundingConstant rho
  let beta := firstOrderLowRateBeta rho
  have hmNat : 0 < m := lowRateFiniteLengthMultiplicity_pos
    hrho hlow heta haOne hn
  have hdelta : 0 < delta := lowRateFiniteLengthDensityMargin_pos
    hrho hlow heta haOne hn
  have hceil : 4 * crank / delta ≤ (m : ℝ) := by
    dsimp only [m, crank, delta]
    unfold lowRateFiniteLengthMultiplicity
    exact Nat.le_ceil _
  have hcrank0 : 0 ≤ crank := by
    dsimp only [crank, lowRateFiniteLengthRankRoundingConstant]
    have := firstOrderLowRateBeta_pos hrho
    positivity
  have habsorb : 4 * crank ≤ (m : ℝ) * delta := by
    exact (div_le_iff₀ hdelta).mp (by simpa [mul_comm] using hceil)
  have hround : crank * (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 * delta / 4 := by
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr habsorb)]
  have hsource := lowRateFiniteLengthSourceDensity_mul_cube_le_sourceCount
    hrho hlow heta haOne hn
  have hrank := firstOrderRankCount_floor_le_density_add_rounding
    (firstOrderLowRateBeta_pos hrho).le m
  have hrank' : (lowRateFiniteLengthRankCount rho eta n : ℝ) ≤
      (m : ℝ) ^ 3 * firstOrderRankDensity (firstOrderLowRateBeta rho) +
        lowRateFiniteLengthRankRoundingConstant rho * (m : ℝ) ^ 2 := by
    simpa only [m, lowRateFiniteLengthRankCount, lowRateFiniteLengthDerivativeCap,
      lowRateFiniteLengthRankRoundingConstant] using hrank
  dsimp only [delta, lowRateFiniteLengthDensityMargin, m, beta, crank]
    at hround hsource hrank' ⊢
  nlinarith

end

end ReedSolomon.FirstOrder
