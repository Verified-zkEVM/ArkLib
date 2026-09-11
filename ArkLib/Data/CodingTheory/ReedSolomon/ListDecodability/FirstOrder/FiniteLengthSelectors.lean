/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.AutomaticBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthParameters

/-!
# Length-dependent first-order interpolation selectors

This file implements the one-degree rate saving used in the finite-length first-order theorem.
The optimizer is chosen at the fixed rate `rho`, while the source density and total jet degree
are evaluated at `rho - 1 / n`.  This distinction is what upgrades inverse agreement slack to
inverse `eta + 1 / n` without changing the derivative cap or its characteristic guard.

The present API covers the clean (upper) branch of the first-order rate curve.  The hypothesis
`automaticBeta rho a ≤ 1 / 2` says exactly that the cubic rank expression is the exact lower
branch of `firstOrderRankDensity`; it avoids building the manuscript's still-unformalized
low-rate stationary root into this module.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder

open ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- The exact normalized degree bound `(k - 1) / n = rho - 1 / n`. -/
def finiteLengthRate (rho : ℝ) (n : ℕ) : ℝ := rho - 1 / (n : ℝ)

/-- The clipped agreement used by the finite-length selector. -/
def finiteLengthCertifiedAgreement (rho eta : ℝ) : ℝ :=
  automaticAgreement rho (automaticFirstOrderThreshold rho + eta)

/-- The derivative-degree ratio remains tuned at the fixed rate `rho`. -/
def finiteLengthDerivativeRatio (rho eta : ℝ) : ℝ :=
  automaticBeta rho (automaticFirstOrderThreshold rho + eta)

/-- Exact finite-length density margin.  Only the source density sees `rho - 1 / n`. -/
def finiteLengthDensityMargin (rho eta : ℝ) (n : ℕ) : ℝ :=
  firstOrderSourceDensity (finiteLengthRate rho n)
      (finiteLengthCertifiedAgreement rho eta) (finiteLengthDerivativeRatio rho eta) -
    firstOrderRankDensity (finiteLengthDerivativeRatio rho eta)

/-- The manuscript's finite rank-rounding coefficient `2 * beta + 3`. -/
def finiteLengthRankRoundingConstant (rho eta : ℝ) : ℝ :=
  2 * finiteLengthDerivativeRatio rho eta + 3

/-- Literal finite-length multiplicity selector. -/
def finiteLengthMultiplicity (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌈4 * finiteLengthRankRoundingConstant rho eta /
    finiteLengthDensityMargin rho eta n⌉₊

/-- Literal derivative cap `floor (beta * m)`.  In particular, zero is retained. -/
def finiteLengthDerivativeCap (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌊finiteLengthDerivativeRatio rho eta * finiteLengthMultiplicity rho eta n⌋₊

/-- Literal total jet degree `ceil (m * a_cert / (rho - 1/n))`. -/
def finiteLengthJetDegree (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌈finiteLengthMultiplicity rho eta n * finiteLengthCertifiedAgreement rho eta /
    finiteLengthRate rho n⌉₊

/-- Exact paper source count at the length-dependent rate. -/
def finiteLengthSourceCount (rho eta : ℝ) (n : ℕ) : ℝ :=
  firstOrderRateSourceCount (finiteLengthRate rho n)
    (finiteLengthCertifiedAgreement rho eta) (finiteLengthMultiplicity rho eta n)
    (finiteLengthDerivativeCap rho eta n) (finiteLengthJetDegree rho eta n)

/-- Exact paper local-rank count for the length-dependent selector. -/
def finiteLengthRankCount (rho eta : ℝ) (n : ℕ) : ℕ :=
  firstOrderRateRankCount (finiteLengthMultiplicity rho eta n)
    (finiteLengthDerivativeCap rho eta n)

/-- Literal challenge height, with the exact natural floor and the `max 1` endpoint. -/
def finiteLengthChallengeHeight (rho eta : ℝ) (n : ℕ) : ℕ :=
  max 1 ⌊(finiteLengthRankCount rho eta n : ℝ) * finiteLengthJetDegree rho eta n /
    (finiteLengthSourceCount rho eta n - finiteLengthRankCount rho eta n)⌋₊

theorem finiteLengthRate_eq {rho : ℝ} {n : ℕ} (hn : 0 < n) :
    finiteLengthRate rho n * n = rho * n - 1 := by
  unfold finiteLengthRate
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp

theorem half_rate_le_finiteLengthRate {rho : ℝ} {n : ℕ}
    (_hrho : 0 < rho) (hn : (2 : ℝ) ≤ rho * n) :
    rho / 2 ≤ finiteLengthRate rho n := by
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    rw [this, mul_zero] at hn
    norm_num at hn
  unfold finiteLengthRate
  have hinv : 1 / (n : ℝ) ≤ rho / 2 := by
    rw [div_le_iff₀ hn0]
    nlinarith
  linarith

theorem finiteLengthRate_pos {rho : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hn : (2 : ℝ) ≤ rho * n) :
    0 < finiteLengthRate rho n := by
  exact (half_pos hrho).trans_le (half_rate_le_finiteLengthRate hrho hn)

theorem length_pos_of_two_le_rate_mul_length {rho : ℝ} {n : ℕ}
    (hn : (2 : ℝ) ≤ rho * n) : 0 < n := by
  by_contra h
  have hz : n = 0 := Nat.eq_zero_of_not_pos h
  subst n
  norm_num at hn

theorem finiteLengthRate_lt_rate {rho : ℝ} {n : ℕ} (hn : 0 < n) :
    finiteLengthRate rho n < rho := by
  unfold finiteLengthRate
  have : (0 : ℝ) < 1 / n := by positivity
  linarith

/-- Decreasing the rate by `1/n` raises the source density by a controlled amount.

The assumptions are deliberately stated for an arbitrary fixed derivative ratio.  The strict
cutoff `beta < a / rho` is the same inequality used to show `M ≤ B`; no branch formula is
used here. -/
theorem sourceDensity_gain_at_finiteLengthRate
    {rho a beta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hn : (2 : ℝ) ≤ rho * n)
    (ha : 0 < a) (hbeta0 : 0 ≤ beta) (hbeta : beta < a / rho) :
    beta * a ^ 2 / (3 * rho ^ 2 * n) ≤
      firstOrderSourceDensity (finiteLengthRate rho n) a beta -
        firstOrderSourceDensity rho a beta := by
  let rn := finiteLengthRate rho n
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    rw [this, mul_zero] at hn
    norm_num at hn
  have hrn0 : 0 < rn := finiteLengthRate_pos hrho hn
  have hrnle : rn ≤ rho := (finiteLengthRate_lt_rate (n := n) (by exact_mod_cast hn0)).le
  have hbetaSq : beta ^ 2 * rho ^ 2 ≤ a ^ 2 := by
    have hbr : beta * rho < a := by
      rw [lt_div_iff₀ hrho] at hbeta
      simpa [mul_comm] using hbeta
    have hbr0 : 0 ≤ beta * rho := mul_nonneg hbeta0 hrho.le
    nlinarith
  have hdenle : 2 * rho * rn ≤ 2 * rho ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hrnle hrho.le]
  have hfirst : beta * a ^ 2 / (2 * rho ^ 2) ≤
      beta * a ^ 2 / (2 * rho * rn) := by
    exact div_le_div_of_nonneg_left (mul_nonneg hbeta0 (sq_nonneg a))
      (mul_pos (mul_pos (by norm_num) hrho) hrn0) hdenle
  have hcube : beta ^ 3 / 6 ≤ beta * a ^ 2 / (6 * rho ^ 2) := by
    field_simp [ne_of_gt hrho]
    nlinarith [mul_le_mul_of_nonneg_left hbetaSq hbeta0]
  have hbracket : beta * a ^ 2 / (3 * rho ^ 2) ≤
      beta * a ^ 2 / (2 * rho * rn) - beta ^ 3 / 6 := by
    have hrhoSq : rho ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hrho)
    field_simp [hrhoSq] at hfirst hcube ⊢
    nlinarith
  have hidentity :
      firstOrderSourceDensity rn a beta - firstOrderSourceDensity rho a beta =
        (rho - rn) *
          (beta * a ^ 2 / (2 * rho * rn) - beta ^ 3 / 6) := by
    unfold firstOrderSourceDensity
    field_simp [ne_of_gt hrho, ne_of_gt hrn0]
    ring
  have hdiff : rho - rn = 1 / (n : ℝ) := by
    dsimp only [rn, finiteLengthRate]
    ring
  rw [hidentity, hdiff]
  calc
    beta * a ^ 2 / (3 * rho ^ 2 * n) =
        (1 / (n : ℝ)) * (beta * a ^ 2 / (3 * rho ^ 2)) := by ring
    _ ≤ (1 / (n : ℝ)) *
        (beta * a ^ 2 / (2 * rho * rn) - beta ^ 3 / 6) := by gcongr

/-- On the clean branch, the exact fixed-rate margin is the automatic surplus. -/
theorem finiteLength_fixedRateMargin_eq_surplus
    {rho eta : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    firstOrderSourceDensity rho (finiteLengthCertifiedAgreement rho eta)
        (finiteLengthDerivativeRatio rho eta) -
      firstOrderRankDensity (finiteLengthDerivativeRatio rho eta) =
        automaticSurplus rho (automaticFirstOrderThreshold rho + eta) := by
  have hrank : firstOrderRankDensity (finiteLengthDerivativeRatio rho eta) =
      firstOrderRankCubicEnvelope (finiteLengthDerivativeRatio rho eta) := by
    rw [firstOrderRankDensity, if_pos hbeta, firstOrderRankCubicEnvelope]
  rw [hrank]
  have hidentity := automatic_sourceDensity_sub_rankDensityEnvelope
    (rho := rho) (a := automaticFirstOrderThreshold rho + eta)
    hrho hrhoOne
  unfold finiteLengthCertifiedAgreement finiteLengthDerivativeRatio
  unfold automaticSourceDensity automaticRankDensityEnvelope at hidentity
  exact hidentity

/-- The exact length-dependent margin is at least a rate-only multiple of `eta + 1/n`.

This is the central finite-length bridge: `beta` stays tuned at `rho`, so the characteristic
guard is unchanged, while the one-degree saving contributes the additional `1/n` margin. -/
theorem automaticSurplusSlope_mul_finiteLengthSlack_le_margin
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    automaticSurplusSlope rho * finiteLengthSlack eta n ≤
      finiteLengthDensityMargin rho eta n := by
  let a := finiteLengthCertifiedAgreement rho eta
  let beta := finiteLengthDerivativeRatio rho eta
  have ha : 0 < a := by
    have := rho_lt_automaticAgreement hrho hrhoOne
      (show automaticFirstOrderThreshold rho < automaticFirstOrderThreshold rho + eta by
        linarith)
    exact hrho.trans this
  have hb0 : 0 < beta := by
    exact automaticBeta_pos hrho hrhoOne (by linarith) haOne
  have hbcut : beta < a / rho := by
    exact automaticBeta_lt_agreement_div_rate hrho hrhoOne (by linarith) haOne
  have hgain := sourceDensity_gain_at_finiteLengthRate hrho hn ha hb0.le hbcut
  have hbase := automaticSurplusSlope_mul_eta_le hrho hrhoOne heta haOne
  have hbetaLower : 3 * automaticRateGap rho / 8 ≤ beta := by
    let a₀ := automaticAgreement rho (automaticFirstOrderThreshold rho + eta)
    have ha₀mid : a₀ ≤ (1 + automaticFirstOrderThreshold rho) / 2 := by
      dsimp only [a₀]
      rw [automaticAgreement_eq_min]
      exact min_le_right _ _
    have hden : 0 < 2 * (2 - rho) := by nlinarith
    dsimp only [beta, finiteLengthDerivativeRatio]
    unfold automaticBeta
    dsimp only [a₀] at ha₀mid ⊢
    unfold automaticRateGap
    rw [le_div_iff₀ hden]
    nlinarith
  have harho : rho ≤ a := by
    exact (rho_lt_automaticAgreement hrho hrhoOne (by linarith)).le
  have haSq : rho ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg (a - rho)]
  have hgainSlope : automaticSurplusSlope rho / n ≤
      beta * a ^ 2 / (3 * rho ^ 2 * n) := by
    have hn0 : (0 : ℝ) < n := by
      by_contra h
      have : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
      rw [this, mul_zero] at hn
      norm_num at hn
    have hgap0 : 0 ≤ automaticRateGap rho :=
      (automaticRateGap_pos hrho hrhoOne).le
    unfold automaticSurplusSlope
    have hprod := mul_le_mul hbetaLower haSq (sq_nonneg rho) hb0.le
    have hrhoSq : 0 < rho ^ 2 := sq_pos_of_pos hrho
    have hbaseSlope : 3 * automaticRateGap rho / 64 ≤
        beta * a ^ 2 / (3 * rho ^ 2) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hrhoSq)]
      nlinarith
    calc
      3 * automaticRateGap rho / 64 / (n : ℝ) ≤
          (beta * a ^ 2 / (3 * rho ^ 2)) / (n : ℝ) :=
        (div_le_div_iff_of_pos_right hn0).2 hbaseSlope
      _ = beta * a ^ 2 / (3 * rho ^ 2 * n) := by ring
  have hfixed := finiteLength_fixedRateMargin_eq_surplus hrho hrhoOne hbetaHalf
  unfold finiteLengthDensityMargin
  dsimp only [a, beta] at hgain hbase hgainSlope hfixed ⊢
  calc
    automaticSurplusSlope rho * finiteLengthSlack eta n =
        automaticSurplusSlope rho * eta + automaticSurplusSlope rho / n := by
      unfold finiteLengthSlack
      ring
    _ ≤ finiteLengthDensityMargin rho eta n := by
      unfold finiteLengthDensityMargin
      nlinarith

/-- Rate-only coefficient for the literal finite-length multiplicity. -/
def finiteLengthMultiplicityBoundConstant (rho : ℝ) : ℝ :=
  1 + 16 / automaticSurplusSlope rho

/-- Rate-only coefficient for the literal finite-length total jet degree. -/
def finiteLengthJetBoundConstant (rho : ℝ) : ℝ :=
  2 * finiteLengthMultiplicityBoundConstant rho / rho + 1

/-- Rate-only coefficient for the challenge height after the finite count-gap estimate. -/
def finiteLengthHeightBoundConstant (rho : ℝ) : ℝ :=
  1 + 8 * finiteLengthJetBoundConstant rho / (3 * automaticSurplusSlope rho)

/-- One rate-only constant dominating all literal finite-length interpolation parameters. -/
def finiteLengthParameterBoundConstant (rho : ℝ) : ℝ :=
  max 1 (max (finiteLengthMultiplicityBoundConstant rho)
    (max (finiteLengthJetBoundConstant rho) (finiteLengthHeightBoundConstant rho)))

theorem one_le_finiteLengthParameterBoundConstant (rho : ℝ) :
    1 ≤ finiteLengthParameterBoundConstant rho := by
  unfold finiteLengthParameterBoundConstant
  exact le_max_left _ _

theorem finiteLengthSlack_lt_one_of_rate
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    finiteLengthSlack eta n < 1 := by
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    rw [this, mul_zero] at hn
    norm_num at hn
  have hinv : 1 / (n : ℝ) ≤ rho / 2 := by
    rw [div_le_iff₀ hn0]
    nlinarith
  have hthreshold := rho_lt_automaticFirstOrderThreshold hrho hrhoOne
  unfold finiteLengthSlack
  linarith

theorem finiteLengthDensityMargin_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    0 < finiteLengthDensityMargin rho eta n := by
  have hc := automaticSurplusSlope_pos hrho hrhoOne
  have hs : 0 < finiteLengthSlack eta n := by
    apply finiteLengthSlack_pos heta
    have : (0 : ℝ) < n := by
      by_contra h
      have hz : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
      rw [hz, mul_zero] at hn
      norm_num at hn
    exact_mod_cast this
  exact (mul_pos hc hs).trans_le
    (automaticSurplusSlope_mul_finiteLengthSlack_le_margin
      hrho hrhoOne heta haOne hn hbetaHalf)

theorem finiteLengthMultiplicity_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    0 < finiteLengthMultiplicity rho eta n := by
  unfold finiteLengthMultiplicity
  apply Nat.ceil_pos.mpr
  have hmargin := finiteLengthDensityMargin_pos
    hrho hrhoOne heta haOne hn hbetaHalf
  have hbeta0 : 0 < finiteLengthDerivativeRatio rho eta :=
    automaticBeta_pos hrho hrhoOne (by linarith) haOne
  unfold finiteLengthRankRoundingConstant
  positivity

/-- The manuscript's exact ceil selector has inverse finite-length-slack size. -/
theorem finiteLengthMultiplicity_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthMultiplicity rho eta n : ℝ) ≤
      finiteLengthMultiplicityBoundConstant rho / finiteLengthSlack eta n := by
  let c := automaticSurplusSlope rho
  let s := finiteLengthSlack eta n
  let delta := finiteLengthDensityMargin rho eta n
  let crank := finiteLengthRankRoundingConstant rho eta
  let m := finiteLengthMultiplicity rho eta n
  have hc : 0 < c := automaticSurplusSlope_pos hrho hrhoOne
  have hs : 0 < s := by
    dsimp only [s]
    exact finiteLengthSlack_pos heta (length_pos_of_two_le_rate_mul_length hn)
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have hdelta : c * s ≤ delta :=
    automaticSurplusSlope_mul_finiteLengthSlack_le_margin
      hrho hrhoOne heta haOne hn hbetaHalf
  have hdeltaPos : 0 < delta := (mul_pos hc hs).trans_le hdelta
  have hcrank : crank ≤ 4 := by
    dsimp only [crank, finiteLengthRankRoundingConstant]
    linarith
  have hcrank0 : 0 ≤ crank := by
    dsimp only [crank, finiteLengthRankRoundingConstant]
    have := automaticBeta_pos hrho hrhoOne (by linarith) haOne
    positivity
  have hx : 4 * crank / delta ≤ 16 / (c * s) := by
    calc
      4 * crank / delta ≤ 16 / delta := by
        exact div_le_div_of_nonneg_right (by linarith) hdeltaPos.le
      _ ≤ 16 / (c * s) := by
        exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hc hs) hdelta
  have hm : (m : ℝ) < 4 * crank / delta + 1 := by
    dsimp only [m, crank, delta]
    unfold finiteLengthMultiplicity
    apply Nat.ceil_lt_add_one
    exact div_nonneg (mul_nonneg (by norm_num) hcrank0) hdeltaPos.le
  calc
    (m : ℝ) ≤ 16 / (c * s) + 1 := by
      exact (hm.trans_le (by simpa [add_comm] using add_le_add_right hx 1)).le
    _ ≤ finiteLengthMultiplicityBoundConstant rho / s := by
      calc
        16 / (c * s) + 1 = (16 / c + s) / s := by
          field_simp [ne_of_gt hc, ne_of_gt hs]
        _ ≤ (16 / c + 1) / s := by gcongr
        _ = finiteLengthMultiplicityBoundConstant rho / s := by
          dsimp only [c]
          rw [finiteLengthMultiplicityBoundConstant]
          ring

/-- The literal floor cap is no larger than the multiplicity, including the `M = 0` endpoint. -/
theorem finiteLengthDerivativeCap_le_multiplicity
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (_hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    finiteLengthDerivativeCap rho eta n ≤ finiteLengthMultiplicity rho eta n := by
  have hb0 : 0 ≤ finiteLengthDerivativeRatio rho eta :=
    (automaticBeta_pos hrho hrhoOne (by linarith) haOne).le
  have hm0 : (0 : ℝ) ≤ finiteLengthMultiplicity rho eta n := Nat.cast_nonneg _
  have hfloor : (finiteLengthDerivativeCap rho eta n : ℝ) ≤
      finiteLengthDerivativeRatio rho eta * finiteLengthMultiplicity rho eta n := by
    unfold finiteLengthDerivativeCap
    exact Nat.floor_le (mul_nonneg hb0 hm0)
  have hmul : finiteLengthDerivativeRatio rho eta *
      finiteLengthMultiplicity rho eta n ≤ finiteLengthMultiplicity rho eta n := by
    have hm := hbetaHalf
    nlinarith
  exact_mod_cast hfloor.trans hmul

theorem finiteLengthDerivativeCap_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthDerivativeCap rho eta n : ℝ) ≤
      finiteLengthMultiplicityBoundConstant rho / finiteLengthSlack eta n := by
  exact (Nat.cast_le.mpr (finiteLengthDerivativeCap_le_multiplicity
    hrho hrhoOne heta haOne hn hbetaHalf)).trans
      (finiteLengthMultiplicity_le_inv_slack
        hrho hrhoOne heta haOne hn hbetaHalf)

/-- The derivative floor lies below the total-degree ceiling, with no positivity assumption on
the floor itself. -/
theorem finiteLengthDerivativeCap_le_jetDegree
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    finiteLengthDerivativeCap rho eta n ≤ finiteLengthJetDegree rho eta n := by
  have hrn : 0 < finiteLengthRate rho n := finiteLengthRate_pos hrho hn
  have hb0 : 0 ≤ finiteLengthDerivativeRatio rho eta :=
    (automaticBeta_pos hrho hrhoOne (by linarith) haOne).le
  have hbcutFixed : finiteLengthDerivativeRatio rho eta <
      finiteLengthCertifiedAgreement rho eta / rho :=
    automaticBeta_lt_agreement_div_rate hrho hrhoOne (by linarith) haOne
  have hrnle : finiteLengthRate rho n < rho :=
    finiteLengthRate_lt_rate (by
      have : (0 : ℝ) < n := by
        by_contra h
        have hz : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
        rw [hz, mul_zero] at hn
        norm_num at hn
      exact_mod_cast this)
  have ha0 : 0 < finiteLengthCertifiedAgreement rho eta := by
    exact hrho.trans (rho_lt_automaticAgreement hrho hrhoOne (by linarith))
  have hbcut : finiteLengthDerivativeRatio rho eta <
      finiteLengthCertifiedAgreement rho eta / finiteLengthRate rho n := by
    exact hbcutFixed.trans_le (div_le_div_of_nonneg_left ha0.le hrn hrnle.le)
  have hm0 : (0 : ℝ) ≤ finiteLengthMultiplicity rho eta n := Nat.cast_nonneg _
  have hfloor : (finiteLengthDerivativeCap rho eta n : ℝ) ≤
      finiteLengthDerivativeRatio rho eta * finiteLengthMultiplicity rho eta n := by
    unfold finiteLengthDerivativeCap
    exact Nat.floor_le (mul_nonneg hb0 hm0)
  have hmul : finiteLengthDerivativeRatio rho eta * finiteLengthMultiplicity rho eta n ≤
      finiteLengthMultiplicity rho eta n * finiteLengthCertifiedAgreement rho eta /
        finiteLengthRate rho n := by
    calc
      _ ≤ (finiteLengthCertifiedAgreement rho eta / finiteLengthRate rho n) *
          finiteLengthMultiplicity rho eta n := by gcongr
      _ = _ := by ring
  have hceil : finiteLengthMultiplicity rho eta n * finiteLengthCertifiedAgreement rho eta /
      finiteLengthRate rho n ≤ (finiteLengthJetDegree rho eta n : ℝ) := by
    unfold finiteLengthJetDegree
    exact Nat.le_ceil _
  exact_mod_cast hfloor.trans (hmul.trans hceil)

/-- The literal total jet degree has inverse finite-length-slack size. -/
theorem finiteLengthJetDegree_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthJetDegree rho eta n : ℝ) ≤
      finiteLengthJetBoundConstant rho / finiteLengthSlack eta n := by
  let m := finiteLengthMultiplicity rho eta n
  let a := finiteLengthCertifiedAgreement rho eta
  let rn := finiteLengthRate rho n
  let s := finiteLengthSlack eta n
  let cm := finiteLengthMultiplicityBoundConstant rho
  have hrnHalf : rho / 2 ≤ rn := half_rate_le_finiteLengthRate hrho hn
  have hrn : 0 < rn := finiteLengthRate_pos hrho hn
  have haOne' : a < 1 := automaticAgreement_lt_one haOne
  have hm := finiteLengthMultiplicity_le_inv_slack
    hrho hrhoOne heta haOne hn hbetaHalf
  have hs : 0 < s := finiteLengthSlack_pos heta (by
    exact length_pos_of_two_le_rate_mul_length hn)
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have harg : (m : ℝ) * a / rn ≤ 2 * cm / (rho * s) := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hma : (m : ℝ) * a ≤ m := by nlinarith
    have hratio : (m : ℝ) / rn ≤ 2 * (m : ℝ) / rho := by
      rw [div_le_iff₀ hrn, div_eq_mul_inv]
      field_simp [ne_of_gt hrho]
      nlinarith
    dsimp only [m, a, rn, s, cm] at hm ⊢
    calc
      (finiteLengthMultiplicity rho eta n : ℝ) *
          finiteLengthCertifiedAgreement rho eta / finiteLengthRate rho n ≤
          (finiteLengthMultiplicity rho eta n : ℝ) / finiteLengthRate rho n := by
        exact div_le_div_of_nonneg_right hma hrn.le
      _ ≤ 2 * finiteLengthMultiplicity rho eta n / rho := hratio
      _ ≤ 2 * finiteLengthMultiplicityBoundConstant rho /
          (rho * finiteLengthSlack eta n) := by
        calc
          2 * (finiteLengthMultiplicity rho eta n : ℝ) / rho ≤
              2 * (finiteLengthMultiplicityBoundConstant rho /
                finiteLengthSlack eta n) / rho := by gcongr
          _ = _ := by ring
  have hceil : (finiteLengthJetDegree rho eta n : ℝ) <
      (m : ℝ) * a / rn + 1 := by
    dsimp only [m, a, rn]
    unfold finiteLengthJetDegree
    apply Nat.ceil_lt_add_one
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (by exact (hrho.trans (rho_lt_automaticAgreement hrho hrhoOne (by linarith))).le))
      hrn.le
  calc
    (finiteLengthJetDegree rho eta n : ℝ) ≤
        2 * cm / (rho * s) + 1 := by
      exact (hceil.trans_le (by simpa [add_comm] using add_le_add_right harg 1)).le
    _ ≤ finiteLengthJetBoundConstant rho / s := by
      have hcm : 0 ≤ cm := by
        dsimp only [cm]
        unfold finiteLengthMultiplicityBoundConstant
        positivity [automaticSurplusSlope_pos hrho hrhoOne]
      calc
        2 * cm / (rho * s) + 1 = (2 * cm / rho + s) / s := by
          field_simp [ne_of_gt hrho, ne_of_gt hs]
        _ ≤ (2 * cm / rho + 1) / s := by gcongr
        _ = finiteLengthJetBoundConstant rho / s := by rfl

/-! ## Exact finite count gap

The automatic-rounding API uses the same rate both to select `beta` and to count source
monomials.  The finite-length selector intentionally uses `rho` for the former and
`rho - 1/n` for the latter.  The private models below record the two rounding estimates in the
needed parametric form. -/

private def finiteLengthRankRoundingModel (u v : ℝ) : ℝ :=
  (u + v) * ((1 - v) / 2 + v) -
    (2 * ((1 - v) * (2 - v) / 6 -
        (1 - u) * (1 - u - v) * (2 * (1 - u) - v) / 6) +
      (2 * u + 3 * v - 3) *
        ((1 - v) / 2 - (1 - u) * (1 - u - v) / 2) +
      u * (v - 1) * (u + v - 1))

private theorem finiteLengthRankRoundingModel_le
    {u v beta : ℝ} (hu0 : 0 ≤ u) (hub : u ≤ beta) (hbu : beta ≤ u + v)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hb1 : beta ≤ 3 / 4) :
    finiteLengthRankRoundingModel u v ≤
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 + 3 * v := by
  unfold finiteLengthRankRoundingModel
  have hu34 : u ≤ 3 / 4 := hub.trans hb1
  have hq : 0 ≤ 1 / 2 - (beta + u) / 2 +
      (beta ^ 2 + beta * u + u ^ 2) / 3 := by
    nlinarith [sq_nonneg (beta - u), sq_nonneg (beta + u - 1)]
  have hP : u / 2 - u ^ 2 / 2 + u ^ 3 / 3 ≤
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 := by
    have hdiff :
      (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3) -
          (u / 2 - u ^ 2 / 2 + u ^ 3 / 3) =
        (beta - u) * (1 / 2 - (beta + u) / 2 +
          (beta ^ 2 + beta * u + u ^ 2) / 3) := by ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hub) hq]
  have hvSq : v ^ 2 ≤ v := by
    nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv1)]
  have huSq : u ^ 2 ≤ (9 / 16 : ℝ) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hu34)
      (add_nonneg hu0 (by norm_num : (0 : ℝ) ≤ 3 / 4))
    nlinarith
  have huSqV : u ^ 2 * v ≤ (9 / 16 : ℝ) * v :=
    mul_le_mul_of_nonneg_right huSq hv0
  have huVSq : u * v ^ 2 ≤ (3 / 4 : ℝ) * v := by
    calc
      u * v ^ 2 ≤ (3 / 4 : ℝ) * v ^ 2 :=
        mul_le_mul_of_nonneg_right hu34 (sq_nonneg v)
      _ ≤ (3 / 4 : ℝ) * v := mul_le_mul_of_nonneg_left hvSq (by norm_num)
  ring_nf at ⊢
  nlinarith

private def finiteLengthLinearSum (x : ℝ) : ℝ := x * (x - 1) / 2

private def finiteLengthSquareSum (x : ℝ) : ℝ := x * (x - 1) * (2 * x - 1) / 6

private theorem finiteLength_sum_range_cast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = finiteLengthLinearSum n := by
  induction n with
  | zero => simp [finiteLengthLinearSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [finiteLengthLinearSum]
      push_cast
      ring

private theorem finiteLength_sum_range_sq_cast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) = finiteLengthSquareSum n := by
  induction n with
  | zero => simp [finiteLengthSquareSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [finiteLengthSquareSum]
      push_cast
      ring

private theorem finiteLengthRankCubicUpperCount_normalized_eq_model {m M : ℕ}
    (hm : 0 < m) (hM : M ≤ m) :
    firstOrderRankCubicUpperCount m M / (m : ℝ) ^ 3 =
      finiteLengthRankRoundingModel ((M : ℝ) / m) ((m : ℝ)⁻¹) := by
  have hamb (q : ℕ) :
      (∑ s ∈ Finset.range q, ((s + 1 : ℕ) : ℝ) * (M + 1)) =
        (M + 1) * (finiteLengthLinearSum q + q) := by
    calc
      _ = (M + 1 : ℝ) * ((∑ s ∈ Finset.range q, (s : ℝ)) + q) := by
        push_cast
        ring_nf
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
      _ = _ := by rw [finiteLength_sum_range_cast]
  have hcorrection (q : ℕ) :
      (∑ s ∈ Finset.range q,
        (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)) =
        2 * finiteLengthSquareSum q +
          (2 * M + 3 - 3 * m) * finiteLengthLinearSum q +
          q * (1 - m) * (M + 1 - m) := by
    calc
      _ = ∑ s ∈ Finset.range q,
          (2 * (s : ℝ) ^ 2 + (2 * M + 3 - 3 * m) * s +
            (1 - m) * (M + 1 - m)) := by
        apply Finset.sum_congr rfl
        intro s _
        push_cast
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, finiteLength_sum_range_cast,
          finiteLength_sum_range_sq_cast]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [firstOrderRankCubicUpperCount,
    Finset.sum_Ico_eq_sub _ (Nat.sub_le m M), hamb, hcorrection, hcorrection]
  rw [Nat.cast_sub hM]
  simp only [finiteLengthLinearSum, finiteLengthSquareSum, finiteLengthRankRoundingModel]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]
  ring

/-- The exact finite-length local rank loses at most `3m²` against the cubic density. -/
theorem finiteLengthRankCount_le_density_add_three_mul_sq
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthRankCount rho eta n : ℝ) ≤
      (finiteLengthMultiplicity rho eta n : ℝ) ^ 3 *
          firstOrderRankDensity (finiteLengthDerivativeRatio rho eta) +
        3 * (finiteLengthMultiplicity rho eta n : ℝ) ^ 2 := by
  let m := finiteLengthMultiplicity rho eta n
  let beta := finiteLengthDerivativeRatio rho eta
  let M := finiteLengthDerivativeCap rho eta n
  let u : ℝ := M / m
  let v : ℝ := (m : ℝ)⁻¹
  have hmNat : 0 < m := finiteLengthMultiplicity_pos
    hrho hrhoOne heta haOne hn hbetaHalf
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hb0 : 0 ≤ beta := by
    dsimp only [beta]
    exact (automaticBeta_pos hrho hrhoOne (by linarith) haOne).le
  have hMReal : (M : ℝ) ≤ beta * m := by
    dsimp only [M, beta, m]
    unfold finiteLengthDerivativeCap
    exact Nat.floor_le (mul_nonneg hb0 (Nat.cast_nonneg _))
  have hMlt : beta * m < (M : ℝ) + 1 := by
    dsimp only [M, beta, m]
    unfold finiteLengthDerivativeCap
    exact Nat.lt_floor_add_one _
  have hMNat : M ≤ m := by
    dsimp only [M, m]
    exact finiteLengthDerivativeCap_le_multiplicity
      hrho hrhoOne heta haOne hn hbetaHalf
  have hu0 : 0 ≤ u := by unfold u; positivity
  have hub : u ≤ beta := by
    unfold u
    exact (div_le_iff₀ hm).2 (by simpa [mul_comm] using hMReal)
  have hbu : beta ≤ u + v := by
    unfold u v
    rw [show (M : ℝ) / m + (m : ℝ)⁻¹ = ((M : ℝ) + 1) / m by
      field_simp [ne_of_gt hm]]
    exact (le_div_iff₀ hm).2 (by linarith)
  have hv0 : 0 ≤ v := by unfold v; positivity
  have hv1 : v ≤ 1 := by
    unfold v
    rw [inv_le_one₀ hm]
    exact_mod_cast hmNat
  have hmodel := finiteLengthRankRoundingModel_le hu0 hub hbu hv0 hv1
    (hbetaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4))
  have hrankDensity : firstOrderRankDensity beta =
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 := by
    rw [firstOrderRankDensity, if_pos hbetaHalf]
  have hnormalized : firstOrderRankCubicUpperCount m M / (m : ℝ) ^ 3 ≤
      firstOrderRankDensity beta + 3 / m := by
    rw [finiteLengthRankCubicUpperCount_normalized_eq_model hmNat hMNat,
      hrankDensity]
    dsimp only [u, v] at hmodel ⊢
    simpa [div_eq_mul_inv] using hmodel
  have hmCube : 0 < (m : ℝ) ^ 3 := pow_pos hm 3
  have hupper : firstOrderRankCubicUpperCount m M ≤
      (m : ℝ) ^ 3 * (firstOrderRankDensity beta + 3 / m) := by
    simpa [mul_comm] using (div_le_iff₀ hmCube).mp hnormalized
  have hscale : (m : ℝ) ^ 3 * (firstOrderRankDensity beta + 3 / m) =
      (m : ℝ) ^ 3 * firstOrderRankDensity beta + 3 * (m : ℝ) ^ 2 := by
    field_simp [ne_of_gt hm]
  unfold finiteLengthRankCount
  calc
    (firstOrderRateRankCount m M : ℝ) ≤ firstOrderRankCubicUpperCount m M :=
      firstOrderRateRankCount_le_cubicUpperCount m M
    _ ≤ (m : ℝ) ^ 3 * (firstOrderRankDensity beta + 3 / m) := hupper
    _ = _ := hscale

private def finiteLengthSourceRoundingModel (z u c v : ℝ) : ℝ :=
  (z + v) * u * (u - v) / 2 - u * (u - v) * (2 * u - v) / 6 +
    u * ((z + v) * (c - u) - (c * (c - v) - u * (u - v)) / 2)

private theorem finiteLengthSourceRoundingModel_ge
    {z u c v beta : ℝ}
    (hz1 : 1 ≤ z) (hbz : beta ≤ z) (hbu : beta ≤ u) (hub : u ≤ beta + v)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hzc : z + v ≤ c) (hcz : c ≤ z + 2 * v) :
    beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
      finiteLengthSourceRoundingModel z u c v := by
  have hconcave : finiteLengthSourceRoundingModel z u (z + v) v ≤
      finiteLengthSourceRoundingModel z u c v := by
    have hid : finiteLengthSourceRoundingModel z u c v -
        finiteLengthSourceRoundingModel z u (z + v) v =
          u / 2 * (c - (z + v)) * (z + 2 * v - c) := by
      unfold finiteLengthSourceRoundingModel
      ring
    rw [← sub_nonneg, hid]
    positivity
  have hleft : beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
      finiteLengthSourceRoundingModel z u (z + v) v := by
    have hquad : 0 ≤
        (u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2 := by
      nlinarith [sq_nonneg ((u - z) + (beta - z)), sq_nonneg (u - z),
        sq_nonneg (beta - z)]
    have hbase : beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
        u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6 := by
      have hid :
          (u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6) -
              (beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6) =
            (u - beta) / 6 *
              ((u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2) := by ring
      have hfac : 0 ≤ (u - beta) / 6 :=
        div_nonneg (sub_nonneg.mpr hbu) (by norm_num)
      nlinarith [mul_nonneg hfac hquad]
    have huz : u ≤ z + v := hub.trans (by
      simpa only [add_comm] using add_le_add_right hbz v)
    have hbracket : 0 ≤ z - u / 2 + v / 3 := by nlinarith
    have hround : 0 ≤ v * u * (z - u / 2 + v / 3) := by positivity
    have hid : finiteLengthSourceRoundingModel z u (z + v) v =
        (u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6) +
          v * u * (z - u / 2 + v / 3) := by
      unfold finiteLengthSourceRoundingModel
      ring
    rw [hid]
    linarith
  exact hleft.trans hconcave

private def finiteLengthSourceLowerCount (R a : ℝ) (m M L : ℕ) : ℝ :=
  ∑ t ∈ Finset.range L, (min t M : ℕ) * (m * a - R * t)

private theorem finiteLengthSourceLowerCount_normalized_eq_model
    {R z : ℝ} {m M L : ℕ} (hm : 0 < m) (hML : M ≤ L) :
    finiteLengthSourceLowerCount R (R * (z + (m : ℝ)⁻¹)) m M L / (m : ℝ) ^ 3 =
      R * finiteLengthSourceRoundingModel z ((M : ℝ) / m) ((L : ℝ) / m)
        ((m : ℝ)⁻¹) := by
  have hsplit :
      finiteLengthSourceLowerCount R (R * (z + (m : ℝ)⁻¹)) m M L =
        (R * (z + (m : ℝ)⁻¹)) * m * finiteLengthLinearSum M -
          R * finiteLengthSquareSum M +
          M * ((R * (z + (m : ℝ)⁻¹)) * m * (L - M) -
            R * (finiteLengthLinearSum L - finiteLengthLinearSum M)) := by
    rw [finiteLengthSourceLowerCount, ← Finset.sum_range_add_sum_Ico _ hML]
    have hfirst :
        (∑ t ∈ Finset.range M,
            (min t M : ℕ) * (m * (R * (z + (m : ℝ)⁻¹)) - R * t)) =
          (R * (z + (m : ℝ)⁻¹)) * m * finiteLengthLinearSum M -
            R * finiteLengthSquareSum M := by
      calc
        _ = ∑ t ∈ Finset.range M,
            ((t : ℝ) * (m * (R * (z + (m : ℝ)⁻¹)) - R * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [min_eq_left (Finset.mem_range.mp ht).le]
        _ = ∑ t ∈ Finset.range M,
            ((R * (z + (m : ℝ)⁻¹)) * m * (t : ℝ) - R * (t : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro t _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            finiteLength_sum_range_cast, finiteLength_sum_range_sq_cast]
    have htail :
        (∑ t ∈ Finset.Ico M L,
            (min t M : ℕ) * (m * (R * (z + (m : ℝ)⁻¹)) - R * t)) =
          M * ((R * (z + (m : ℝ)⁻¹)) * m * (L - M) -
            R * (finiteLengthLinearSum L - finiteLengthLinearSum M)) := by
      calc
        _ = ∑ t ∈ Finset.Ico M L,
            ((M : ℝ) * (m * (R * (z + (m : ℝ)⁻¹)) - R * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [min_eq_right (Finset.mem_Ico.mp ht).1]
        _ = _ := by
          have hsum (q : ℕ) :
              (∑ t ∈ Finset.range q,
                ((m : ℝ) * (R * (z + (m : ℝ)⁻¹)) - R * t)) =
                q * (m * (R * (z + (m : ℝ)⁻¹))) -
                  R * finiteLengthLinearSum q := by
            induction q with
            | zero => simp [finiteLengthLinearSum]
            | succ q ih =>
                rw [Finset.sum_range_succ, ih]
                simp only [finiteLengthLinearSum]
                push_cast
                ring
          rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ hML, hsum, hsum]
          ring
    exact congrArg₂ (fun x y : ℝ ↦ x + y) hfirst htail
  rw [hsplit]
  simp only [finiteLengthLinearSum, finiteLengthSquareSum, finiteLengthSourceRoundingModel]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]

private theorem finiteLength_shiftedSourceLowerCount_eq
    {R a : ℝ} {m M L : ℕ} (hm : 0 < m) :
    finiteLengthSourceLowerCount R (a + R / m) m (M + 1) (L + 2) =
      ∑ t ∈ Finset.range (L + 1),
        (min t M + 1 : ℕ) * (m * a - R * t) := by
  rw [finiteLengthSourceLowerCount, Finset.sum_range_succ']
  rw [show min 0 (M + 1) = 0 by omega]
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro t _
  rw [show min (t + 1) (M + 1) = min t M + 1 by omega]
  push_cast
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]
  ring

/-- The rounded finite-length source count dominates its exact continuous density. -/
theorem finiteLengthSourceDensity_mul_cube_le_sourceCount
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthMultiplicity rho eta n : ℝ) ^ 3 *
        firstOrderSourceDensity (finiteLengthRate rho n)
          (finiteLengthCertifiedAgreement rho eta) (finiteLengthDerivativeRatio rho eta) ≤
      finiteLengthSourceCount rho eta n := by
  let R := finiteLengthRate rho n
  let a := finiteLengthCertifiedAgreement rho eta
  let beta := finiteLengthDerivativeRatio rho eta
  let m := finiteLengthMultiplicity rho eta n
  let M := finiteLengthDerivativeCap rho eta n
  let mu := finiteLengthJetDegree rho eta n
  let L := ⌊m * a / R⌋₊
  let z := a / R
  let u : ℝ := (M + 1 : ℕ) / m
  let c : ℝ := (L + 2 : ℕ) / m
  let v : ℝ := (m : ℝ)⁻¹
  let Q : ℝ := ∑ t ∈ Finset.range (L + 1),
    (min t M + 1 : ℕ) * (m * a - R * t)
  have hR : 0 < R := finiteLengthRate_pos hrho hn
  have hmNat : 0 < m := finiteLengthMultiplicity_pos
    hrho hrhoOne heta haOne hn hbetaHalf
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hmCube : 0 < (m : ℝ) ^ 3 := pow_pos hm 3
  have ha0 : 0 < a := hrho.trans
    (rho_lt_automaticAgreement hrho hrhoOne (by linarith))
  have hb0 : 0 ≤ beta := by
    dsimp only [beta]
    exact (automaticBeta_pos hrho hrhoOne (by linarith) haOne).le
  have hbetaCutFixed : beta < a / rho := by
    dsimp only [beta, a]
    exact automaticBeta_lt_agreement_div_rate hrho hrhoOne (by linarith) haOne
  have hRlt : R < rho := by
    dsimp only [R]
    exact finiteLengthRate_lt_rate (length_pos_of_two_le_rate_mul_length hn)
  have hbz : beta < z := hbetaCutFixed.trans_le
    (div_le_div_of_nonneg_left ha0.le hR hRlt.le)
  have hMReal : (M : ℝ) ≤ beta * m := by
    dsimp only [M, beta, m]
    unfold finiteLengthDerivativeCap
    exact Nat.floor_le (mul_nonneg hb0 (Nat.cast_nonneg _))
  have hMlt : beta * m < (M : ℝ) + 1 := by
    dsimp only [M, beta, m]
    unfold finiteLengthDerivativeCap
    exact Nat.lt_floor_add_one _
  have hmulCutoff : beta * m ≤ m * a / R := by
    have := mul_le_mul_of_nonneg_right hbz.le (Nat.cast_nonneg m)
    dsimp only [z] at this
    calc
      beta * (m : ℝ) ≤ (a / R) * m := this
      _ = (m : ℝ) * a / R := by ring
  have hML : M ≤ L := by
    dsimp only [M, L]
    unfold finiteLengthDerivativeCap
    exact Nat.floor_le_floor hmulCutoff
  have hcutoff0 : 0 ≤ (m : ℝ) * a / R := by positivity
  have hLReal : (L : ℝ) ≤ m * a / R := by
    unfold L
    exact Nat.floor_le hcutoff0
  have hLlt : (m : ℝ) * a / R < (L : ℝ) + 1 := by
    unfold L
    exact Nat.lt_floor_add_one _
  have hLmu : L ≤ mu := by
    dsimp only [mu, L, m, a, R]
    unfold finiteLengthJetDegree
    exact_mod_cast hLReal.trans (Nat.le_ceil _)
  have hQle : Q ≤ finiteLengthSourceCount rho eta n := by
    unfold finiteLengthSourceCount
    change Q ≤ ∑ t ∈ Finset.range (mu + 1),
      (min t M + 1 : ℕ) * max (m * a - R * t) 0
    dsimp only [Q]
    calc
      (∑ t ∈ Finset.range (L + 1),
          (min t M + 1 : ℕ) * (m * a - R * t)) =
          ∑ t ∈ Finset.range (L + 1),
            (min t M + 1 : ℕ) * max (m * a - R * t) 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [max_eq_left]
        have htL : (t : ℝ) ≤ L := by
          have htNat : t < L + 1 := Finset.mem_range.mp ht
          have : t ≤ L := by omega
          exact_mod_cast this
        have htCutoff := htL.trans hLReal
        have := mul_le_mul_of_nonneg_left htCutoff hR.le
        field_simp [ne_of_gt hR] at this ⊢
        nlinarith
      _ ≤ ∑ t ∈ Finset.range (mu + 1),
            (min t M + 1 : ℕ) * max (m * a - R * t) 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (Nat.add_le_add_right hLmu 1)
        · intro t _ _
          positivity
  have hshift : finiteLengthSourceLowerCount R (a + R / m) m (M + 1) (L + 2) = Q :=
    finiteLength_shiftedSourceLowerCount_eq hmNat
  have harg : R * (z + (m : ℝ)⁻¹) = a + R / m := by
    dsimp only [z]
    field_simp [ne_of_gt hR, ne_of_gt hm]
  have hnormalized : Q / (m : ℝ) ^ 3 =
      R * finiteLengthSourceRoundingModel z u c v := by
    have h := finiteLengthSourceLowerCount_normalized_eq_model
      (R := R) (z := z) (m := m) (M := M + 1) (L := L + 2) hmNat (by omega)
    rw [harg, hshift] at h
    exact h
  have hz1 : 1 ≤ z := by
    dsimp only [z]
    apply (le_div_iff₀ hR).2
    have hfixed : rho < a := by
      dsimp only [a, finiteLengthCertifiedAgreement]
      exact rho_lt_automaticAgreement hrho hrhoOne (by linarith)
    simpa only [one_mul] using (hRlt.trans hfixed).le
  have hbu : beta ≤ u := by
    dsimp only [u]
    exact (le_div_iff₀ hm).2 (by norm_num at hMlt ⊢; linarith)
  have hub : u ≤ beta + v := by
    dsimp only [u, v]
    rw [show beta + (m : ℝ)⁻¹ = (beta * m + 1) / m by
      field_simp [ne_of_gt hm]]
    exact (div_le_div_iff_of_pos_right hm).2 (by norm_num; linarith)
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp only [v]
    rw [inv_le_one₀ hm]
    exact_mod_cast hmNat
  have hzc : z + v ≤ c := by
    dsimp only [z, v, c]
    apply (le_div_iff₀ hm).2
    have : (m : ℝ) * (a / R + (m : ℝ)⁻¹) = m * a / R + 1 := by
      field_simp [ne_of_gt hm]
    rw [mul_comm, this]
    push_cast
    linarith
  have hcz : c ≤ z + 2 * v := by
    dsimp only [z, v, c]
    apply (div_le_iff₀ hm).2
    have : (m : ℝ) * (a / R + 2 * (m : ℝ)⁻¹) = m * a / R + 2 := by
      field_simp [ne_of_gt hm]
    rw [mul_comm, this]
    push_cast
    linarith
  have hmodel := finiteLengthSourceRoundingModel_ge hz1 hbz.le hbu hub hu0 hv0 hv1 hzc hcz
  have hdensity : firstOrderSourceDensity R a beta =
      R * (beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6) := by
    unfold firstOrderSourceDensity
    dsimp only [z]
    field_simp [ne_of_gt hR]
  have hdensityNorm : firstOrderSourceDensity R a beta ≤ Q / (m : ℝ) ^ 3 := by
    rw [hdensity, hnormalized]
    exact mul_le_mul_of_nonneg_left hmodel hR.le
  have hdensityQ : (m : ℝ) ^ 3 * firstOrderSourceDensity R a beta ≤ Q := by
    have := (le_div_iff₀ hmCube).mp hdensityNorm
    nlinarith
  exact hdensityQ.trans hQle

/-- The literal ceiling choice absorbs the exact rank-rounding loss. -/
theorem finiteLength_count_gap
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    3 * (finiteLengthMultiplicity rho eta n : ℝ) ^ 3 *
        finiteLengthDensityMargin rho eta n / 4 ≤
      finiteLengthSourceCount rho eta n - finiteLengthRankCount rho eta n := by
  let m := finiteLengthMultiplicity rho eta n
  let delta := finiteLengthDensityMargin rho eta n
  let crank := finiteLengthRankRoundingConstant rho eta
  let beta := finiteLengthDerivativeRatio rho eta
  have hmNat : 0 < m := finiteLengthMultiplicity_pos
    hrho hrhoOne heta haOne hn hbetaHalf
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hdelta : 0 < delta := finiteLengthDensityMargin_pos
    hrho hrhoOne heta haOne hn hbetaHalf
  have hceil : 4 * crank / delta ≤ (m : ℝ) := by
    dsimp only [m, crank, delta]
    unfold finiteLengthMultiplicity
    exact Nat.le_ceil _
  have hcrank3 : 3 ≤ crank := by
    have hb : 0 ≤ finiteLengthDerivativeRatio rho eta := by
      unfold finiteLengthDerivativeRatio
      exact (automaticBeta_pos hrho hrhoOne (by linarith) haOne).le
    change 3 ≤ 2 * finiteLengthDerivativeRatio rho eta + 3
    linarith
  have habsorb : 4 * crank ≤ (m : ℝ) * delta := by
    exact (div_le_iff₀ hdelta).mp (by simpa [mul_comm] using hceil)
  have hround : crank * (m : ℝ) ^ 2 ≤
      (m : ℝ) ^ 3 * delta / 4 := by
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ))
      (sub_nonneg.mpr habsorb)]
  have hsource := finiteLengthSourceDensity_mul_cube_le_sourceCount
    hrho hrhoOne heta haOne hn hbetaHalf
  have hrank := finiteLengthRankCount_le_density_add_three_mul_sq
    hrho hrhoOne heta haOne hn hbetaHalf
  have hrank' : (finiteLengthRankCount rho eta n : ℝ) ≤
      (m : ℝ) ^ 3 * firstOrderRankDensity beta + crank * (m : ℝ) ^ 2 := by
    dsimp only [m, beta] at hrank ⊢
    exact hrank.trans (by gcongr)
  dsimp only [delta, finiteLengthDensityMargin, m, beta] at hround hsource hrank' ⊢
  nlinarith

/-- A coarse bound on the exact local-rank count, sufficient for the height estimate. -/
theorem finiteLengthRankCount_le_two_mul_cube
    {rho eta : ℝ} {n : ℕ}
    (hm : 0 < finiteLengthMultiplicity rho eta n)
    (hM : finiteLengthDerivativeCap rho eta n ≤ finiteLengthMultiplicity rho eta n) :
    finiteLengthRankCount rho eta n ≤
      2 * finiteLengthMultiplicity rho eta n ^ 3 := by
  let m := finiteLengthMultiplicity rho eta n
  let M := finiteLengthDerivativeCap rho eta n
  have hone : m + 1 ≤ 2 * m := by omega
  unfold finiteLengthRankCount firstOrderRateRankCount
  calc
    (∑ s ∈ Finset.range m,
        ((s + 1) * (M + 1) -
          (2 * s + 1 - m) * (s + M + 1 - m))) ≤
        ∑ _s ∈ Finset.range m, m * (m + 1) := by
      apply Finset.sum_le_sum
      intro s hs
      exact (Nat.sub_le _ _).trans (Nat.mul_le_mul
        (Finset.mem_range.mp hs) (Nat.add_le_add_right hM 1))
    _ = m * (m * (m + 1)) := by simp
    _ ≤ m * (m * (2 * m)) := by gcongr
    _ = 2 * m ^ 3 := by ring

/-- Compatibility form of the height bound with an explicit finite count-gap premise. -/
theorem finiteLengthChallengeHeight_le_inv_slack_sq_of_count_gap
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hgap : 3 * (finiteLengthMultiplicity rho eta n : ℝ) ^ 3 *
        finiteLengthDensityMargin rho eta n / 4 ≤
      finiteLengthSourceCount rho eta n - finiteLengthRankCount rho eta n) :
    (finiteLengthChallengeHeight rho eta n : ℝ) ≤
      finiteLengthHeightBoundConstant rho / finiteLengthSlack eta n ^ 2 := by
  let m := finiteLengthMultiplicity rho eta n
  let B := finiteLengthJetDegree rho eta n
  let R := finiteLengthRankCount rho eta n
  let N := finiteLengthSourceCount rho eta n
  let c := automaticSurplusSlope rho
  let cB := finiteLengthJetBoundConstant rho
  let s := finiteLengthSlack eta n
  have hmNat : 0 < m := finiteLengthMultiplicity_pos
    hrho hrhoOne heta haOne hn hbetaHalf
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hc : 0 < c := automaticSurplusSlope_pos hrho hrhoOne
  have hs : 0 < s := finiteLengthSlack_pos heta
    (length_pos_of_two_le_rate_mul_length hn)
  have hsOne : s ≤ 1 :=
    (finiteLengthSlack_lt_one_of_rate hrho hrhoOne haOne hn).le
  have hdelta : c * s ≤ finiteLengthDensityMargin rho eta n :=
    automaticSurplusSlope_mul_finiteLengthSlack_le_margin
      hrho hrhoOne heta haOne hn hbetaHalf
  have hgapLower : 3 * (m : ℝ) ^ 3 * (c * s) / 4 ≤ N - R := by
    dsimp only [m, N, R, c, s] at hgap ⊢
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdelta (by positivity)) (by norm_num)).trans hgap
  have hgapPos : 0 < N - R := by
    exact (by positivity : 0 < 3 * (m : ℝ) ^ 3 * (c * s) / 4).trans_le hgapLower
  have hM : finiteLengthDerivativeCap rho eta n ≤ m :=
    finiteLengthDerivativeCap_le_multiplicity
      hrho hrhoOne heta haOne hn hbetaHalf
  have hR : (R : ℝ) ≤ 2 * (m : ℝ) ^ 3 := by
    exact_mod_cast finiteLengthRankCount_le_two_mul_cube hmNat hM
  have hB : (B : ℝ) ≤ cB / s := by
    exact finiteLengthJetDegree_le_inv_slack
      hrho hrhoOne heta haOne hn hbetaHalf
  have hcB : 0 ≤ cB := by
    dsimp only [cB]
    unfold finiteLengthJetBoundConstant finiteLengthMultiplicityBoundConstant
    positivity
  have hnum : (R : ℝ) * B ≤ 2 * (m : ℝ) ^ 3 * (cB / s) := by
    gcongr
  have hquot : (R : ℝ) * B / (N - R) ≤ 8 * cB / (3 * c * s ^ 2) := by
    calc
      (R : ℝ) * B / (N - R) ≤
          (2 * (m : ℝ) ^ 3 * (cB / s)) / (N - R) := by
        exact div_le_div_of_nonneg_right hnum hgapPos.le
      _ ≤
          (2 * (m : ℝ) ^ 3 * (cB / s)) /
            (3 * (m : ℝ) ^ 3 * (c * s) / 4) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hgapLower
      _ = 8 * cB / (3 * c * s ^ 2) := by
        field_simp [ne_of_gt hm, ne_of_gt hc, ne_of_gt hs]
        ring
  have hq0 : 0 ≤ (R : ℝ) * B / (N - R) := by positivity
  have hheight : (finiteLengthChallengeHeight rho eta n : ℝ) ≤
      1 + (R : ℝ) * B / (N - R) := by
    unfold finiteLengthChallengeHeight
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith
    · exact (Nat.floor_le hq0).trans (by linarith)
  have hK : 0 ≤ 8 * cB / (3 * c) := by positivity
  calc
    (finiteLengthChallengeHeight rho eta n : ℝ) ≤
        1 + (R : ℝ) * B / (N - R) := hheight
    _ ≤ 1 + 8 * cB / (3 * c * s ^ 2) := by linarith
    _ = 1 + (8 * cB / (3 * c)) / s ^ 2 := by ring
    _ ≤ (1 + 8 * cB / (3 * c)) / s ^ 2 := by
      have hsSq : s ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hsOne)]
      have hone : 1 ≤ 1 / s ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hs)]
        simpa using hsSq
      calc
        1 + (8 * cB / (3 * c)) / s ^ 2 ≤
            1 / s ^ 2 + (8 * cB / (3 * c)) / s ^ 2 := by gcongr
        _ = (1 + 8 * cB / (3 * c)) / s ^ 2 := by ring
    _ = finiteLengthHeightBoundConstant rho / s ^ 2 := by rfl

/-- The literal `m`, `M`, and `B` selectors share one inverse-slack envelope. -/
theorem finiteLength_multiplicity_derivativeCap_jetDegree_bounds
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthMultiplicity rho eta n : ℝ) ≤
        finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n ∧
      (finiteLengthDerivativeCap rho eta n : ℝ) ≤
        finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n ∧
      (finiteLengthJetDegree rho eta n : ℝ) ≤
        finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n := by
  have hs := finiteLengthSlack_pos heta (length_pos_of_two_le_rate_mul_length hn)
  have hcm : finiteLengthMultiplicityBoundConstant rho ≤
      finiteLengthParameterBoundConstant rho := by
    unfold finiteLengthParameterBoundConstant
    exact le_max_of_le_right (le_max_left _ _)
  have hcB : finiteLengthJetBoundConstant rho ≤
      finiteLengthParameterBoundConstant rho := by
    unfold finiteLengthParameterBoundConstant
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hcmDiv : finiteLengthMultiplicityBoundConstant rho /
      finiteLengthSlack eta n ≤ finiteLengthParameterBoundConstant rho /
        finiteLengthSlack eta n := div_le_div_of_nonneg_right hcm hs.le
  have hcBDiv : finiteLengthJetBoundConstant rho /
      finiteLengthSlack eta n ≤ finiteLengthParameterBoundConstant rho /
        finiteLengthSlack eta n := div_le_div_of_nonneg_right hcB hs.le
  exact ⟨(finiteLengthMultiplicity_le_inv_slack
      hrho hrhoOne heta haOne hn hbetaHalf).trans hcmDiv,
    (finiteLengthDerivativeCap_le_inv_slack
      hrho hrhoOne heta haOne hn hbetaHalf).trans hcmDiv,
    (finiteLengthJetDegree_le_inv_slack
      hrho hrhoOne heta haOne hn hbetaHalf).trans hcBDiv⟩

/-- Compatibility form of the common height bound with an explicit finite count-gap premise. -/
theorem finiteLengthChallengeHeight_le_common_inv_slack_sq_of_count_gap
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2)
    (hgap : 3 * (finiteLengthMultiplicity rho eta n : ℝ) ^ 3 *
        finiteLengthDensityMargin rho eta n / 4 ≤
      finiteLengthSourceCount rho eta n - finiteLengthRankCount rho eta n) :
    (finiteLengthChallengeHeight rho eta n : ℝ) ≤
      finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n ^ 2 := by
  have hsSq : 0 ≤ finiteLengthSlack eta n ^ 2 := sq_nonneg _
  have hcH : finiteLengthHeightBoundConstant rho ≤
      finiteLengthParameterBoundConstant rho := by
    unfold finiteLengthParameterBoundConstant
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  exact (finiteLengthChallengeHeight_le_inv_slack_sq_of_count_gap
    hrho hrhoOne heta haOne hn hbetaHalf hgap).trans
      (div_le_div_of_nonneg_right hcH hsSq)

/-- The literal challenge height has inverse-square finite-length-slack size, with the exact
floor quotient and `max 1` endpoint. -/
theorem finiteLengthChallengeHeight_le_inv_slack_sq
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthChallengeHeight rho eta n : ℝ) ≤
      finiteLengthHeightBoundConstant rho / finiteLengthSlack eta n ^ 2 := by
  exact finiteLengthChallengeHeight_le_inv_slack_sq_of_count_gap
    hrho hrhoOne heta haOne hn hbetaHalf
      (finiteLength_count_gap hrho hrhoOne heta haOne hn hbetaHalf)

/-- The common finite-length parameter constant also dominates the exact challenge height. -/
theorem finiteLengthChallengeHeight_le_common_inv_slack_sq
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthChallengeHeight rho eta n : ℝ) ≤
      finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n ^ 2 := by
  exact finiteLengthChallengeHeight_le_common_inv_slack_sq_of_count_gap
    hrho hrhoOne heta haOne hn hbetaHalf
      (finiteLength_count_gap hrho hrhoOne heta haOne hn hbetaHalf)

end

end ReedSolomon.FirstOrder
