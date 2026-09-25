/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.AutomaticBounds
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthParameters

/-!
# Length-dependent first-order interpolation selectors

This file defines the finite-length interpolation selectors for a fixed rate `rho` and block
length `n`. The derivative ratio is selected at `rho`, while source density and jet degree use
the exact degree rate `rho - 1 / n`. The resulting selectors and counts have bounds in terms of
the finite-length slack `eta + 1 / n`.

The density and height bounds are stated on the branch where the derivative ratio is at most
`1 / 2`, so `firstOrderRankDensity` agrees with the cubic expression used by the rank estimate.

## Main statements

* `finiteLengthSlack_lt_one_of_threshold` gives a threshold-independent slack comparison.
* `finiteLengthDensityMargin_pos` and `finiteLength_count_gap` give a positive finite surplus.
* `finiteLengthMultiplicity_le_inv_slack` and `finiteLengthJetDegree_le_inv_slack` bound the
  literal interpolation parameters.
* `finiteLengthChallengeHeight_le_inv_slack_sq_of_count_gap` takes a finite surplus as a premise.
* `finiteLengthChallengeHeight_le_common_inv_slack_sq` bounds the exact challenge height.

## References

* [DKT26]
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
  automaticAgreement rho (firstOrderRateThreshold rho + eta)

/-- The derivative-degree ratio remains tuned at the fixed rate `rho`. -/
def finiteLengthDerivativeRatio (rho eta : ℝ) : ℝ :=
  automaticDerivativeRatio rho (firstOrderRateThreshold rho + eta)

/-- Exact finite-length density margin.  Only the source density sees `rho - 1 / n`. -/
def finiteLengthDensityMargin (rho eta : ℝ) (n : ℕ) : ℝ :=
  firstOrderSourceDensity (finiteLengthRate rho n)
      (finiteLengthCertifiedAgreement rho eta) (finiteLengthDerivativeRatio rho eta) -
    firstOrderRankDensity (finiteLengthDerivativeRatio rho eta)

/-- The finite rank-rounding coefficient `2 * beta + 3`. -/
def finiteLengthRankRoundingConstant (rho eta : ℝ) : ℝ :=
  2 * finiteLengthDerivativeRatio rho eta + 3

/-- Literal finite-length multiplicity selector. -/
def finiteLengthMultiplicity (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌈4 * finiteLengthRankRoundingConstant rho eta /
    finiteLengthDensityMargin rho eta n⌉₊

/-- Literal derivative cap `floor (beta * m)`.  In particular, zero is retained. -/
def finiteLengthDerivativeCap (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌊finiteLengthDerivativeRatio rho eta * finiteLengthMultiplicity rho eta n⌋₊

/-- The total jet degree selected from the certified agreement and the exact finite rate. -/
def finiteLengthJetDegree (rho eta : ℝ) (n : ℕ) : ℕ :=
  ⌈finiteLengthMultiplicity rho eta n * finiteLengthCertifiedAgreement rho eta /
    finiteLengthRate rho n⌉₊

/-- Exact source count at the length-dependent rate. -/
def finiteLengthSourceCount (rho eta : ℝ) (n : ℕ) : ℝ :=
  firstOrderSourceCount (finiteLengthRate rho n)
    (finiteLengthCertifiedAgreement rho eta) (finiteLengthMultiplicity rho eta n)
    (finiteLengthDerivativeCap rho eta n) (finiteLengthJetDegree rho eta n)

/-- Exact local-rank count for the length-dependent selector. -/
def finiteLengthRankCount (rho eta : ℝ) (n : ℕ) : ℕ :=
  firstOrderRankCount (finiteLengthMultiplicity rho eta n)
    (finiteLengthDerivativeCap rho eta n)

/-- Literal challenge height, with the exact natural floor and the `max 1` endpoint. -/
def finiteLengthChallengeHeight (rho eta : ℝ) (n : ℕ) : ℕ :=
  max 1 ⌊(finiteLengthRankCount rho eta n : ℝ) * finiteLengthJetDegree rho eta n /
    (finiteLengthSourceCount rho eta n - finiteLengthRankCount rho eta n)⌋₊

/-- The exact finite rate multiplied by the block length equals `rho * n - 1`. -/
theorem finiteLengthRate_eq {rho : ℝ} {n : ℕ} (hn : 0 < n) :
    finiteLengthRate rho n * n = rho * n - 1 := by
  unfold finiteLengthRate
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp

/-- The finite rate is at least half the fixed rate when `rho * n ≥ 2`. -/
theorem half_rate_le_finiteLengthRate {rho : ℝ} {n : ℕ}
    (hn : (2 : ℝ) ≤ rho * n) :
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

/-- The finite rate is positive when the rate-length product is at least two. -/
theorem finiteLengthRate_pos {rho : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hn : (2 : ℝ) ≤ rho * n) :
    0 < finiteLengthRate rho n := by
  exact (half_pos hrho).trans_le (half_rate_le_finiteLengthRate hn)

/-- A rate-length product of at least two forces positive block length. -/
theorem length_pos_of_two_le_rate_mul_length {rho : ℝ} {n : ℕ}
    (hn : (2 : ℝ) ≤ rho * n) : 0 < n := by
  by_contra h
  have hz : n = 0 := Nat.eq_zero_of_not_pos h
  subst n
  norm_num at hn

/-- The finite rate is strictly below the fixed rate at positive block length. -/
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
        automaticSurplus rho (firstOrderRateThreshold rho + eta) := by
  have hrank : firstOrderRankDensity (finiteLengthDerivativeRatio rho eta) =
      firstOrderRankCubicEnvelope (finiteLengthDerivativeRatio rho eta) := by
    rw [firstOrderRankDensity, ite_eq_left hbeta, firstOrderRankCubicEnvelope]
  rw [hrank]
  have hidentity := automatic_sourceDensity_sub_rankDensityEnvelope
    (rho := rho) (a := firstOrderRateThreshold rho + eta)
    hrho hrhoOne
  unfold finiteLengthCertifiedAgreement finiteLengthDerivativeRatio
  unfold automaticSourceDensity automaticRankDensityEnvelope at hidentity
  exact hidentity

/-- The exact length-dependent margin is at least a rate-only multiple of `eta + 1/n`. -/
theorem automaticSurplusSlope_mul_finiteLengthSlack_le_margin
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    automaticSurplusSlope rho * finiteLengthSlack eta n ≤
      finiteLengthDensityMargin rho eta n := by
  let a := finiteLengthCertifiedAgreement rho eta
  let beta := finiteLengthDerivativeRatio rho eta
  have ha : 0 < a := by
    have := rho_lt_automaticAgreement hrho hrhoOne
      (show firstOrderRateThreshold rho < firstOrderRateThreshold rho + eta by
        linarith)
    exact hrho.trans this
  have hb0 : 0 < beta := by
    exact automaticDerivativeRatio_pos hrhoOne haOne
  have hbcut : beta < a / rho := by
    exact automaticDerivativeRatio_lt_agreement_div_rate hrho hrhoOne (by linarith)
  have hgain := sourceDensity_gain_at_finiteLengthRate hrho hn ha hb0.le hbcut
  have hbase := automaticSurplusSlope_mul_eta_le hrho hrhoOne heta haOne
  have hbetaLower : 3 * automaticRateGap rho / 8 ≤ beta := by
    let a₀ := automaticAgreement rho (firstOrderRateThreshold rho + eta)
    have ha₀mid : a₀ ≤ (1 + firstOrderRateThreshold rho) / 2 := by
      dsimp only [a₀]
      rw [automaticAgreement_eq_min]
      exact min_le_right _ _
    have hden : 0 < 2 * (2 - rho) := by nlinarith
    dsimp only [beta, finiteLengthDerivativeRatio]
    unfold automaticDerivativeRatio firstOrderRateBeta
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

/-- Finite-length slack is below one when a threshold exceeds the rate and leaves room. -/
theorem finiteLengthSlack_lt_one_of_threshold
    {rho threshold eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hthreshold : rho < threshold)
    (haOne : threshold + eta < 1) (hn : (2 : ℝ) ≤ rho * n) :
    finiteLengthSlack eta n < 1 := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast length_pos_of_two_le_rate_mul_length hn
  have hinv : 1 / (n : ℝ) ≤ rho / 2 := by
    rw [div_le_iff₀ hn0]
    nlinarith
  unfold finiteLengthSlack
  linarith

/-- The finite-length slack is below one under the stated rate and length guards. -/
theorem finiteLengthSlack_lt_one_of_rate
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    finiteLengthSlack eta n < 1 := by
  exact finiteLengthSlack_lt_one_of_threshold hrho
    (rate_lt_firstOrderRateThreshold hrho hrhoOne) haOne hn

/-- The finite-length density margin is positive on the clean rank branch. -/
theorem finiteLengthDensityMargin_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    0 < finiteLengthDensityMargin rho eta n := by
  have hc := automaticSurplusSlope_pos hrho hrhoOne
  have hs : 0 < finiteLengthSlack eta n := finiteLengthSlack_pos heta
  exact (mul_pos hc hs).trans_le
    (automaticSurplusSlope_mul_finiteLengthSlack_le_margin
      hrho hrhoOne heta haOne hn hbetaHalf)

/-- The finite-length multiplicity is positive when the density margin is positive. -/
theorem finiteLengthMultiplicity_pos
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    0 < finiteLengthMultiplicity rho eta n := by
  unfold finiteLengthMultiplicity
  apply Nat.ceil_pos.mpr
  have hmargin := finiteLengthDensityMargin_pos
    hrho hrhoOne heta haOne hn hbetaHalf
  have hbeta0 : 0 < finiteLengthDerivativeRatio rho eta :=
    automaticDerivativeRatio_pos hrhoOne haOne
  unfold finiteLengthRankRoundingConstant
  positivity

/-- The literal multiplicity selector has inverse-slack size. -/
theorem finiteLengthMultiplicity_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
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
    exact finiteLengthSlack_pos heta
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
    have := automaticDerivativeRatio_pos hrhoOne haOne
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
    (hrhoOne : rho < 1)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    finiteLengthDerivativeCap rho eta n ≤ finiteLengthMultiplicity rho eta n := by
  have hb0 : 0 ≤ finiteLengthDerivativeRatio rho eta :=
    (automaticDerivativeRatio_pos hrhoOne haOne).le
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

/-- The derivative cap has the same inverse-slack bound as the multiplicity. -/
theorem finiteLengthDerivativeCap_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthDerivativeCap rho eta n : ℝ) ≤
      finiteLengthMultiplicityBoundConstant rho / finiteLengthSlack eta n := by
  exact (Nat.cast_le.mpr (finiteLengthDerivativeCap_le_multiplicity
    hrhoOne haOne hbetaHalf)).trans
      (finiteLengthMultiplicity_le_inv_slack
        hrho hrhoOne heta haOne hn hbetaHalf)

/-- The derivative floor lies below the total-degree ceiling, with no positivity assumption on
the floor itself. -/
theorem finiteLengthDerivativeCap_le_jetDegree
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (hn : (2 : ℝ) ≤ rho * n) :
    finiteLengthDerivativeCap rho eta n ≤ finiteLengthJetDegree rho eta n := by
  have hrn : 0 < finiteLengthRate rho n := finiteLengthRate_pos hrho hn
  have hbcutFixed : finiteLengthDerivativeRatio rho eta <
      finiteLengthCertifiedAgreement rho eta / rho :=
    automaticDerivativeRatio_lt_agreement_div_rate hrho hrhoOne (by linarith)
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
  exact natFloor_mul_le_natCeil_mul_div hbcut.le

/-- The literal total jet degree has inverse finite-length-slack size. -/
theorem finiteLengthJetDegree_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthJetDegree rho eta n : ℝ) ≤
      finiteLengthJetBoundConstant rho / finiteLengthSlack eta n := by
  let m := finiteLengthMultiplicity rho eta n
  let a := finiteLengthCertifiedAgreement rho eta
  let rn := finiteLengthRate rho n
  let s := finiteLengthSlack eta n
  let cm := finiteLengthMultiplicityBoundConstant rho
  have hrnHalf : rho / 2 ≤ rn := half_rate_le_finiteLengthRate hn
  have hrn : 0 < rn := finiteLengthRate_pos hrho hn
  have haOne' : a < 1 := automaticAgreement_lt_one haOne
  have hm := finiteLengthMultiplicity_le_inv_slack
    hrho hrhoOne heta haOne hn hbetaHalf
  have hs : 0 < s := by
    dsimp only [s]
    exact finiteLengthSlack_pos heta
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

/-! ## Exact finite count gap -/

/-- The exact finite-length local rank loses at most `3 m²` against the cubic density. -/
theorem finiteLengthRankCount_le_density_add_three_mul_sq
    {rho eta : ℝ} {n : ℕ}
    (hrhoOne : rho < 1) (haOne : firstOrderRateThreshold rho + eta < 1)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthRankCount rho eta n : ℝ) ≤
      (finiteLengthMultiplicity rho eta n : ℝ) ^ 3 *
          firstOrderRankDensity (finiteLengthDerivativeRatio rho eta) +
        3 * (finiteLengthMultiplicity rho eta n : ℝ) ^ 2 := by
  have hbeta0 : 0 ≤ finiteLengthDerivativeRatio rho eta := by
    unfold finiteLengthDerivativeRatio
    exact (automaticDerivativeRatio_pos hrhoOne haOne).le
  have hbeta34 : finiteLengthDerivativeRatio rho eta ≤ 3 / 4 :=
    hbetaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
  have hrankDensity : firstOrderRankDensity (finiteLengthDerivativeRatio rho eta) =
      finiteLengthDerivativeRatio rho eta / 2 -
        (finiteLengthDerivativeRatio rho eta) ^ 2 / 2 +
          (finiteLengthDerivativeRatio rho eta) ^ 3 / 3 := by
    rw [firstOrderRankDensity, ite_eq_left hbetaHalf]
  unfold finiteLengthRankCount finiteLengthDerivativeCap
  rw [hrankDensity]
  exact firstOrderRankCount_floor_le (finiteLengthMultiplicity rho eta n) hbeta0 hbeta34

/-- The rounded finite-length source count dominates its exact continuous density. -/
theorem finiteLengthSourceDensity_mul_cube_le_sourceCount
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (finiteLengthMultiplicity rho eta n : ℝ) ^ 3 *
        firstOrderSourceDensity (finiteLengthRate rho n)
          (finiteLengthCertifiedAgreement rho eta) (finiteLengthDerivativeRatio rho eta) ≤
      finiteLengthSourceCount rho eta n := by
  let rate := finiteLengthRate rho n
  let agreement := finiteLengthCertifiedAgreement rho eta
  let beta := finiteLengthDerivativeRatio rho eta
  let m := finiteLengthMultiplicity rho eta n
  let mu := finiteLengthJetDegree rho eta n
  have hrate : 0 < rate := by
    dsimp only [rate]
    exact finiteLengthRate_pos hrho hn
  have hrateLt : rate < rho := by
    dsimp only [rate]
    exact finiteLengthRate_lt_rate (length_pos_of_two_le_rate_mul_length hn)
  have hrhoAgreement : rho < agreement := by
    dsimp only [agreement, finiteLengthCertifiedAgreement]
    exact rho_lt_automaticAgreement hrho hrhoOne (by linarith)
  have hrateAgreement : rate ≤ agreement := hrateLt.le.trans hrhoAgreement.le
  have hagreement : 0 < agreement := hrho.trans hrhoAgreement
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta, finiteLengthDerivativeRatio]
    exact (automaticDerivativeRatio_pos hrhoOne haOne).le
  have hbetaCutFixed : beta < agreement / rho := by
    dsimp only [beta, agreement, finiteLengthDerivativeRatio,
      finiteLengthCertifiedAgreement]
    exact automaticDerivativeRatio_lt_agreement_div_rate hrho hrhoOne (by linarith)
  have hbetaCut : beta ≤ agreement / rate :=
    hbetaCutFixed.le.trans (div_le_div_of_nonneg_left hagreement.le hrate hrateLt.le)
  have hmu : ⌊m * agreement / rate⌋₊ ≤ mu := by
    dsimp only [mu, m, agreement, rate]
    unfold finiteLengthJetDegree
    exact Nat.floor_le_ceil _
  have hsource := cube_mul_sourceDensity_le_firstOrderSourceCount
    hrate hrateAgreement hbeta0 hbetaCut hmu
  simpa [firstOrderSourceDensity, finiteLengthSourceCount, finiteLengthDerivativeCap,
    rate, agreement, beta, m, mu] using hsource

/-- The literal ceiling choice absorbs the exact rank-rounding loss. -/
theorem finiteLength_count_gap
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
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
      exact (automaticDerivativeRatio_pos hrhoOne haOne).le
    change 3 ≤ 2 * finiteLengthDerivativeRatio rho eta + 3
    linarith
  have habsorb : 4 * crank ≤ (m : ℝ) * delta := by
    exact (div_le_iff₀ hdelta).mp (by simpa [mul_comm] using hceil)
  have hround : crank * (m : ℝ) ^ 2 ≤
      (m : ℝ) ^ 3 * delta / 4 := by
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ))
      (sub_nonneg.mpr habsorb)]
  have hsource := finiteLengthSourceDensity_mul_cube_le_sourceCount
    hrho hrhoOne heta haOne hn
  have hrank := finiteLengthRankCount_le_density_add_three_mul_sq
    (n := n) hrhoOne haOne hbetaHalf
  have hrank' : (finiteLengthRankCount rho eta n : ℝ) ≤
      (m : ℝ) ^ 3 * firstOrderRankDensity beta + crank * (m : ℝ) ^ 2 := by
    dsimp only [m, beta] at hrank ⊢
    exact hrank.trans (by gcongr)
  dsimp only [delta, finiteLengthDensityMargin, m, beta] at hround hsource hrank' ⊢
  nlinarith

/-- An explicit finite count gap bounds the exact challenge height by the inverse-square slack. -/
theorem finiteLengthChallengeHeight_le_inv_slack_sq_of_count_gap
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
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
      hrhoOne haOne hbetaHalf
  have hR : (R : ℝ) ≤ 2 * (m : ℝ) ^ 3 := by
    dsimp only [R, finiteLengthRankCount, m]
    exact_mod_cast firstOrderRankCount_le_two_mul_cube hmNat hM
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

/-- The selected multiplicity, derivative cap, and jet degree share one inverse-slack envelope. -/
theorem finiteLength_multiplicity_derivativeCap_jetDegree_bounds
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthMultiplicity rho eta n : ℝ) ≤
        finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n ∧
      (finiteLengthDerivativeCap rho eta n : ℝ) ≤
        finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n ∧
      (finiteLengthJetDegree rho eta n : ℝ) ≤
        finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n := by
  have hs := finiteLengthSlack_pos (eta := eta) (n := n) heta
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

/-- The literal challenge height has inverse-square finite-length-slack size, with the exact
floor quotient and `max 1` endpoint. -/
theorem finiteLengthChallengeHeight_le_inv_slack_sq
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
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
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n)
    (hbetaHalf : finiteLengthDerivativeRatio rho eta ≤ 1 / 2) :
    (finiteLengthChallengeHeight rho eta n : ℝ) ≤
      finiteLengthParameterBoundConstant rho / finiteLengthSlack eta n ^ 2 := by
  have hheight := finiteLengthChallengeHeight_le_inv_slack_sq
    hrho hrhoOne heta haOne hn hbetaHalf
  have hcH : finiteLengthHeightBoundConstant rho ≤
      finiteLengthParameterBoundConstant rho := by
    unfold finiteLengthParameterBoundConstant
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  exact hheight.trans (div_le_div_of_nonneg_right hcH (sq_nonneg _))

end

end ReedSolomon.FirstOrder
