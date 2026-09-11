/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.LowRateFiniteLength

/-! # Rate-only bounds for the low-rate finite-length selectors -/

@[expose] public section

namespace ReedSolomon.FirstOrder

open ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- Literal low-rate challenge height with the exact floor and `max 1` endpoint. -/
def lowRateFiniteLengthChallengeHeight (rho eta : ℝ) (n : ℕ) : ℕ :=
  max 1 ⌊(lowRateFiniteLengthRankCount rho eta n : ℝ) *
    lowRateFiniteLengthJetDegree rho eta n /
      (lowRateFiniteLengthSourceCount rho eta n - lowRateFiniteLengthRankCount rho eta n)⌋₊

def lowRateMultiplicityBoundConstant (rho : ℝ) : ℝ :=
  1 + 4 * lowRateFiniteLengthRankRoundingConstant rho / lowRateFiniteLengthSlope rho

def lowRateDerivativeCapBoundConstant (rho : ℝ) : ℝ :=
  firstOrderLowRateBeta rho * lowRateMultiplicityBoundConstant rho

def lowRateJetBoundConstant (rho : ℝ) : ℝ :=
  2 * lowRateMultiplicityBoundConstant rho / rho + 1

def lowRateRankBoundConstant (rho : ℝ) : ℝ :=
  firstOrderRankDensity (firstOrderLowRateBeta rho) +
    lowRateFiniteLengthRankRoundingConstant rho

def lowRateHeightBoundConstant (rho : ℝ) : ℝ :=
  1 + 4 * lowRateRankBoundConstant rho * lowRateJetBoundConstant rho /
    (3 * lowRateFiniteLengthSlope rho)

def lowRateParameterBoundConstant (rho : ℝ) : ℝ :=
  max 1 (max (lowRateMultiplicityBoundConstant rho)
    (max (lowRateDerivativeCapBoundConstant rho)
      (max (lowRateJetBoundConstant rho) (lowRateHeightBoundConstant rho))))

theorem one_le_lowRateParameterBoundConstant (rho : ℝ) :
    1 ≤ lowRateParameterBoundConstant rho := le_max_left _ _

theorem lowRateFiniteLengthSlack_lt_one
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    finiteLengthSlack eta n < 1 := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast length_pos_of_two_le_rate_mul_length hn
  have hinv : 1 / (n : ℝ) ≤ rho / 2 := by
    rw [div_le_iff₀ hnPos]
    nlinarith
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
  have hthreshold := rate_lt_firstOrderLowRateThreshold hrho hrhoOne hregime
  unfold finiteLengthSlack
  linarith

theorem lowRateFiniteLengthMultiplicity_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthMultiplicity rho eta n : ℝ) ≤
      lowRateMultiplicityBoundConstant rho / finiteLengthSlack eta n := by
  let c := lowRateFiniteLengthSlope rho
  let s := finiteLengthSlack eta n
  let delta := lowRateFiniteLengthDensityMargin rho eta n
  let crank := lowRateFiniteLengthRankRoundingConstant rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  have hc : 0 < c := lowRateFiniteLengthSlope_pos hrho hrhoOne hlow
  have hs : 0 < s := finiteLengthSlack_pos heta (length_pos_of_two_le_rate_mul_length hn)
  have hsOne : s ≤ 1 := (lowRateFiniteLengthSlack_lt_one hrho hrhoOne hlow haOne hn).le
  have hdelta : c * s ≤ delta :=
    lowRateFiniteLengthSlope_mul_slack_le_margin hrho hrhoOne hlow heta haOne hn
  have hdeltaPos : 0 < delta := (mul_pos hc hs).trans_le hdelta
  have hcrank0 : 0 ≤ crank := by
    dsimp only [crank, lowRateFiniteLengthRankRoundingConstant]
    positivity [firstOrderLowRateBeta_pos hrho]
  have hx : 4 * crank / delta ≤ 4 * crank / (c * s) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hcrank0) (mul_pos hc hs) hdelta
  have hm : (m : ℝ) < 4 * crank / delta + 1 := by
    dsimp only [m, crank, delta]
    unfold lowRateFiniteLengthMultiplicity
    exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hcrank0) hdeltaPos.le)
  calc
    (m : ℝ) ≤ 4 * crank / (c * s) + 1 := by linarith
    _ = (4 * crank / c + s) / s := by field_simp [ne_of_gt hc, ne_of_gt hs]
    _ ≤ (4 * crank / c + 1) / s := by gcongr
    _ = lowRateMultiplicityBoundConstant rho / s := by
      dsimp only [c]
      rw [lowRateMultiplicityBoundConstant]
      ring

theorem lowRateFiniteLengthDerivativeCap_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthDerivativeCap rho eta n : ℝ) ≤
      lowRateDerivativeCapBoundConstant rho / finiteLengthSlack eta n := by
  have hfloor : (lowRateFiniteLengthDerivativeCap rho eta n : ℝ) ≤
      firstOrderLowRateBeta rho * lowRateFiniteLengthMultiplicity rho eta n := by
    unfold lowRateFiniteLengthDerivativeCap
    exact Nat.floor_le (mul_nonneg (firstOrderLowRateBeta_pos hrho).le (Nat.cast_nonneg _))
  have hm := lowRateFiniteLengthMultiplicity_le_inv_slack
    hrho hrhoOne hlow heta haOne hn
  have hbeta := firstOrderLowRateBeta_pos hrho
  calc
    _ ≤ firstOrderLowRateBeta rho * lowRateFiniteLengthMultiplicity rho eta n := hfloor
    _ ≤ firstOrderLowRateBeta rho *
        (lowRateMultiplicityBoundConstant rho / finiteLengthSlack eta n) := by gcongr
    _ = lowRateDerivativeCapBoundConstant rho / finiteLengthSlack eta n := by
      rw [lowRateDerivativeCapBoundConstant]
      ring

theorem lowRateFiniteLengthDerivativeCap_le_jetDegree
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (_hrhoOne : rho < 1) (_hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    lowRateFiniteLengthDerivativeCap rho eta n ≤ lowRateFiniteLengthJetDegree rho eta n := by
  let R := finiteLengthRate rho n
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let beta := firstOrderLowRateBeta rho
  let m := lowRateFiniteLengthMultiplicity rho eta n
  have hR : 0 < R := finiteLengthRate_pos hrho hn
  have hRrho : R < rho := finiteLengthRate_lt_rate
    (length_pos_of_two_le_rate_mul_length hn)
  have ha0 : 0 < a := lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le
  have hTa : firstOrderLowRateThreshold rho ≤ a := by
    have h := lowRateFiniteLengthCertifiedAgreement_ge_half_slack
      (rho := rho) heta.le haOne.le
    dsimp only [a] at h ⊢
    linarith
  have hbcut : beta < a / R :=
    (firstOrderLowRateBeta_lt_threshold_div_rate hrho).trans_le
      ((div_le_div_of_nonneg_right hTa hrho.le).trans
        (div_le_div_of_nonneg_left ha0.le hR hRrho.le))
  have hfloor : (lowRateFiniteLengthDerivativeCap rho eta n : ℝ) ≤ beta * m := by
    dsimp only [beta, m]
    unfold lowRateFiniteLengthDerivativeCap
    exact Nat.floor_le (mul_nonneg (firstOrderLowRateBeta_pos hrho).le (Nat.cast_nonneg _))
  have hceil : (m : ℝ) * a / R ≤ (lowRateFiniteLengthJetDegree rho eta n : ℝ) := by
    dsimp only [m, a, R]
    unfold lowRateFiniteLengthJetDegree
    exact Nat.le_ceil _
  have hreal : (lowRateFiniteLengthDerivativeCap rho eta n : ℝ) ≤
      (lowRateFiniteLengthJetDegree rho eta n : ℝ) := hfloor.trans <| calc
    beta * (m : ℝ) ≤ (a / R) * m :=
      mul_le_mul_of_nonneg_right hbcut.le (Nat.cast_nonneg m)
    _ = (m : ℝ) * a / R := by ring
    _ ≤ lowRateFiniteLengthJetDegree rho eta n := hceil
  exact_mod_cast hreal

theorem lowRateFiniteLengthJetDegree_le_inv_slack
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthJetDegree rho eta n : ℝ) ≤
      lowRateJetBoundConstant rho / finiteLengthSlack eta n := by
  let s := finiteLengthSlack eta n
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let a := lowRateFiniteLengthCertifiedAgreement rho eta
  let R := finiteLengthRate rho n
  have hs : 0 < s := finiteLengthSlack_pos heta (length_pos_of_two_le_rate_mul_length hn)
  have hsOne : s ≤ 1 := (lowRateFiniteLengthSlack_lt_one hrho hrhoOne hlow haOne hn).le
  have hR : 0 < R := finiteLengthRate_pos hrho hn
  have hRhalf : rho / 2 ≤ R := half_rate_le_finiteLengthRate hrho hn
  have haOne' : a < 1 := lowRateFiniteLengthCertifiedAgreement_lt_one haOne
  have hm := lowRateFiniteLengthMultiplicity_le_inv_slack
    hrho hrhoOne hlow heta haOne hn
  have harg : (m : ℝ) * a / R ≤
      2 * lowRateMultiplicityBoundConstant rho / (rho * s) := by
    have hma : (m : ℝ) * a ≤ m := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      nlinarith
    have hratio : (m : ℝ) / R ≤ 2 * (m : ℝ) / rho := by
      rw [div_le_iff₀ hR]
      field_simp [ne_of_gt hrho]
      nlinarith
    calc
      (m : ℝ) * a / R ≤ (m : ℝ) / R := div_le_div_of_nonneg_right hma hR.le
      _ ≤ 2 * (m : ℝ) / rho := hratio
      _ ≤ 2 * (lowRateMultiplicityBoundConstant rho / s) / rho := by gcongr
      _ = 2 * lowRateMultiplicityBoundConstant rho / (rho * s) := by ring
  have hceil : (lowRateFiniteLengthJetDegree rho eta n : ℝ) <
      (m : ℝ) * a / R + 1 := by
    dsimp only [m, a, R]
    unfold lowRateFiniteLengthJetDegree
    exact Nat.ceil_lt_add_one (div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (lowRateFiniteLengthCertifiedAgreement_pos hrho heta.le).le)
      hR.le)
  calc
    _ ≤ 2 * lowRateMultiplicityBoundConstant rho / (rho * s) + 1 := by linarith
    _ = (2 * lowRateMultiplicityBoundConstant rho / rho + s) / s := by
      field_simp [ne_of_gt hrho, ne_of_gt hs]
    _ ≤ (2 * lowRateMultiplicityBoundConstant rho / rho + 1) / s := by gcongr
    _ = lowRateJetBoundConstant rho / s := by rfl

theorem lowRateFiniteLengthChallengeHeight_le_inv_slack_sq
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    (lowRateFiniteLengthChallengeHeight rho eta n : ℝ) ≤
      lowRateHeightBoundConstant rho / finiteLengthSlack eta n ^ 2 := by
  let s := finiteLengthSlack eta n
  let m := lowRateFiniteLengthMultiplicity rho eta n
  let B := lowRateFiniteLengthJetDegree rho eta n
  let r := lowRateFiniteLengthRankCount rho eta n
  let N := lowRateFiniteLengthSourceCount rho eta n
  let c := lowRateFiniteLengthSlope rho
  let cr := lowRateRankBoundConstant rho
  let cB := lowRateJetBoundConstant rho
  have hs : 0 < s := finiteLengthSlack_pos heta (length_pos_of_two_le_rate_mul_length hn)
  have hsOne : s ≤ 1 := (lowRateFiniteLengthSlack_lt_one hrho hrhoOne hlow haOne hn).le
  have hmNat : 0 < m := lowRateFiniteLengthMultiplicity_pos hrho hrhoOne hlow heta haOne hn
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hc : 0 < c := lowRateFiniteLengthSlope_pos hrho hrhoOne hlow
  have hregime := (firstOrderLowRateRegime_iff_lt_rateSwitch hrho.le).2 hlow
  have hrankDensity : 0 ≤ firstOrderRankDensity (firstOrderLowRateBeta rho) := by
    rw [firstOrderRankDensity, if_neg (not_le.mpr
      (half_lt_firstOrderLowRateBeta hrho hregime))]
    positivity [firstOrderLowRateBeta_pos hrho]
  have hcrank : 0 ≤ lowRateFiniteLengthRankRoundingConstant rho := by
    unfold lowRateFiniteLengthRankRoundingConstant
    positivity [firstOrderLowRateBeta_pos hrho]
  have hcr : 0 ≤ cr := by
    dsimp only [cr, lowRateRankBoundConstant]
    positivity
  have hcB : 0 ≤ cB := by
    dsimp only [cB, lowRateJetBoundConstant, lowRateMultiplicityBoundConstant,
      lowRateFiniteLengthRankRoundingConstant]
    positivity
  have hdelta := lowRateFiniteLengthSlope_mul_slack_le_margin
    hrho hrhoOne hlow heta haOne hn
  have hgap := lowRateFiniteLength_count_gap hrho hrhoOne hlow heta haOne hn
  have hgapLower : 3 * (m : ℝ) ^ 3 * (c * s) / 4 ≤ N - r := by
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdelta (by positivity)) (by norm_num)).trans hgap
  have hgapPos : 0 < N - r :=
    (by positivity : 0 < 3 * (m : ℝ) ^ 3 * (c * s) / 4).trans_le hgapLower
  have hrank := lowRateFiniteLengthRankCount_le_density_add_rounding
    (rho := rho) (eta := eta) (n := n) hrho
  have hr : (r : ℝ) ≤ cr * (m : ℝ) ^ 3 := by
    have hmSqCube : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr (show (1 : ℝ) ≤ m by
        exact_mod_cast hmNat))]
    dsimp only [r, cr, lowRateRankBoundConstant] at hrank ⊢
    nlinarith [mul_le_mul_of_nonneg_left hmSqCube hcrank]
  have hB : (B : ℝ) ≤ cB / s :=
    lowRateFiniteLengthJetDegree_le_inv_slack hrho hrhoOne hlow heta haOne hn
  have hquot : (r : ℝ) * B / (N - r) ≤ 4 * cr * cB / (3 * c * s ^ 2) := by
    calc
      (r : ℝ) * B / (N - r) ≤
          (cr * (m : ℝ) ^ 3 * (cB / s)) / (N - r) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul hr hB (Nat.cast_nonneg _) (by positivity)) hgapPos.le
      _ ≤ (cr * (m : ℝ) ^ 3 * (cB / s)) /
          (3 * (m : ℝ) ^ 3 * (c * s) / 4) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hgapLower
      _ = 4 * cr * cB / (3 * c * s ^ 2) := by
        field_simp [ne_of_gt hm, ne_of_gt hc, ne_of_gt hs]
  have hquot0 : 0 ≤ (r : ℝ) * B / (N - r) := by positivity
  have hheight : (lowRateFiniteLengthChallengeHeight rho eta n : ℝ) ≤
      1 + (r : ℝ) * B / (N - r) := by
    unfold lowRateFiniteLengthChallengeHeight
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith
    · exact (Nat.floor_le (by positivity)).trans (by linarith)
  calc
    _ ≤ 1 + 4 * cr * cB / (3 * c * s ^ 2) := hheight.trans (by linarith)
    _ = 1 + (4 * cr * cB / (3 * c)) / s ^ 2 := by ring
    _ ≤ (1 + 4 * cr * cB / (3 * c)) / s ^ 2 := by
      have hsSq : s ^ 2 ≤ 1 := pow_le_one₀ hs.le hsOne
      have hK : 0 ≤ 4 * cr * cB / (3 * c) := by positivity
      rw [le_div_iff₀ (sq_pos_of_pos hs)]
      calc
        (1 + 4 * cr * cB / (3 * c) / s ^ 2) * s ^ 2 =
            s ^ 2 + 4 * cr * cB / (3 * c) := by
          field_simp [ne_of_gt hs]
        _ ≤ 1 + 4 * cr * cB / (3 * c) := by
          simpa only [add_comm] using add_le_add_right hsSq (4 * cr * cB / (3 * c))
    _ = lowRateHeightBoundConstant rho / s ^ 2 := by rfl

theorem lowRateFiniteLength_parameter_bounds
    {rho eta : ℝ} {n : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (hlow : rho < firstOrderRateSwitch)
    (heta : 0 < eta) (haOne : firstOrderLowRateThreshold rho + eta < 1)
    (hn : (2 : ℝ) ≤ rho * n) :
    let C := lowRateParameterBoundConstant rho
    let s := finiteLengthSlack eta n
    (lowRateFiniteLengthMultiplicity rho eta n : ℝ) ≤ C / s ∧
      (lowRateFiniteLengthDerivativeCap rho eta n : ℝ) ≤ C / s ∧
      (lowRateFiniteLengthJetDegree rho eta n : ℝ) ≤ C / s ∧
      (lowRateFiniteLengthChallengeHeight rho eta n : ℝ) ≤ C / s ^ 2 := by
  dsimp only
  have hs := finiteLengthSlack_pos heta (length_pos_of_two_le_rate_mul_length hn)
  have hm := lowRateFiniteLengthMultiplicity_le_inv_slack hrho hrhoOne hlow heta haOne hn
  have hM := lowRateFiniteLengthDerivativeCap_le_inv_slack hrho hrhoOne hlow heta haOne hn
  have hB := lowRateFiniteLengthJetDegree_le_inv_slack hrho hrhoOne hlow heta haOne hn
  have hH := lowRateFiniteLengthChallengeHeight_le_inv_slack_sq
    hrho hrhoOne hlow heta haOne hn
  unfold lowRateParameterBoundConstant
  refine ⟨hm.trans (div_le_div_of_nonneg_right ?_ hs.le),
    hM.trans (div_le_div_of_nonneg_right ?_ hs.le),
    hB.trans (div_le_div_of_nonneg_right ?_ hs.le),
    hH.trans (div_le_div_of_nonneg_right ?_ (sq_nonneg _))⟩
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

end

end ReedSolomon.FirstOrder
