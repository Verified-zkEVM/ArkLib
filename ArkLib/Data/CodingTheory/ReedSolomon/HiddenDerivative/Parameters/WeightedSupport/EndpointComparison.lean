/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.GCongr

/-!
# Exact endpoint comparison for the no-band support

The dimension lower bound has two useful terms. At high rates the cubic baseline contributes
`F`, while the variance correction contributes `J`. Their separate lower bounds are kept here so
the final comparison cannot silently discard either contribution. At low rates the cubic baseline
alone has ample room; an eighth-degree Taylor polynomial certifies that branch.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

noncomputable section

/-- The clipped rate parameter used by both endpoint branches. -/
def rateGap (δ ρ : ℝ) : ℝ := min 1 (δ / ρ)

/-- The normalized cubic-baseline factor after cancelling the common simplex volume. -/
def dimensionBaselineFactor (δ ρ H logd : ℝ) : ℝ :=
  let g := rateGap δ ρ
  ρ * (g * H / (1 + theta * g)) ^ 2 *
    Real.exp (logd * (theta * g / (1 + theta * g)))

/-- The normalized centered-variance factor after cancelling the common simplex volume. -/
def dimensionVarianceFactor (δ ρ logd : ℝ) : ℝ :=
  let g := rateGap δ ρ
  ρ * Real.exp (logd * (theta * g / (1 + theta * g)))

/-- The common scalar ratio supplied by the cubic baseline and centered-variance terms. -/
def normalizedDimensionRankSurplus (δ ρ H logd : ℝ) : ℝ :=
  (residualFraction ^ 3 * dimensionBaselineFactor δ ρ H logd +
      (999 / 1000) * (4147 / 2160) * dimensionVarianceFactor δ ρ logd) /
    (6 * (101 / 100) * (37 / 20) * (448 / 625))

/-- On the high-rate interval, the denominator appearing in `F` is small enough that its
rational prefactor is at least one. -/
theorem highRate_denominator_sq_le_rate (δ ρ : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : δ ≤ ρ) (hρmax : ρ ≤ 1 - δ) :
    (ρ + theta * δ) ^ 2 ≤ ρ := by
  have hnonneg : 0 ≤ (ρ - δ) * (1 - ρ - δ) :=
    mul_nonneg (sub_nonneg.mpr hρ) (by nlinarith)
  have hquarter : 0 ≤ δ * (1 / 4 - δ) :=
    mul_nonneg hδ.le (sub_nonneg.mpr hδmax)
  norm_num [theta] at hnonneg hquarter ⊢
  nlinarith

/-- The high-rate cubic-baseline factor `F` is at least `ξ² exp(θξ)`. The hypotheses are the
actual rate, harmonic, and logarithmic lower bounds, rather than a restatement of the result. -/
theorem highRate_F_lower (δ ρ H logd : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : δ ≤ ρ) (hρmax : ρ ≤ 1 - δ)
    (hH : xi / δ ≤ H) (hlog : xi / δ ≤ logd) :
    xi ^ 2 * Real.exp (theta * xi) ≤
      ρ * (δ / ρ) ^ 2 * H ^ 2 / (1 + theta * (δ / ρ)) ^ 2 *
        Real.exp (logd * ((theta * (δ / ρ)) / (1 + theta * (δ / ρ)))) := by
  have hρpos : 0 < ρ := hδ.trans_le hρ
  have hHpos : 0 < H := (div_pos xi_pos hδ).trans_le hH
  have htpos : 0 < ρ + theta * δ := by
    exact add_pos_of_pos_of_nonneg hρpos (mul_nonneg theta_pos.le hδ.le)
  have hapos : 0 < 1 + theta * (δ / ρ) := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg theta_pos.le (div_nonneg hδ.le hρpos.le))
  have hden := highRate_denominator_sq_le_rate δ ρ hδ hδmax hρ hρmax
  have hbase : xi ^ 2 ≤ xi ^ 2 * ρ / (ρ + theta * δ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos htpos)).mpr
    nlinarith [sq_nonneg xi]
  have hH2 : (xi / δ) ^ 2 ≤ H ^ 2 := by
    exact (sq_le_sq₀ (div_nonneg xi_pos.le hδ.le) hHpos.le).mpr hH
  have hfactor : 0 ≤ ρ * (δ / ρ) ^ 2 / (1 + theta * (δ / ρ)) ^ 2 := by
    positivity
  have hrat : xi ^ 2 ≤
      ρ * (δ / ρ) ^ 2 * H ^ 2 / (1 + theta * (δ / ρ)) ^ 2 := by
    calc
      xi ^ 2 ≤ xi ^ 2 * ρ / (ρ + theta * δ) ^ 2 := hbase
      _ = ρ * (δ / ρ) ^ 2 * (xi / δ) ^ 2 /
          (1 + theta * (δ / ρ)) ^ 2 := by field_simp
      _ ≤ ρ * (δ / ρ) ^ 2 * H ^ 2 /
          (1 + theta * (δ / ρ)) ^ 2 := by
        gcongr
  have ht_le_one : ρ + theta * δ ≤ 1 := by
    have := hρmax
    norm_num [theta] at this ⊢
    nlinarith
  have hexponent : theta * xi ≤
      logd * ((theta * (δ / ρ)) / (1 + theta * (δ / ρ))) := by
    have hθxi : 0 ≤ theta * xi := mul_nonneg theta_pos.le xi_pos.le
    calc
      theta * xi ≤ theta * xi / (ρ + theta * δ) := by
        apply (le_div_iff₀ htpos).mpr
        nlinarith
      _ = (xi / δ) * ((theta * (δ / ρ)) /
          (1 + theta * (δ / ρ))) := by field_simp
      _ ≤ logd * ((theta * (δ / ρ)) /
          (1 + theta * (δ / ρ))) := by
        exact mul_le_mul_of_nonneg_right hlog
          (div_nonneg (mul_nonneg theta_pos.le (div_nonneg hδ.le hρpos.le)) hapos.le)
  exact mul_le_mul hrat (Real.exp_le_exp.mpr hexponent)
    (Real.exp_pos _).le (by positivity)

/-- The elementary minimum `ρ exp(c/ρ) ≥ exp(1)c`, proved from the tangent inequality for
the exponential. -/
theorem exp_reciprocal_product_lower (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) :
    Real.exp 1 * c ≤ ρ * Real.exp (c / ρ) := by
  have ht := Real.add_one_le_exp (c / ρ - 1)
  have hquot : c / ρ ≤ Real.exp (c / ρ - 1) := by linarith
  calc
    Real.exp 1 * c = ρ * (Real.exp 1 * (c / ρ)) := by field_simp
    _ ≤ ρ * (Real.exp 1 * Real.exp (c / ρ - 1)) := by gcongr
    _ = ρ * Real.exp (c / ρ) := by rw [← Real.exp_add]; congr 2; ring

/-- The high-rate variance factor `J` retains the independent lower bound
`exp(1) * (θξ/(1+θ))`. -/
theorem highRate_J_lower (δ ρ logd : ℝ)
    (hδ : 0 < δ) (hρ : δ ≤ ρ) (hlog : xi / δ ≤ logd) :
    Real.exp 1 * (theta * xi / (1 + theta)) ≤
      ρ * Real.exp (logd * ((theta * (δ / ρ)) /
        (1 + theta * (δ / ρ)))) := by
  have hρpos : 0 < ρ := hδ.trans_le hρ
  have htpos : 0 < ρ + theta * δ := by
    exact add_pos_of_pos_of_nonneg hρpos (mul_nonneg theta_pos.le hδ.le)
  have ha : 0 < 1 + theta := add_pos_of_pos_of_nonneg zero_lt_one theta_pos.le
  have hapos : 0 < 1 + theta * (δ / ρ) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg theta_pos.le (div_nonneg hδ.le hρpos.le))
  have hc : 0 < theta * xi / (1 + theta) :=
    div_pos (mul_pos theta_pos xi_pos) ha
  have hden : ρ + theta * δ ≤ (1 + theta) * ρ := by
    nlinarith [mul_nonneg theta_pos.le (sub_nonneg.mpr hρ)]
  have hexponent : (theta * xi / (1 + theta)) / ρ ≤
      logd * ((theta * (δ / ρ)) / (1 + theta * (δ / ρ))) := by
    calc
      (theta * xi / (1 + theta)) / ρ =
          theta * xi / ((1 + theta) * ρ) := by rw [div_div]
      _ ≤ theta * xi / (ρ + theta * δ) :=
        div_le_div_of_nonneg_left (mul_nonneg theta_pos.le xi_pos.le) htpos hden
      _ = (xi / δ) * ((theta * (δ / ρ)) /
          (1 + theta * (δ / ρ))) := by field_simp
      _ ≤ logd * ((theta * (δ / ρ)) /
          (1 + theta * (δ / ρ))) := by
        apply mul_le_mul_of_nonneg_right hlog
        exact div_nonneg (mul_nonneg theta_pos.le (div_nonneg hδ.le hρpos.le)) hapos.le
  exact (exp_reciprocal_product_lower _ _ hc hρpos).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hρpos.le)

/-- The low-rate cubic-baseline factor is bounded at the endpoint `δ=1/4`. -/
theorem lowRate_F_lower (δ ρ H logd : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4) (hρ : δ / 3 ≤ ρ)
    (hH : xi / δ ≤ H) (hlog : xi / δ ≤ logd) :
    (4 * xi ^ 2 / (3 * (1 + theta) ^ 2)) *
        Real.exp (4 * theta * xi / (1 + theta)) ≤
      ρ * H ^ 2 / (1 + theta) ^ 2 *
        Real.exp (logd * (theta / (1 + theta))) := by
  have hρpos : 0 < ρ := (div_pos hδ (by norm_num)).trans_le hρ
  have hHpos : 0 < H := (div_pos xi_pos hδ).trans_le hH
  have ha : 0 < 1 + theta := add_pos_of_pos_of_nonneg zero_lt_one theta_pos.le
  have hH2 : (xi / δ) ^ 2 ≤ H ^ 2 :=
    (sq_le_sq₀ (div_nonneg xi_pos.le hδ.le) hHpos.le).mpr hH
  have hrat : 4 * xi ^ 2 / (3 * (1 + theta) ^ 2) ≤
      ρ * H ^ 2 / (1 + theta) ^ 2 := by
    have hbase : 4 * xi ^ 2 / 3 ≤ (δ / 3) * (xi / δ) ^ 2 := by
      calc
        4 * xi ^ 2 / 3 ≤ xi ^ 2 / (3 * δ) := by
          apply (le_div_iff₀ (mul_pos (by norm_num) hδ)).mpr
          nlinarith [sq_nonneg xi]
        _ = (δ / 3) * (xi / δ) ^ 2 := by field_simp
    rw [show 4 * xi ^ 2 / (3 * (1 + theta) ^ 2) =
      (4 * xi ^ 2 / 3) / (1 + theta) ^ 2 by field_simp]
    apply div_le_div_of_nonneg_right
    · exact hbase.trans (mul_le_mul hρ hH2 (sq_nonneg _) hρpos.le)
    · positivity
  have hexponent : 4 * theta * xi / (1 + theta) ≤
      logd * (theta / (1 + theta)) := by
    have hfour : 4 * xi ≤ xi / δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith [xi_pos]
    rw [show 4 * theta * xi / (1 + theta) =
      (4 * xi) * (theta / (1 + theta)) by ring]
    exact mul_le_mul_of_nonneg_right (hfour.trans hlog) (div_nonneg theta_pos.le ha.le)
  exact mul_le_mul hrat (Real.exp_le_exp.mpr hexponent)
    (Real.exp_pos _).le (by positivity)

/-- A fifth-degree Taylor polynomial gives the strict exponential lower bound used by `F`. -/
theorem exp_eightyOne_eightieth_gt : (11 / 4 : ℝ) < Real.exp (81 / 80) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 81 / 80) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A sixth-degree Taylor polynomial gives the strict lower bound for Euler's number used by
`J`. -/
theorem exp_one_gt : (163 / 60 : ℝ) < Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 7
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The finite exponential-tail estimate used in the normalized rank bound. -/
theorem endpoint_exp_upper : Real.exp (61 / 100) < (37 / 20 : ℝ) := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 61 / 100)
    (by norm_num : (61 / 100 : ℝ) ≤ 1) (by norm_num : 0 < (4 : ℕ))
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The eighth-degree Taylor polynomial at the low-rate endpoint lies below the exponential. -/
theorem lowRate_taylorEight_le_exp :
    (∑ i ∈ Finset.range 9, (162 / 55 : ℝ) ^ i / i.factorial) ≤ Real.exp (162 / 55) := by
  simpa using Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 162 / 55) 9

/-- The low-rate baseline term alone exceeds the required normalized surplus by a wide margin. -/
theorem lowRate_taylorEight_ratio_gt :
    (29 / 10 : ℝ) <
      ((5 / 8 : ℝ) ^ 3 *
        ((4 * (27 / 10 : ℝ) ^ 2 / (3 * (11 / 8 : ℝ) ^ 2)) *
          (∑ i ∈ Finset.range 9, (162 / 55 : ℝ) ^ i / i.factorial))) /
        (6 * (101 / 100 : ℝ) * (37 / 20) * (448 / 625)) := by
  norm_num [Finset.sum_range_succ]

/-- Exact rational value obtained from the two high-rate contributions. -/
theorem exact_surplus_identity :
    (((5 / 8 : ℝ) ^ 3 * (729 / 100) * (11 / 4) +
      (999 / 1000) * (4147 / 2160) * (81 / 110) * (163 / 60)) /
        (6 * (101 / 100) * (37 / 20) * (448 / 625))) =
      1862667945 / 1714356224 := by
  norm_num

/-- The audited two-term scalar is strictly larger than `543/500`. -/
theorem exact_surplus_gt :
    (543 / 500 : ℝ) < 1862667945 / 1714356224 := by norm_num

/-- The reciprocal of the audited surplus gap is strictly below `500/43`. -/
theorem exact_surplus_challenge_ratio_lt :
    1 / ((1862667945 / 1714356224 : ℝ) - 1) < 500 / 43 := by norm_num

/-- The displayed `543/500` margin has reciprocal surplus exactly `500/43`. -/
theorem targetSurplus_challenge_ratio_eq :
    1 / ((543 / 500 : ℝ) - 1) = 500 / 43 := by norm_num

/-- The public integer height constant `12` strictly dominates the challenge ratio. -/
theorem challenge_ratio_lt_twelve : (500 / 43 : ℝ) < 12 := by norm_num

/-- The two endpoint arguments give the same strict `543/500` surplus at every permitted rate.
The statement keeps the actual clipped rate and exponential factors visible, so it can be
combined directly with the dimension and rank estimates. -/
theorem normalizedDimensionRankSurplus_gt (δ ρ H logd : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hρ : δ / 3 ≤ ρ) (hρmax : ρ ≤ 1 - δ)
    (hH : xi / δ ≤ H) (hlog : xi / δ ≤ logd) :
    (543 / 500 : ℝ) < normalizedDimensionRankSurplus δ ρ H logd := by
  have hρpos : 0 < ρ := (div_pos hδ (by norm_num)).trans_le hρ
  by_cases hhigh : δ ≤ ρ
  · have hg : rateGap δ ρ = δ / ρ := by
      rw [rateGap, min_eq_right]
      exact (div_le_one hρpos).mpr hhigh
    have hapos : 0 < 1 + theta * (δ / ρ) :=
      add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg theta_pos.le (div_nonneg hδ.le hρpos.le))
    have hF := highRate_F_lower δ ρ H logd hδ hδmax hhigh hρmax hH hlog
    have hJ := highRate_J_lower δ ρ logd hδ hhigh hlog
    have hFlow : (729 / 100 : ℝ) * (11 / 4) <
        dimensionBaselineFactor δ ρ H logd := by
      calc
        (729 / 100 : ℝ) * (11 / 4) < xi ^ 2 * Real.exp (theta * xi) := by
          rw [show (729 / 100 : ℝ) = xi ^ 2 by norm_num [xi]]
          exact mul_lt_mul_of_pos_left
            (by
              have he := exp_eightyOne_eightieth_gt
              norm_num [theta, xi] at he ⊢
              exact he)
            (by norm_num [xi])
        _ ≤ dimensionBaselineFactor δ ρ H logd := by
          rw [dimensionBaselineFactor, hg]
          convert hF using 1
          field_simp [hρpos.ne', hapos.ne']
    have hJlow : (81 / 110 : ℝ) * (163 / 60) <
        dimensionVarianceFactor δ ρ logd := by
      calc
        (81 / 110 : ℝ) * (163 / 60) <
            Real.exp 1 * (theta * xi / (1 + theta)) := by
          rw [show (81 / 110 : ℝ) = theta * xi / (1 + theta) by norm_num [theta, xi]]
          exact (by
            simpa [mul_comm] using mul_lt_mul_of_pos_right exp_one_gt
              (by norm_num [theta, xi] : 0 < theta * xi / (1 + theta)))
        _ ≤ dimensionVarianceFactor δ ρ logd := by
          rw [dimensionVarianceFactor, hg]
          simpa [mul_div_assoc] using hJ
    have hnum :
        (residualFraction ^ 3 * ((729 / 100 : ℝ) * (11 / 4)) +
          (999 / 1000) * (4147 / 2160) * ((81 / 110) * (163 / 60))) <
        residualFraction ^ 3 * dimensionBaselineFactor δ ρ H logd +
          (999 / 1000) * (4147 / 2160) * dimensionVarianceFactor δ ρ logd := by
      have hb : 0 < residualFraction ^ 3 := by norm_num [residualFraction]
      have hc : 0 < (999 / 1000 : ℝ) * (4147 / 2160) := by norm_num
      nlinarith
    rw [normalizedDimensionRankSurplus]
    have hden : 0 < (6 * (101 / 100) * (37 / 20) * (448 / 625) : ℝ) := by norm_num
    calc
      (543 / 500 : ℝ) < 1862667945 / 1714356224 := exact_surplus_gt
      _ = (residualFraction ^ 3 * ((729 / 100 : ℝ) * (11 / 4)) +
          (999 / 1000) * (4147 / 2160) * ((81 / 110) * (163 / 60))) /
            (6 * (101 / 100) * (37 / 20) * (448 / 625)) := by
        rw [← exact_surplus_identity]
        norm_num [residualFraction]
      _ < _ := div_lt_div_of_pos_right hnum hden
  · have hlow : ρ < δ := lt_of_not_ge hhigh
    have hg : rateGap δ ρ = 1 := by
      rw [rateGap, min_eq_left]
      exact (one_le_div hρpos).mpr hlow.le
    have hF := lowRate_F_lower δ ρ H logd hδ hδmax hρ hH hlog
    have hTaylor :
        ((4 * xi ^ 2 / (3 * (1 + theta) ^ 2)) *
          (∑ i ∈ Finset.range 9, (162 / 55 : ℝ) ^ i / i.factorial)) ≤
          dimensionBaselineFactor δ ρ H logd := by
      calc
        _ ≤ (4 * xi ^ 2 / (3 * (1 + theta) ^ 2)) *
            Real.exp (162 / 55) := by
          gcongr
          exact lowRate_taylorEight_le_exp
        _ ≤ dimensionBaselineFactor δ ρ H logd := by
          rw [dimensionBaselineFactor, hg]
          norm_num [theta, xi] at hF ⊢
          convert hF using 1
          field_simp
          ring
    have hden : 0 < (6 * (101 / 100) * (37 / 20) * (448 / 625) : ℝ) := by norm_num
    have hbase : (29 / 10 : ℝ) <
        residualFraction ^ 3 * dimensionBaselineFactor δ ρ H logd /
          (6 * (101 / 100) * (37 / 20) * (448 / 625)) := by
      calc
        (29 / 10 : ℝ) <
            (residualFraction ^ 3 *
              ((4 * xi ^ 2 / (3 * (1 + theta) ^ 2)) *
                (∑ i ∈ Finset.range 9, (162 / 55 : ℝ) ^ i / i.factorial))) /
              (6 * (101 / 100) * (37 / 20) * (448 / 625)) := by
            have hlow := lowRate_taylorEight_ratio_gt
            norm_num [residualFraction, xi, theta] at hlow ⊢
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTaylor (by norm_num [residualFraction])) hden.le
    rw [normalizedDimensionRankSurplus]
    have hJnonneg : 0 ≤ dimensionVarianceFactor δ ρ logd := by
      rw [dimensionVarianceFactor]
      positivity
    have hc : 0 ≤ (999 / 1000 : ℝ) * (4147 / 2160) := by norm_num
    have hadd : residualFraction ^ 3 * dimensionBaselineFactor δ ρ H logd /
          (6 * (101 / 100) * (37 / 20) * (448 / 625)) ≤
        (residualFraction ^ 3 * dimensionBaselineFactor δ ρ H logd +
          (999 / 1000) * (4147 / 2160) * dimensionVarianceFactor δ ρ logd) /
          (6 * (101 / 100) * (37 / 20) * (448 / 625)) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith
    exact (by norm_num : (543 / 500 : ℝ) < 29 / 10) |>.trans (hbase.trans_le hadd)

end
end ReedSolomon.HiddenDerivative.WeightedSupportParameters
