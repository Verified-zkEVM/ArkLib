/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Asymptotics
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Moment
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.UniformParameters
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# A rate-uniform margin for the partition Gamma factor

This file certifies the two scalar branches of Appendix H.  For
`d = ceil (exp (3 / (2 * δ)))`, the limiting partition ratio retains enough margin after the
closed multiplicity loss `exp (-1/1000)` to exceed `151/150`.
-/

@[expose] public section

noncomputable section

open Set

namespace ReedSolomon.HiddenDerivative

private theorem log_forty_ninths_eq :
    Real.log (40 / 9 : ℝ) =
      3 * Real.log 2 + Real.log 5 - 2 * Real.log 3 := by
  calc
    Real.log (40 / 9 : ℝ) = Real.log 40 - Real.log 9 := by
      rw [Real.log_div] <;> norm_num
    _ = 3 * Real.log 2 + Real.log 5 - 2 * Real.log 3 := by
      rw [show (40 : ℝ) = 2 ^ 3 * 5 by norm_num,
        show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_mul] <;>
        try positivity
      rw [Real.log_pow, Real.log_pow]
      norm_num

private theorem log_forty_ninths_lt :
    Real.log (40 / 9 : ℝ) < 373 / 250 := by
  rw [log_forty_ninths_eq]
  linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_lt_d9]

private theorem log_forty_ninths_gt :
    (149 / 100 : ℝ) < Real.log (40 / 9 : ℝ) := by
  rw [log_forty_ninths_eq]
  linarith [Real.log_two_gt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9]

private theorem log_twentyseven_tenths_eq :
    Real.log (27 / 10 : ℝ) =
      3 * Real.log 3 - Real.log 2 - Real.log 5 := by
  calc
    Real.log (27 / 10 : ℝ) = Real.log 27 - Real.log 10 := by
      rw [Real.log_div] <;> norm_num
    _ = 3 * Real.log 3 - Real.log 2 - Real.log 5 := by
      rw [show (27 : ℝ) = 3 ^ 3 by norm_num,
        show (10 : ℝ) = 2 * 5 by norm_num, Real.log_pow,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
      ring

private theorem log_six_eq :
    Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
  rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  norm_num

/-- The uniform derivative order is already in the range of the simplex moment estimate. -/
theorem uniformRatePartitionOrder_ge_500 {δ : ℝ} (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    500 ≤ uniformRatePartitionOrder δ := by
  have hexponent : (311 / 50 : ℝ) < 3 / (2 * δ) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hδ)).2
    nlinarith
  have hlog : Real.log 500 < 3 / (2 * δ) :=
    (RatePartition.log_five_hundred_lt).trans hexponent
  have hexp : (500 : ℝ) < Real.exp (3 / (2 * δ)) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 500)]
    exact Real.exp_lt_exp.mpr hlog
  have heq : (3 / 2 : ℝ) / δ = 3 / (2 * δ) := by field_simp
  rw [uniformRatePartitionOrder, heq]
  exact_mod_cast hexp.le.trans (Nat.le_ceil (Real.exp (3 / (2 * δ))))

private theorem uniform_margin_numeric :
    (151 / 150 : ℝ) <
      Real.exp (3 / 2 - Real.log (40 / 9)) * Real.exp (-1 / 1000) := by
  have hlog151 : Real.log (151 / 150 : ℝ) < 1 / 150 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 151 / 150)
      (by norm_num : (151 / 150 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hexponent : Real.log (151 / 150 : ℝ) <
      3 / 2 - Real.log (40 / 9) - 1 / 1000 := by
    linarith [log_forty_ninths_lt]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 151 / 150), ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  linarith

private def lowRateLogMargin (δ : ℝ) : ℝ :=
  3 / (2 * δ) - 3 + Real.log (27 / 10) +
    2 * Real.log δ - 2 * δ * Real.log 6

private theorem lowRateLogMargin_quarter_gt :
    (3 / 10 : ℝ) < lowRateLogMargin (1 / 4) := by
  rw [lowRateLogMargin, log_twentyseven_tenths_eq,
    show Real.log (1 / 4 : ℝ) = -2 * Real.log 2 by
      rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      ring,
    log_six_eq]
  linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_lt_d9]

private theorem lowRateLogMargin_gt {δ : ℝ} (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    (3 / 10 : ℝ) < lowRateLogMargin δ := by
  have hquarter : δ ≤ 1 / 4 := by linarith
  let x : ℝ := 1 / (4 * δ)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxone : 1 ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ (mul_pos (by norm_num) hδ)).2
    nlinarith
  have hlogx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hxpos
  have hx_eq : x = (1 / 4 : ℝ) / δ := by
    dsimp [x]
    field_simp
  have hlogdiff : Real.log δ - Real.log (1 / 4 : ℝ) = -Real.log x := by
    rw [hx_eq, Real.log_div (by norm_num : (1 / 4 : ℝ) ≠ 0) hδ.ne']
    ring
  have hrecip : 3 / (2 * δ) = 6 * x := by
    dsimp [x]
    field_simp
    ring
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hcompare : lowRateLogMargin (1 / 4) ≤ lowRateLogMargin δ := by
    unfold lowRateLogMargin
    nlinarith
  exact lowRateLogMargin_quarter_gt.trans_le hcompare

private theorem uniformRatePartitionOrder_log_lower {δ : ℝ} (hδ : 0 < δ) :
    3 / (2 * δ) ≤ Real.log (uniformRatePartitionOrder δ : ℝ) := by
  have hexp := Real.exp_pos (3 / (2 * δ))
  have heq : (3 / 2 : ℝ) / δ = 3 / (2 * δ) := by field_simp
  have hceil : Real.exp (3 / (2 * δ)) ≤ (uniformRatePartitionOrder δ : ℝ) := by
    rw [uniformRatePartitionOrder, heq]
    exact Nat.le_ceil _
  simpa only [Real.log_exp] using Real.log_le_log hexp hceil

/-- The low-rate ambient choice has the uniform limiting-ratio lower bound used before
any finite-multiplicity loss is charged. -/
theorem uniformRatePartitionGamma_low_base_gt {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    Real.exp (3 / 2 - Real.log (40 / 9)) <
      ratePartitionGamma (2 * δ ^ 2) δ (uniformRatePartitionOrder δ) := by
  let d := uniformRatePartitionOrder δ
  have hd500 : 500 ≤ d := uniformRatePartitionOrder_ge_500 hδ hδmax
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : 0 < 2 * δ ^ 2 := by positivity
  have hlogd : 3 / (2 * δ) ≤ Real.log (d : ℝ) :=
    uniformRatePartitionOrder_log_lower hδ
  have hcoefficient : 0 < 1 - 2 * δ := by linarith
  have hlogfactor :
      Real.log ((27 / 20 : ℝ) * (2 * δ ^ 2)) =
        Real.log (27 / 10) + 2 * Real.log δ := by
    rw [show (27 / 20 : ℝ) * (2 * δ ^ 2) = (27 / 10) * δ ^ 2 by ring,
      Real.log_mul (by norm_num : (27 / 10 : ℝ) ≠ 0) (sq_pos_of_pos hδ).ne',
      Real.log_pow]
    norm_num
  have hlogsucc : Real.log (d : ℝ) < Real.log ((d : ℝ) + 1) :=
    Real.strictMonoOn_log (by simpa using hdR) (by simp; linarith) (by linarith)
  have hloggamma : lowRateLogMargin δ <
      Real.log (ratePartitionGamma (2 * δ ^ 2) δ d) := by
    rw [log_ratePartitionGamma hR hd, hlogfactor]
    have hmain := mul_le_mul_of_nonneg_left hlogd hcoefficient.le
    have hmain' : 3 / (2 * δ) - 3 ≤ (1 - 2 * δ) * Real.log d := by
      calc
        3 / (2 * δ) - 3 = (1 - 2 * δ) * (3 / (2 * δ)) := by field_simp
        _ ≤ (1 - 2 * δ) * Real.log d := hmain
    have hcombine : 3 / (2 * δ) - 3 <
        Real.log ((d : ℝ) + 1) - 2 * δ * Real.log d := by
      nlinarith
    unfold lowRateLogMargin
    have hratio : (2 * δ ^ 2) / δ = 2 * δ := by field_simp
    rw [hratio]
    calc
      3 / (2 * δ) - 3 + Real.log (27 / 10) + 2 * Real.log δ -
          2 * δ * Real.log 6 <
        Real.log (27 / 10) + 2 * Real.log δ +
          (Real.log ((d : ℝ) + 1) - 2 * δ * Real.log d) -
            2 * δ * Real.log 6 := by linarith
      _ = Real.log (27 / 10) + 2 * Real.log δ + Real.log ((d : ℝ) + 1) -
          2 * δ * (Real.log 6 + Real.log d) := by ring
  have hlower : 3 / 2 - Real.log (40 / 9) <
      Real.log (ratePartitionGamma (2 * δ ^ 2) δ d) := by
    have hm := lowRateLogMargin_gt hδ hδmax
    have hc := log_forty_ninths_gt
    linarith
  have hgammapos : 0 < ratePartitionGamma (2 * δ ^ 2) δ d := by
    unfold ratePartitionGamma
    positivity
  have hexp : Real.exp (3 / 2 - Real.log (40 / 9)) <
      ratePartitionGamma (2 * δ ^ 2) δ d := by
    rw [← Real.exp_log hgammapos]
    exact Real.exp_lt_exp.mpr hlower
  exact hexp

/-- The low-rate ambient choice `R = 2δ²`, `a = δ` retains the legacy closed
finite-ratio margin. -/
theorem uniformRatePartitionGamma_low_gt {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    (151 / 150 : ℝ) <
      ratePartitionGamma (2 * δ ^ 2) δ (uniformRatePartitionOrder δ) *
        Real.exp (-1 / 1000) := by
  exact uniform_margin_numeric.trans (mul_lt_mul_of_pos_right
    (uniformRatePartitionGamma_low_base_gt hδ hδmax) (Real.exp_pos (-1 / 1000)))

/-- The logarithmic constants in the high-rate penalty match. -/
private theorem log_six_sub_log_factor :
    Real.log 6 - Real.log (27 / 20 : ℝ) = Real.log (40 / 9 : ℝ) := by
  rw [← Real.log_div (by norm_num : (6 : ℝ) ≠ 0) (by norm_num : (27 / 20 : ℝ) ≠ 0)]
  congr 1
  norm_num

private def highRatePenalty (R δ : ℝ) : ℝ :=
  R * Real.log (40 / 9) - (R + δ) * Real.log R - δ * Real.log (27 / 20)

private theorem highRatePenalty_hasDerivAt {R δ : ℝ} (hR : 0 < R) :
    HasDerivAt (fun x ↦ highRatePenalty x δ)
      (Real.log (40 / 9) - Real.log R - 1 - δ / R) R := by
  have hderiv := ((hasDerivAt_id R).mul_const (Real.log (40 / 9))).sub
    (((hasDerivAt_id R).add_const δ).mul (Real.hasDerivAt_log hR.ne')) |>.sub_const
      (δ * Real.log (27 / 20))
  have heq :
      1 * Real.log (40 / 9) - (1 * Real.log R + (R + δ) * R⁻¹) =
        Real.log (40 / 9) - Real.log R - 1 - δ / R := by
    rw [div_eq_mul_inv]
    field_simp [hR.ne']
    ring
  convert hderiv.congr_deriv heq using 1 <;> try rfl

private theorem highRatePenalty_deriv {R δ : ℝ} (hR : 0 < R) :
    deriv (fun x ↦ highRatePenalty x δ) R =
      Real.log (40 / 9) - Real.log R - 1 - δ / R :=
  (highRatePenalty_hasDerivAt hR).deriv

private theorem highRatePenalty_le_endpoint {R δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) (hRδ : δ ≤ R) (hRtop : R ≤ 1 - δ) :
    highRatePenalty R δ ≤ highRatePenalty (1 - δ) δ := by
  have htoppos : 0 < 1 - δ := by linarith
  have hRpos : 0 < R := hδ.trans_le hRδ
  have hmono : MonotoneOn (fun x ↦ highRatePenalty x δ) (Icc δ (1 - δ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc δ (1 - δ))
    · intro x hx
      have hxpos : 0 < x := hδ.trans_le hx.1
      exact (highRatePenalty_hasDerivAt hxpos).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Ioo δ (1 - δ) := by simpa only [interior_Icc] using hx
      have hxpos : 0 < x := hδ.trans hx'.1
      have hxlow : δ < x := hx'.1
      have hxtop : x < 1 - δ := hx'.2
      exact (highRatePenalty_hasDerivAt hxpos).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo δ (1 - δ) := by simpa only [interior_Icc] using hx
      have hxpos : 0 < x := hδ.trans hx'.1
      have hxlow : δ < x := hx'.1
      have hxtop : x < 1 - δ := hx'.2
      rw [highRatePenalty_deriv hxpos]
      have hlog := Real.log_le_sub_one_of_pos hxpos
      have hproduct : 0 ≤ (1 - x) * (x - δ) :=
        mul_nonneg (by linarith) (by linarith)
      have hsum : x + δ / x ≤ 1 + δ := by
        calc
          x + δ / x = (x ^ 2 + δ) / x := by field_simp
          _ ≤ 1 + δ := (div_le_iff₀ hxpos).2 (by nlinarith)
      linarith [log_forty_ninths_gt]
  exact hmono ⟨hRδ, hRtop⟩ ⟨by linarith, le_rfl⟩ hRtop

private theorem highRatePenalty_endpoint_lt {δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    highRatePenalty (1 - δ) δ < Real.log (40 / 9) := by
  have hspos : 0 < 1 - δ := by linarith
  have hlogs := Real.one_sub_inv_le_log_of_pos hspos
  have hlog6 : (4 / 3 : ℝ) < Real.log 6 := by
    rw [log_six_eq]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hneglog : -Real.log (1 - δ) ≤ 4 * δ / 3 := by
    have hfirst : -(Real.log (1 - δ)) ≤ δ / (1 - δ) := by
      rw [show 1 - (1 - δ)⁻¹ = -(δ / (1 - δ)) by field_simp; ring] at hlogs
      linarith
    have hsecond : δ / (1 - δ) ≤ 4 * δ / 3 := by
      apply (div_le_iff₀ hspos).2
      nlinarith
    exact hfirst.trans hsecond
  unfold highRatePenalty
  have hid :
      (1 - δ) * Real.log (40 / 9) - ((1 - δ) + δ) * Real.log (1 - δ) -
          δ * Real.log (27 / 20) =
        Real.log (40 / 9) - δ * Real.log 6 - Real.log (1 - δ) := by
    rw [← log_six_sub_log_factor]
    ring
  rw [hid]
  have : 4 * δ / 3 < δ * Real.log 6 := by nlinarith
  linarith

private theorem highRatePenalty_convex_low {δ : ℝ} (hδ : 0 < δ) :
    ConvexOn ℝ (Icc (δ ^ 2) δ) (fun R ↦ highRatePenalty R δ) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (δ ^ 2) δ)
  · intro x hx
    have hxpos : 0 < x := (sq_pos_of_pos hδ).trans_le hx.1
    exact (highRatePenalty_hasDerivAt hxpos).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (δ ^ 2) δ := by simpa only [interior_Icc] using hx
    have hxpos : 0 < x := (sq_pos_of_pos hδ).trans hx'.1
    exact (highRatePenalty_hasDerivAt hxpos).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (δ ^ 2) δ := by simpa only [interior_Icc] using hx
    have hxpos : 0 < x := (sq_pos_of_pos hδ).trans hx'.1
    have hsecond := (((hasDerivAt_const x (Real.log (40 / 9))).sub
      (Real.hasDerivAt_log hxpos.ne')).sub_const 1).sub
        ((hasDerivAt_const x δ).div (hasDerivAt_id x) hxpos.ne')
    convert hsecond.hasDerivWithinAt using 1 <;> try rfl
  · intro x hx
    have hx' : x ∈ Ioo (δ ^ 2) δ := by simpa only [interior_Icc] using hx
    have hxpos : 0 < x := (sq_pos_of_pos hδ).trans hx'.1
    simp only [id_eq, zero_mul, zero_sub]
    rw [show -x⁻¹ - -(δ * 1) / x ^ 2 = (δ - x) / x ^ 2 by
      field_simp [hxpos.ne']; ring]
    exact div_nonneg (sub_nonneg.mpr hx'.2.le) (sq_nonneg x)

private theorem neg_mul_log_le_half {x : ℝ} (hx : 0 < x) :
    -x * Real.log x ≤ 1 / 2 := by
  have h2x : 0 < 2 * x := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos h2x
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hx.le
  have hxinv : x * (2 * x)⁻¹ = 1 / 2 := by field_simp
  rw [mul_sub, mul_one, hxinv, mul_add] at hmul
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlog2mul := mul_lt_mul_of_pos_left hlog2 hx
  linarith

private theorem highRatePenalty_sq_endpoint_lt {δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    highRatePenalty (δ ^ 2) δ < Real.log (40 / 9) := by
  have hN := neg_mul_log_le_half hδ
  have hLpos : 0 < Real.log (40 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hLupper := log_forty_ninths_lt
  have hLlower := log_forty_ninths_gt
  have hcpos : 0 < Real.log (27 / 20 : ℝ) := Real.log_pos (by norm_num)
  have hδsq : δ ^ 2 < 1 / 16 := by nlinarith
  have hδsqL : δ ^ 2 * Real.log (40 / 9 : ℝ) < 373 / 4000 := by
    calc
      δ ^ 2 * Real.log (40 / 9 : ℝ) <
          (1 / 16) * Real.log (40 / 9 : ℝ) := mul_lt_mul_of_pos_right hδsq hLpos
      _ < (1 / 16) * (373 / 250) := mul_lt_mul_of_pos_left hLupper (by norm_num)
      _ = 373 / 4000 := by norm_num
  have hNmul := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 2 * (δ + 1))
  unfold highRatePenalty
  rw [Real.log_pow]
  norm_num at ⊢
  have hid :
      δ ^ 2 * Real.log (40 / 9) - (δ ^ 2 + δ) * (2 * Real.log δ) -
          δ * Real.log (27 / 20) =
        δ ^ 2 * Real.log (40 / 9) + 2 * (δ + 1) * (-δ * Real.log δ) -
          δ * Real.log (27 / 20) := by ring
  rw [hid]
  nlinarith

private theorem highRatePenalty_delta_endpoint_lt {δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    highRatePenalty δ δ < Real.log (40 / 9) := by
  have hN := neg_mul_log_le_half hδ
  have hLpos : 0 < Real.log (40 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hLupper := log_forty_ninths_lt
  have hLlower := log_forty_ninths_gt
  have hcpos : 0 < Real.log (27 / 20 : ℝ) := Real.log_pos (by norm_num)
  have hδL : δ * Real.log (40 / 9 : ℝ) < 373 / 1000 := by
    calc
      δ * Real.log (40 / 9 : ℝ) <
          (1 / 4) * Real.log (40 / 9 : ℝ) := mul_lt_mul_of_pos_right hδquarter hLpos
      _ < (1 / 4) * (373 / 250) := mul_lt_mul_of_pos_left hLupper (by norm_num)
      _ = 373 / 1000 := by norm_num
  unfold highRatePenalty
  nlinarith

private theorem highRatePenalty_low_lt {R δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4)
    (hRlow : δ ^ 2 ≤ R) (hRhigh : R ≤ δ) :
    highRatePenalty R δ < Real.log (40 / 9) := by
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hle := (highRatePenalty_convex_low hδ).le_max_of_mem_Icc
    ⟨le_rfl, hδsq⟩ ⟨hδsq, le_rfl⟩ ⟨hRlow, hRhigh⟩
  exact hle.trans_lt (max_lt (highRatePenalty_sq_endpoint_lt hδ hδquarter)
    (highRatePenalty_delta_endpoint_lt hδ hδquarter))

private theorem highRatePenalty_lt {R δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    highRatePenalty R δ < Real.log (40 / 9) := by
  have hδquarter : δ < 1 / 4 := by linarith
  rcases le_total R δ with hRδ | hδR
  · exact highRatePenalty_low_lt hδ hδquarter hRlow hRδ
  · exact (highRatePenalty_le_endpoint hδ hδquarter hδR hRtop).trans_lt
      (highRatePenalty_endpoint_lt hδ hδquarter)

/-- The high-rate choice has the same uniform limiting-ratio lower bound before
finite-multiplicity loss, for every `δ² ≤ R ≤ 1 - δ`. -/
theorem uniformRatePartitionGamma_high_base_gt {R δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    Real.exp (3 / 2 - Real.log (40 / 9)) <
      ratePartitionGamma R (R + δ) (uniformRatePartitionOrder δ) := by
  let d := uniformRatePartitionOrder δ
  have hd500 : 500 ≤ d := uniformRatePartitionOrder_ge_500 hδ hδmax
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRpos : 0 < R := (sq_pos_of_pos hδ).trans_le hRlow
  have ha : 0 < R + δ := add_pos hRpos hδ
  have hale : R + δ ≤ 1 := by linarith
  have hlogd : 3 / (2 * δ) ≤ Real.log (d : ℝ) :=
    uniformRatePartitionOrder_log_lower hδ
  have hthree : (3 / 2 : ℝ) ≤ δ * Real.log (d : ℝ) := by
    calc
      (3 / 2 : ℝ) = δ * (3 / (2 * δ)) := by field_simp
      _ ≤ δ * Real.log (d : ℝ) := mul_le_mul_of_nonneg_left hlogd hδ.le
  have hlogsucc : Real.log (d : ℝ) < Real.log ((d : ℝ) + 1) :=
    Real.strictMonoOn_log (by simpa using hdR) (by simp; linarith) (by linarith)
  have hcombine :
      δ * Real.log (d : ℝ) <
        (R + δ) * Real.log ((d : ℝ) + 1) - R * Real.log (d : ℝ) := by
    have hδlog := mul_lt_mul_of_pos_left hlogsucc hδ
    have hRlog := mul_nonneg hRpos.le (sub_nonneg.mpr hlogsucc.le)
    nlinarith
  have hlogfactor :
      Real.log ((27 / 20 : ℝ) * R) = Real.log (27 / 20) + Real.log R := by
    rw [Real.log_mul (by norm_num : (27 / 20 : ℝ) ≠ 0) hRpos.ne']
  have hloggamma := log_ratePartitionGamma (a := R + δ) hRpos hd
  have hscaled :
      (R + δ) * Real.log (ratePartitionGamma R (R + δ) d) =
        (R + δ) * (Real.log (27 / 20) + Real.log R) +
          (R + δ) * Real.log ((d : ℝ) + 1) -
            R * (Real.log 6 + Real.log d) := by
    rw [hloggamma, hlogfactor]
    field_simp [ha.ne']
  have hpenaltyIdentity :
      3 / 2 - highRatePenalty R δ =
        (R + δ) * (Real.log (27 / 20) + Real.log R) + 3 / 2 -
          R * Real.log 6 := by
    rw [highRatePenalty, ← log_six_sub_log_factor]
    ring
  have hscaledLower :
      3 / 2 - highRatePenalty R δ <
        (R + δ) * Real.log (ratePartitionGamma R (R + δ) d) := by
    rw [hpenaltyIdentity, hscaled]
    nlinarith
  have hpenalty := highRatePenalty_lt hδ hδmax hRlow hRtop
  have hbasepos : 0 < 3 / 2 - Real.log (40 / 9 : ℝ) := by
    linarith [log_forty_ninths_lt]
  have hproduct :
      3 / 2 - Real.log (40 / 9 : ℝ) <
        (R + δ) * Real.log (ratePartitionGamma R (R + δ) d) :=
    (sub_lt_sub_left hpenalty (3 / 2)).trans hscaledLower
  have hloggammapos : 0 < Real.log (ratePartitionGamma R (R + δ) d) := by
    rcases (mul_pos_iff.mp (hbasepos.trans hproduct)) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge ha.le) h.1)
  have hloglower :
      3 / 2 - Real.log (40 / 9 : ℝ) <
        Real.log (ratePartitionGamma R (R + δ) d) := by
    have hmul := mul_le_mul_of_nonneg_right hale hloggammapos.le
    norm_num at hmul
    exact hproduct.trans_le hmul
  have hgammapos : 0 < ratePartitionGamma R (R + δ) d := by
    unfold ratePartitionGamma
    positivity
  have hexp : Real.exp (3 / 2 - Real.log (40 / 9)) <
      ratePartitionGamma R (R + δ) d := by
    rw [← Real.exp_log hgammapos]
    exact Real.exp_lt_exp.mpr hloglower
  exact hexp

/-- The high-rate choice `a = R + δ` retains the legacy closed finite-ratio margin uniformly for
all `δ² ≤ R ≤ 1 - δ`. -/
theorem uniformRatePartitionGamma_high_gt {R δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    (151 / 150 : ℝ) <
      ratePartitionGamma R (R + δ) (uniformRatePartitionOrder δ) *
        Real.exp (-1 / 1000) := by
  exact uniform_margin_numeric.trans (mul_lt_mul_of_pos_right
    (uniformRatePartitionGamma_high_base_gt hδ hδmax hRlow hRtop)
    (Real.exp_pos (-1 / 1000)))

end ReedSolomon.HiddenDerivative
