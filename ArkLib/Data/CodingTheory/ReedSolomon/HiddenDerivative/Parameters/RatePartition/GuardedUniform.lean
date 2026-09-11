/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.MathematicalUniform
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.SharpRatio
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Archived guarded `1.489` uniform rate-partition parameters

The readable three-halves recipe remains the mathematical headline. This module retains, as a
library-only comparison, the optional refinement removed from the canonical manuscript:

`min (ceil (exp (1.5/δ))) (max 1000 (ceil (exp (1.489/δ))))`.

When the first branch is selected, all existing `27/20` proofs are reused.  Otherwise the order
is at least `1000`, so the sharpened `273/200` source coefficient applies.  The multiplicity is
always the mathematical 300-based selector; no executable parameter is changed.
-/

@[expose] public section

noncomputable section

open Set PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

private theorem neg_log_ninety_one_hundred_lt :
    -Real.log (91 / 100 : ℝ) < 94311 / 1000000 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := (9 / 100 : ℝ)) (by norm_num) 8
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 100),
    show (1 - 9 / 100 : ℝ) = 91 / 100 by norm_num] at h
  have hu := (abs_le.mp h).1
  norm_num [Finset.sum_range_succ] at hu ⊢
  linarith

private theorem neg_log_ninety_one_hundred_ge :
    (9 / 100 : ℝ) ≤ -Real.log (91 / 100 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 91 / 100)
  norm_num at h ⊢
  linarith

private theorem log_sharp_factor_lt :
    Real.log (400 / 91 : ℝ) < 148061 / 100000 := by
  rw [show Real.log (400 / 91 : ℝ) = Real.log 4 - Real.log (91 / 100) by
    rw [← Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (91 / 100 : ℝ) ≠ 0)]
    congr 1
    norm_num, Real.log_four_eq]
  linarith [Real.log_two_lt_d9, neg_log_ninety_one_hundred_lt]

private theorem log_sharp_factor_gt :
    (147 / 100 : ℝ) < Real.log (400 / 91 : ℝ) := by
  rw [show Real.log (400 / 91 : ℝ) = Real.log 4 - Real.log (91 / 100) by
    rw [← Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (91 / 100 : ℝ) ≠ 0)]
    congr 1
    norm_num, Real.log_four_eq]
  linarith [Real.log_two_gt_d9, neg_log_ninety_one_hundred_ge]

private theorem log_twice_sharp_coefficient_gt :
    (1 : ℝ) < Real.log (273 / 100 : ℝ) := by
  rw [show Real.log (273 / 100 : ℝ) = Real.log 3 + Real.log (91 / 100) by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (by norm_num : (91 / 100 : ℝ) ≠ 0)]
    congr 1
    norm_num]
  linarith [Real.log_three_gt_d9, neg_log_ninety_one_hundred_lt]

private theorem sharp_uniform_margin_numeric :
    (151 / 150 : ℝ) <
      Real.exp (1489 / 1000 - Real.log (400 / 91)) *
        Real.exp (-(1677 / 1000000 : ℝ)) := by
  have hlog151 : Real.log (151 / 150 : ℝ) < 1 / 150 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 151 / 150)
      (by norm_num : (151 / 150 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hexponent : Real.log (151 / 150 : ℝ) <
      1489 / 1000 - Real.log (400 / 91) - 1677 / 1000000 := by
    linarith [log_sharp_factor_lt]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 151 / 150), ← Real.exp_add]
  exact Real.exp_lt_exp.mpr (by linarith)

private def sharpLowRateLogMargin (δ : ℝ) : ℝ :=
  1489 / (1000 * δ) - 3 + Real.log (273 / 100) +
    2 * Real.log δ - 2 * δ * Real.log 6

private theorem sharpLowRateLogMargin_quarter_gt :
    (1 / 4 : ℝ) < sharpLowRateLogMargin (1 / 4) := by
  unfold sharpLowRateLogMargin
  rw [show Real.log (1 / 4 : ℝ) = -2 * Real.log 2 by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    ring,
    show Real.log (6 : ℝ) = Real.log 2 + Real.log 3 by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num]
  linarith [log_twice_sharp_coefficient_gt, Real.log_two_lt_d9,
    Real.log_three_lt_d9]

private theorem sharpLowRateLogMargin_gt {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    (1 / 4 : ℝ) < sharpLowRateLogMargin δ := by
  have hquarter : δ ≤ 1 / 4 := by linarith
  let x : ℝ := 1 / (4 * δ)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxone : 1 ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ (mul_pos (by norm_num) hδ)).2 (by nlinarith)
  have hlogx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hxpos
  have hx_eq : x = (1 / 4 : ℝ) / δ := by dsimp [x]; field_simp
  have hlogdiff : Real.log δ - Real.log (1 / 4 : ℝ) = -Real.log x := by
    rw [hx_eq, Real.log_div (by norm_num : (1 / 4 : ℝ) ≠ 0) hδ.ne']
    ring
  have hrecip : 1489 / (1000 * δ) = (1489 / 250 : ℝ) * x := by
    dsimp [x]
    field_simp
    ring
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hcompare : sharpLowRateLogMargin (1 / 4) ≤ sharpLowRateLogMargin δ := by
    unfold sharpLowRateLogMargin
    nlinarith
  exact sharpLowRateLogMargin_quarter_gt.trans_le hcompare

/-- Logarithm of the sharpened limiting ratio. -/
private theorem log_sharpRatePartitionGamma {R a : ℝ} {d : ℕ}
    (hR : 0 < R) (hd : 0 < d) :
    Real.log (sharpRatePartitionGamma R a d) =
      Real.log ((273 / 200 : ℝ) * R) + Real.log ((d : ℝ) + 1) -
        R / a * (Real.log 6 + Real.log d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sharpRatePartitionGamma, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity : (273 / 200 : ℝ) * R ≠ 0) (by positivity),
    Real.log_rpow (by positivity), Real.log_mul (by norm_num) hd'.ne']

private def sharpHighRatePenalty (R δ : ℝ) : ℝ :=
  R * Real.log (400 / 91) - (R + δ) * Real.log R -
    δ * Real.log (273 / 200)

private theorem log_six_sub_log_sharp_coefficient :
    Real.log 6 - Real.log (273 / 200 : ℝ) = Real.log (400 / 91 : ℝ) := by
  rw [← Real.log_div (by norm_num : (6 : ℝ) ≠ 0)
    (by norm_num : (273 / 200 : ℝ) ≠ 0)]
  congr 1
  norm_num

private theorem sharpHighRatePenalty_hasDerivAt {R δ : ℝ} (hR : 0 < R) :
    HasDerivAt (fun x ↦ sharpHighRatePenalty x δ)
      (Real.log (400 / 91) - Real.log R - 1 - δ / R) R := by
  have hderiv := ((hasDerivAt_id R).mul_const (Real.log (400 / 91))).sub
    (((hasDerivAt_id R).add_const δ).mul (Real.hasDerivAt_log hR.ne')) |>.sub_const
      (δ * Real.log (273 / 200))
  have heq :
      1 * Real.log (400 / 91) - (1 * Real.log R + (R + δ) * R⁻¹) =
        Real.log (400 / 91) - Real.log R - 1 - δ / R := by
    rw [div_eq_mul_inv]
    field_simp [hR.ne']
    ring
  convert hderiv.congr_deriv heq using 1 <;> try rfl

private theorem sharpHighRatePenalty_deriv {R δ : ℝ} (hR : 0 < R) :
    deriv (fun x ↦ sharpHighRatePenalty x δ) R =
      Real.log (400 / 91) - Real.log R - 1 - δ / R :=
  (sharpHighRatePenalty_hasDerivAt hR).deriv

private theorem sharpHighRatePenalty_le_endpoint {R δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) (hRδ : δ ≤ R) (hRtop : R ≤ 1 - δ) :
    sharpHighRatePenalty R δ ≤ sharpHighRatePenalty (1 - δ) δ := by
  have hmono : MonotoneOn (fun x ↦ sharpHighRatePenalty x δ) (Icc δ (1 - δ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc δ (1 - δ))
    · intro x hx
      exact (sharpHighRatePenalty_hasDerivAt (hδ.trans_le hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Ioo δ (1 - δ) := by simpa only [interior_Icc] using hx
      exact (sharpHighRatePenalty_hasDerivAt (hδ.trans hx'.1)).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo δ (1 - δ) := by simpa only [interior_Icc] using hx
      have hxlow : δ < x := hx'.1
      have hxtop : x < 1 - δ := hx'.2
      have hxpos : 0 < x := hδ.trans hx'.1
      rw [sharpHighRatePenalty_deriv hxpos]
      have hlog := Real.log_le_sub_one_of_pos hxpos
      have hproduct : 0 ≤ (1 - x) * (x - δ) :=
        mul_nonneg (by linarith) (by linarith)
      have hsum : x + δ / x ≤ 1 + δ := by
        rw [show x + δ / x = (x ^ 2 + δ) / x by field_simp]
        exact (div_le_iff₀ hxpos).2 (by nlinarith)
      linarith [log_sharp_factor_gt]
  exact hmono ⟨hRδ, hRtop⟩ ⟨by linarith, le_rfl⟩ hRtop

private theorem sharpHighRatePenalty_endpoint_lt {δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    sharpHighRatePenalty (1 - δ) δ < Real.log (400 / 91) := by
  have hspos : 0 < 1 - δ := by linarith
  have hlogs := Real.one_sub_inv_le_log_of_pos hspos
  have hlog6 : (4 / 3 : ℝ) < Real.log 6 := by
    rw [show Real.log (6 : ℝ) = Real.log 2 + Real.log 3 by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hneglog : -Real.log (1 - δ) ≤ 4 * δ / 3 := by
    have hfirst : -Real.log (1 - δ) ≤ δ / (1 - δ) := by
      rw [show 1 - (1 - δ)⁻¹ = -(δ / (1 - δ)) by field_simp; ring] at hlogs
      linarith
    exact hfirst.trans ((div_le_iff₀ hspos).2 (by nlinarith))
  unfold sharpHighRatePenalty
  rw [show
      (1 - δ) * Real.log (400 / 91) - ((1 - δ) + δ) * Real.log (1 - δ) -
          δ * Real.log (273 / 200) =
        Real.log (400 / 91) - δ * Real.log 6 - Real.log (1 - δ) by
    rw [← log_six_sub_log_sharp_coefficient]
    ring]
  nlinarith

private theorem neg_mul_log_le_half {x : ℝ} (hx : 0 < x) :
    -x * Real.log x ≤ 1 / 2 := by
  have h2x : 0 < 2 * x := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos h2x
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hx.le
  have hxinv : x * (2 * x)⁻¹ = 1 / 2 := by field_simp
  rw [mul_sub, mul_one, hxinv, mul_add] at hmul
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  nlinarith [mul_lt_mul_of_pos_left hlog2 hx]

private theorem sharpHighRatePenalty_convex_low {δ : ℝ} (hδ : 0 < δ) :
    ConvexOn ℝ (Icc (δ ^ 2) δ) (fun R ↦ sharpHighRatePenalty R δ) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (δ ^ 2) δ)
  · intro x hx
    exact (sharpHighRatePenalty_hasDerivAt ((sq_pos_of_pos hδ).trans_le hx.1)).continuousAt
      |>.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (δ ^ 2) δ := by simpa only [interior_Icc] using hx
    exact (sharpHighRatePenalty_hasDerivAt ((sq_pos_of_pos hδ).trans hx'.1)).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (δ ^ 2) δ := by simpa only [interior_Icc] using hx
    have hxpos : 0 < x := (sq_pos_of_pos hδ).trans hx'.1
    have hsecond := (((hasDerivAt_const x (Real.log (400 / 91))).sub
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

private theorem sharpHighRatePenalty_sq_endpoint_lt {δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    sharpHighRatePenalty (δ ^ 2) δ < Real.log (400 / 91) := by
  have hN := neg_mul_log_le_half hδ
  have hLpos : 0 < Real.log (400 / 91 : ℝ) := Real.log_pos (by norm_num)
  have hδsqL : δ ^ 2 * Real.log (400 / 91 : ℝ) < 148061 / 1600000 := by
    calc
      δ ^ 2 * Real.log (400 / 91 : ℝ) <
          (1 / 16) * Real.log (400 / 91 : ℝ) :=
        mul_lt_mul_of_pos_right (by nlinarith) hLpos
      _ < (1 / 16) * (148061 / 100000) :=
        mul_lt_mul_of_pos_left log_sharp_factor_lt (by norm_num)
      _ = 148061 / 1600000 := by norm_num
  have hNmul := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 2 * (δ + 1))
  unfold sharpHighRatePenalty
  rw [Real.log_pow]
  norm_num at ⊢
  rw [show
      δ ^ 2 * Real.log (400 / 91) - (δ ^ 2 + δ) * (2 * Real.log δ) -
          δ * Real.log (273 / 200) =
        δ ^ 2 * Real.log (400 / 91) + 2 * (δ + 1) * (-δ * Real.log δ) -
          δ * Real.log (273 / 200) by ring]
  have hBlog : 0 < Real.log (273 / 200 : ℝ) := Real.log_pos (by norm_num)
  nlinarith [log_sharp_factor_gt]

private theorem sharpHighRatePenalty_delta_endpoint_lt {δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    sharpHighRatePenalty δ δ < Real.log (400 / 91) := by
  have hN := neg_mul_log_le_half hδ
  have hLpos : 0 < Real.log (400 / 91 : ℝ) := Real.log_pos (by norm_num)
  have hδL : δ * Real.log (400 / 91 : ℝ) < 148061 / 400000 := by
    calc
      δ * Real.log (400 / 91 : ℝ) < (1 / 4) * Real.log (400 / 91 : ℝ) :=
        mul_lt_mul_of_pos_right hδquarter hLpos
      _ < (1 / 4) * (148061 / 100000) :=
        mul_lt_mul_of_pos_left log_sharp_factor_lt (by norm_num)
      _ = 148061 / 400000 := by norm_num
  unfold sharpHighRatePenalty
  have hBlog : 0 < Real.log (273 / 200 : ℝ) := Real.log_pos (by norm_num)
  nlinarith [log_sharp_factor_gt]

private theorem sharpHighRatePenalty_lt {R δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    sharpHighRatePenalty R δ < Real.log (400 / 91) := by
  have hδquarter : δ < 1 / 4 := by linarith
  rcases le_total R δ with hRδ | hδR
  · have hδsq : δ ^ 2 ≤ δ := by nlinarith
    have hle := (sharpHighRatePenalty_convex_low hδ).le_max_of_mem_Icc
      ⟨le_rfl, hδsq⟩ ⟨hδsq, le_rfl⟩ ⟨hRlow, hRδ⟩
    exact hle.trans_lt (max_lt (sharpHighRatePenalty_sq_endpoint_lt hδ hδquarter)
      (sharpHighRatePenalty_delta_endpoint_lt hδ hδquarter))
  · exact (sharpHighRatePenalty_le_endpoint hδ hδquarter hδR hRtop).trans_lt
      (sharpHighRatePenalty_endpoint_lt hδ hδquarter)

private theorem sharpRatePartitionGamma_high_base_gt
    {R δ : ℝ} {d : ℕ} (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hd : 0 < d) (hlogd : 1489 / (1000 * δ) ≤ Real.log (d : ℝ))
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    Real.exp (1489 / 1000 - Real.log (400 / 91)) <
      sharpRatePartitionGamma R (R + δ) d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRpos : 0 < R := (sq_pos_of_pos hδ).trans_le hRlow
  have ha : 0 < R + δ := add_pos hRpos hδ
  have hale : R + δ ≤ 1 := by linarith
  have hmain : (1489 / 1000 : ℝ) ≤ δ * Real.log (d : ℝ) := by
    calc
      (1489 / 1000 : ℝ) = δ * (1489 / (1000 * δ)) := by field_simp
      _ ≤ δ * Real.log (d : ℝ) := mul_le_mul_of_nonneg_left hlogd hδ.le
  have hlogsucc : Real.log (d : ℝ) < Real.log ((d : ℝ) + 1) :=
    Real.strictMonoOn_log (by simpa using hdR) (by simp; linarith) (by linarith)
  have hcombine : δ * Real.log (d : ℝ) <
      (R + δ) * Real.log ((d : ℝ) + 1) - R * Real.log (d : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_left hlogsucc hδ,
      mul_nonneg hRpos.le (sub_nonneg.mpr hlogsucc.le)]
  have hlogfactor : Real.log ((273 / 200 : ℝ) * R) =
      Real.log (273 / 200) + Real.log R := by
    rw [Real.log_mul (by norm_num : (273 / 200 : ℝ) ≠ 0) hRpos.ne']
  have hscaled :
      (R + δ) * Real.log (sharpRatePartitionGamma R (R + δ) d) =
        (R + δ) * (Real.log (273 / 200) + Real.log R) +
          (R + δ) * Real.log ((d : ℝ) + 1) -
            R * (Real.log 6 + Real.log d) := by
    rw [log_sharpRatePartitionGamma hRpos hd, hlogfactor]
    field_simp [ha.ne']
  have hpenaltyIdentity :
      1489 / 1000 - sharpHighRatePenalty R δ =
        (R + δ) * (Real.log (273 / 200) + Real.log R) + 1489 / 1000 -
          R * Real.log 6 := by
    rw [sharpHighRatePenalty, ← log_six_sub_log_sharp_coefficient]
    ring
  have hscaledLower : 1489 / 1000 - sharpHighRatePenalty R δ <
      (R + δ) * Real.log (sharpRatePartitionGamma R (R + δ) d) := by
    rw [hpenaltyIdentity, hscaled]
    nlinarith
  have hpenalty := sharpHighRatePenalty_lt hδ hδmax hRlow hRtop
  have hbasepos : 0 < (1489 / 1000 : ℝ) - Real.log (400 / 91) := by
    linarith [log_sharp_factor_lt]
  have hproduct : 1489 / 1000 - Real.log (400 / 91) <
      (R + δ) * Real.log (sharpRatePartitionGamma R (R + δ) d) :=
    (sub_lt_sub_left hpenalty (1489 / 1000)).trans hscaledLower
  have hloggammapos : 0 < Real.log (sharpRatePartitionGamma R (R + δ) d) := by
    rcases (mul_pos_iff.mp (hbasepos.trans hproduct)) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge ha.le) h.1)
  have hloglower : 1489 / 1000 - Real.log (400 / 91) <
      Real.log (sharpRatePartitionGamma R (R + δ) d) := by
    exact hproduct.trans_le (by
      have := mul_le_mul_of_nonneg_right hale hloggammapos.le
      norm_num at this
      exact this)
  have hgammapos : 0 < sharpRatePartitionGamma R (R + δ) d := by
    unfold sharpRatePartitionGamma
    positivity
  rw [← Real.exp_log hgammapos]
  exact Real.exp_lt_exp.mpr hloglower

private theorem sharpRatePartitionGamma_low_base_gt
    {δ : ℝ} {d : ℕ} (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hd : 0 < d) (hlogd : 1489 / (1000 * δ) ≤ Real.log (d : ℝ)) :
    Real.exp (1489 / 1000 - Real.log (400 / 91)) <
      sharpRatePartitionGamma (2 * δ ^ 2) δ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hR : 0 < 2 * δ ^ 2 := by positivity
  have hcoefficient : 0 < 1 - 2 * δ := by linarith
  have hlogfactor : Real.log ((273 / 200 : ℝ) * (2 * δ ^ 2)) =
      Real.log (273 / 100) + 2 * Real.log δ := by
    rw [show (273 / 200 : ℝ) * (2 * δ ^ 2) = (273 / 100) * δ ^ 2 by ring,
      Real.log_mul (by norm_num : (273 / 100 : ℝ) ≠ 0) (sq_pos_of_pos hδ).ne',
      Real.log_pow]
    norm_num
  have hlogsucc : Real.log (d : ℝ) < Real.log ((d : ℝ) + 1) :=
    Real.strictMonoOn_log (by simpa using hdR) (by simp; linarith) (by linarith)
  have hmain := mul_le_mul_of_nonneg_left hlogd hcoefficient.le
  have hmain' : 1489 / (1000 * δ) - 3 ≤
      (1 - 2 * δ) * Real.log d := by
    have : 1489 / (1000 * δ) - 2978 / 1000 ≤
        (1 - 2 * δ) * Real.log d := by
      calc
        1489 / (1000 * δ) - 2978 / 1000 =
            (1 - 2 * δ) * (1489 / (1000 * δ)) := by field_simp; ring
        _ ≤ (1 - 2 * δ) * Real.log d := hmain
    linarith
  have hloggamma : sharpLowRateLogMargin δ <
      Real.log (sharpRatePartitionGamma (2 * δ ^ 2) δ d) := by
    rw [log_sharpRatePartitionGamma hR hd, hlogfactor]
    have hratio : (2 * δ ^ 2) / δ = 2 * δ := by field_simp
    rw [hratio]
    unfold sharpLowRateLogMargin
    nlinarith
  have hlower : 1489 / 1000 - Real.log (400 / 91) <
      Real.log (sharpRatePartitionGamma (2 * δ ^ 2) δ d) := by
    have hm := sharpLowRateLogMargin_gt hδ hδmax
    linarith [log_sharp_factor_gt]
  have hgammapos : 0 < sharpRatePartitionGamma (2 * δ ^ 2) δ d := by
    unfold sharpRatePartitionGamma
    positivity
  rw [← Real.exp_log hgammapos]
  exact Real.exp_lt_exp.mpr hlower

/-- Guarded derivative order for the archived comparison. -/
def guardedRatePartitionOrder (δ : ℝ) : ℕ :=
  min (uniformRatePartitionOrder δ)
    (max 1000 ⌈Real.exp ((1489 / 1000 : ℝ) / δ)⌉₊)

def guardedRatePartitionMultiplicity (δ : ℝ) : ℕ :=
  ratePartitionMathematicalMultiplicity (guardedRatePartitionOrder δ)

def guardedRatePartitionLength (δ : ℝ) : ℕ :=
  ⌈2 * (guardedRatePartitionMultiplicity δ : ℝ) / δ ^ 2⌉₊

def guardedRatePartitionJetBound (δ : ℝ) : ℕ :=
  ⌈(guardedRatePartitionMultiplicity δ : ℝ) / δ ^ 2⌉₊ - 1

/-- Use the headline ratio on the headline-order branch and the sharp ratio otherwise. -/
def guardedRatePartitionFiniteRatio (δ R a : ℝ) : ℝ :=
  if guardedRatePartitionOrder δ = uniformRatePartitionOrder δ then
    ratePartitionFiniteRatio R a (guardedRatePartitionOrder δ)
      (guardedRatePartitionMultiplicity δ)
  else
    sharpRatePartitionFiniteRatio R a (guardedRatePartitionOrder δ)
      (guardedRatePartitionMultiplicity δ)

theorem guardedRatePartitionOrder_eq_uniform_or_ge_1000 (δ : ℝ) :
    guardedRatePartitionOrder δ = uniformRatePartitionOrder δ ∨
      1000 ≤ guardedRatePartitionOrder δ := by
  by_cases h : guardedRatePartitionOrder δ = uniformRatePartitionOrder δ
  · exact Or.inl h
  · right
    unfold guardedRatePartitionOrder at h ⊢
    rcases min_choice (uniformRatePartitionOrder δ)
      (max 1000 ⌈Real.exp ((1489 / 1000 : ℝ) / δ)⌉₊) with hmin | hmin
    · exact (h hmin).elim
    · rw [hmin]
      exact Nat.le_max_left _ _

theorem guardedRatePartitionOrder_ge_519 {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    519 ≤ guardedRatePartitionOrder δ := by
  rw [guardedRatePartitionOrder]
  rw [Nat.le_min]
  exact ⟨uniformRatePartitionOrder_ge_519 hδ hδmax,
    (show 519 ≤ 1000 by omega).trans (Nat.le_max_left _ _)⟩

private theorem guardedRatePartitionOrder_log_lower_of_ne {δ : ℝ}
    (hδ : 0 < δ)
    (hne : guardedRatePartitionOrder δ ≠ uniformRatePartitionOrder δ) :
    1489 / (1000 * δ) ≤ Real.log (guardedRatePartitionOrder δ : ℝ) := by
  have hchoice := guardedRatePartitionOrder_eq_uniform_or_ge_1000 δ
  rcases hchoice with h | _
  · exact (hne h).elim
  have hsecond : guardedRatePartitionOrder δ =
      max 1000 ⌈Real.exp ((1489 / 1000 : ℝ) / δ)⌉₊ := by
    unfold guardedRatePartitionOrder at hne ⊢
    rcases min_choice (uniformRatePartitionOrder δ)
      (max 1000 ⌈Real.exp ((1489 / 1000 : ℝ) / δ)⌉₊) with hmin | hmin
    · exact (hne hmin).elim
    · exact hmin
  have hexp : Real.exp ((1489 / 1000 : ℝ) / δ) ≤
      (guardedRatePartitionOrder δ : ℝ) := by
    rw [hsecond]
    exact (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 1000 _)
  have hpos := Real.exp_pos ((1489 / 1000 : ℝ) / δ)
  have := Real.log_le_log hpos hexp
  have halg : (1489 / 1000 : ℝ) / δ = 1489 / (1000 * δ) := by field_simp
  rw [Real.log_exp, halg] at this
  exact this

theorem ratePartitionMathematicalMultiplicity_ge_guardedOrder {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    guardedRatePartitionOrder δ + 2 ≤ guardedRatePartitionMultiplicity δ := by
  exact ratePartitionMathematicalMultiplicity_ge_order
    (guardedRatePartitionOrder_ge_519 hδ hδmax)

theorem guardedRatePartition_integer_guards {δ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδone : δ < 1)
    (hm : 0 < guardedRatePartitionMultiplicity δ)
    (hn : guardedRatePartitionLength δ ≤ n) :
    let m := guardedRatePartitionMultiplicity δ
    let ν := guardedRatePartitionJetBound δ
    2 * (m : ℝ) ≤ δ ^ 2 * n ∧ m ≤ n ∧ 0 < ν ∧ ν < n := by
  let m := guardedRatePartitionMultiplicity δ
  let c := ⌈(m : ℝ) / δ ^ 2⌉₊
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδ2one : δ ^ 2 < 1 := by nlinarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hbound : 2 * (m : ℝ) / δ ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have hsize : 2 * (m : ℝ) ≤ δ ^ 2 * n := by
    simpa only [mul_comm] using (div_le_iff₀ hδ2).mp hbound
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hcpos : 1 < c := by
    apply Nat.lt_ceil.mpr
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
    apply (lt_div_iff₀ hδ2).mpr
    norm_num
    linarith
  have hcn : c ≤ n := by
    apply Nat.ceil_le.mpr
    exact (div_le_iff₀ hδ2).mpr (by nlinarith)
  exact ⟨hsize, hmn, by change 0 < c - 1; omega, by change c - 1 < n; omega⟩

theorem guardedRatePartition_totalJetDegree_le {D d W n A : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hDlower : δ ^ 2 * n ≤ D) (hAn : A ≤ n)
    {u : JetVariable d →₀ ℕ}
    (hu : RatePartitionEligible D d W (guardedRatePartitionMultiplicity δ * A : ℕ) u) :
    totalJetDegree u ≤ guardedRatePartitionJetBound δ := by
  let m := guardedRatePartitionMultiplicity δ
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have ht := totalJetDegree_lt_of_ratePartitionEligible hD hu
  have hb : ((m * A : ℕ) : ℝ) / D ≤ (m : ℝ) / δ ^ 2 := by
    apply (div_le_div_iff₀ hD' hδ2).2
    have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hDlower hm',
      mul_le_mul_of_nonneg_left hAn' (mul_nonneg hm' hδ2.le)]
  have hc : (m : ℝ) / δ ^ 2 ≤ ⌈(m : ℝ) / δ ^ 2⌉₊ := Nat.le_ceil _
  have hlt : totalJetDegree u < ⌈(m : ℝ) / δ ^ 2⌉₊ := by
    exact_mod_cast (ht.trans_le (hb.trans hc))
  exact Nat.le_sub_one_of_lt hlt

theorem guardedRatePartition_low_ratio_gt {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25) :
    (151 / 150 : ℝ) < guardedRatePartitionFiniteRatio δ (2 * δ ^ 2) δ := by
  by_cases heq : guardedRatePartitionOrder δ = uniformRatePartitionOrder δ
  · simp only [guardedRatePartitionFiniteRatio, heq, if_pos]
    simpa only [heq, guardedRatePartitionMultiplicity,
      uniformRatePartitionMathematicalMultiplicity] using
      uniformRatePartitionMathematical_low_ratio_gt hδ hδmax
  · rw [guardedRatePartitionFiniteRatio, if_neg heq]
    have hd519 := guardedRatePartitionOrder_ge_519 hδ hδmax
    have hd : 0 < guardedRatePartitionOrder δ := by omega
    have hbase := sharpRatePartitionGamma_low_base_gt hδ hδmax hd
      (guardedRatePartitionOrder_log_lower_of_ne hδ heq)
    have hfinite := sharpRatePartition_mathematical_ratio_gt
      (R := 2 * δ ^ 2) (a := δ)
      (show 0 < 2 * δ ^ 2 by positivity) (show 2 * δ ^ 2 < δ by nlinarith) hd519
    exact sharp_uniform_margin_numeric.trans <|
      (mul_lt_mul_of_pos_right hbase
        (Real.exp_pos (-(1677 / 1000000 : ℝ)))).trans (by
          simpa only [guardedRatePartitionMultiplicity] using hfinite)

theorem guardedRatePartition_high_ratio_gt {R δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ < 6 / 25)
    (hRlow : δ ^ 2 ≤ R) (hRtop : R ≤ 1 - δ) :
    (151 / 150 : ℝ) < guardedRatePartitionFiniteRatio δ R (R + δ) := by
  by_cases heq : guardedRatePartitionOrder δ = uniformRatePartitionOrder δ
  · simp only [guardedRatePartitionFiniteRatio, heq, if_pos]
    simpa only [heq, guardedRatePartitionMultiplicity,
      uniformRatePartitionMathematicalMultiplicity] using
      uniformRatePartitionMathematical_high_ratio_gt hδ hδmax hRlow hRtop
  · rw [guardedRatePartitionFiniteRatio, if_neg heq]
    have hd519 := guardedRatePartitionOrder_ge_519 hδ hδmax
    have hd : 0 < guardedRatePartitionOrder δ := by omega
    have hR : 0 < R := (sq_pos_of_pos hδ).trans_le hRlow
    have hbase := sharpRatePartitionGamma_high_base_gt hδ hδmax hd
      (guardedRatePartitionOrder_log_lower_of_ne hδ heq) hRlow hRtop
    have hfinite := sharpRatePartition_mathematical_ratio_gt
      (R := R) (a := R + δ) hR (by linarith) hd519
    exact sharp_uniform_margin_numeric.trans <|
      (mul_lt_mul_of_pos_right hbase
        (Real.exp_pos (-(1677 / 1000000 : ℝ)))).trans (by
          simpa only [guardedRatePartitionMultiplicity] using hfinite)

/-- A rate-uniform envelope for the archived guarded order. -/
structure GuardedRatePartitionEnvelope (δ : ℝ) (n k A : ℕ) where
  ambientDegree : ℕ
  rate : ℝ
  agreement : ℝ
  rate_pos : 0 < rate
  rate_lt_agreement : rate < agreement
  agreement_le_one : agreement ≤ 1
  order_le : guardedRatePartitionOrder δ + 1 ≤ ambientDegree
  ambient_le : ambientDegree + 1 ≤ n
  message_le : k ≤ ambientDegree + 1
  ambient_lower : δ ^ 2 * n ≤ ambientDegree
  rate_upper : (ambientDegree : ℝ) ≤ rate * n
  agreement_lower : agreement * n ≤ A
  ratio_gt : (151 / 150 : ℝ) < guardedRatePartitionFiniteRatio δ rate agreement

theorem exists_guardedRatePartitionEnvelope {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : guardedRatePartitionLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    Nonempty (GuardedRatePartitionEnvelope δ n k A) := by
  have hδone : δ < 1 := by linarith
  have hmorder := ratePartitionMathematicalMultiplicity_ge_guardedOrder hδ hδsmall
  have hm : 0 < guardedRatePartitionMultiplicity δ := by omega
  obtain ⟨hsize, _hmn, _hν, _hνn⟩ :=
    guardedRatePartition_integer_guards hδ hδone hm hn
  have hkA : k ≤ A := by
    have : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast this
  have hnpos : 0 < n := hk.trans_le (hkA.trans hAn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  by_cases hhigh : δ ^ 2 * n ≤ k
  · let R : ℝ := (k : ℝ) / n
    let a : ℝ := R + δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRlow : δ ^ 2 ≤ R := by
      dsimp [R]
      exact (le_div_iff₀ hnR).2 (by simpa only [Nat.cast_ofNat] using hhigh)
    have hRtop : R ≤ 1 - δ := by
      dsimp [R]
      exact (div_le_iff₀ hnR).2 (by
        have hAn' : (A : ℝ) ≤ n := by exact_mod_cast hAn
        nlinarith)
    obtain ⟨horder, hambient⟩ := uniformRatePartition_high_ambient
      hδ hδone hmorder hsize hhigh hgap hAn
    refine ⟨⟨k, R, a, hRpos, by dsimp [a]; linarith, ?_, horder, hambient,
      Nat.le_succ k, hhigh, ?_, ?_, guardedRatePartition_high_ratio_gt
        hδ hδsmall hRlow hRtop⟩⟩
    · dsimp [a]
      linarith
    · dsimp [R]
      field_simp
      norm_num
    · calc
        a * n = (k : ℝ) + δ * n := by dsimp [a, R]; field_simp
        _ ≤ A := hgap
  · let D : ℕ := ⌊2 * δ ^ 2 * n⌋₊
    let R : ℝ := 2 * δ ^ 2
    let a : ℝ := δ
    have hRpos : 0 < R := by dsimp [R]; positivity
    obtain ⟨horder, hDlower, hambient⟩ := uniformRatePartition_low_ambient
      hδ hδsmall hmorder hsize
    have hkDreal : (k : ℝ) ≤ D := by
      have hklt : (k : ℝ) < δ ^ 2 * n := lt_of_not_ge hhigh
      exact hklt.le.trans (by simpa only [D] using hDlower)
    have hkD : k ≤ D := by exact_mod_cast hkDreal
    refine ⟨⟨D, R, a, hRpos, by dsimp [R, a]; nlinarith, hδone.le,
      horder, hambient, hkD.trans (Nat.le_succ D), hDlower, ?_, ?_,
      guardedRatePartition_low_ratio_gt hδ hδsmall⟩⟩
    · dsimp [D, R]
      exact Nat.floor_le (by positivity)
    · dsimp [a]
      nlinarith [Nat.cast_nonneg k (α := ℝ)]

end ReedSolomon.HiddenDerivative
