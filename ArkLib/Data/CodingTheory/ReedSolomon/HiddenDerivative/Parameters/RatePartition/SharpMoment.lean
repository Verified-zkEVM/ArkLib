/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RatePartition.Moment

/-!
# Sharpened maximum-coordinate moment above order 1000

The ordinary rate-partition estimate uses a strict `27/10` lower bound for the normalized
positive-part second moment.  Once the derivative order is at least `1000`, the same exact
mean--variance argument yields `273/100`.  This is the analytic input for the guarded `1.489`
comparison retained in the library. The canonical manuscript no longer includes that optional
refinement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace ReedSolomon.HiddenDerivative.RatePartition

theorem log_six_gt_sharp : (17917 / 10000 : ℝ) < Real.log 6 := by
  rw [show Real.log (6 : ℝ) = Real.log 2 + Real.log 3 by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

theorem log_one_thousand_gt : (69 / 10 : ℝ) < Real.log 1000 := by
  rw [show Real.log (1000 : ℝ) = 3 * (Real.log 2 + Real.log 5) by
    calc
      Real.log (1000 : ℝ) = Real.log ((2 * 5 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log (2 * 5 : ℝ) := by rw [Real.log_pow]; norm_num
      _ = 3 * (Real.log 2 + Real.log 5) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]]
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

theorem log_one_thousand_lt : Real.log 1000 < (1727 / 250 : ℝ) := by
  rw [show Real.log (1000 : ℝ) = 3 * (Real.log 2 + Real.log 5) by
    calc
      Real.log (1000 : ℝ) = Real.log ((2 * 5 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log (2 * 5 : ℝ) := by rw [Real.log_pow]; norm_num
      _ = 3 * (Real.log 2 + Real.log 5) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

private theorem affineMoment_strict_lower_sharp
    {D H Q L A : ℝ} (hD : 1000 ≤ D) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hHupper : H - L < 29 / 50) (hQ : 41 / 25 < Q)
    (hA : 17917 / 10000 < A) :
    (12117 / 10000 : ℝ) ^ 2 + 41 / 25 -
        ((L + 29 / 50) ^ 2 -
          2 * (12117 / 10000) * (1000 / 1001) * (L + 29 / 50) +
          3 * (41 / 25)) / D <
      (A + L) ^ 2 - 2 * (A + L) * D * (H / (D + 1)) +
        D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) := by
  have hD0 : 0 < D := by linarith
  have hD1 : 0 < D + 1 := by linarith
  have hD2 : 0 < D + 2 := by linarith
  have ht : 0 < L + 29 / 50 := by linarith
  have hHu : H < L + 29 / 50 := by linarith
  have hres : (12117 / 10000 : ℝ) + (L + 29 / 50) / (D + 1) <
      A + L - D * H / (D + 1) := by
    field_simp
    nlinarith
  have hratio : (1000 / 1001 : ℝ) * (L + 29 / 50) / D ≤
      (L + 29 / 50) / (D + 1) := by
    field_simp
    nlinarith
  have hbias : (12117 / 10000 : ℝ) ^ 2 +
      2 * (12117 / 10000) * (1000 / 1001) * (L + 29 / 50) / D <
        (A + L - D * H / (D + 1)) ^ 2 := by
    have hbase : 0 < (12117 / 10000 : ℝ) := by norm_num
    have hres' : (12117 / 10000 : ℝ) +
        (1000 / 1001) * (L + 29 / 50) / D <
          A + L - D * H / (D + 1) := by
      calc
        (12117 / 10000 : ℝ) + (1000 / 1001) * (L + 29 / 50) / D ≤
            12117 / 10000 + (L + 29 / 50) / (D + 1) := by linarith
        _ < A + L - D * H / (D + 1) := hres
    have hleft : 0 ≤ (12117 / 10000 : ℝ) +
        (1000 / 1001) * (L + 29 / 50) / D := by positivity
    have hsquares := (sq_lt_sq₀ hleft (hleft.trans_lt hres').le).2 hres'
    calc
      (12117 / 10000 : ℝ) ^ 2 +
          2 * (12117 / 10000) * (1000 / 1001) * (L + 29 / 50) / D ≤
          (12117 / 10000 + (1000 / 1001) * (L + 29 / 50) / D) ^ 2 := by
        let r : ℝ := (1000 / 1001) * (L + 29 / 50) / D
        calc
          (12117 / 10000 : ℝ) ^ 2 +
              2 * (12117 / 10000) * (1000 / 1001) * (L + 29 / 50) / D ≤
              (12117 / 10000) ^ 2 +
                2 * (12117 / 10000) * (1000 / 1001) * (L + 29 / 50) / D + r ^ 2 :=
            le_add_of_nonneg_right (sq_nonneg r)
          _ = (12117 / 10000 + (1000 / 1001) * (L + 29 / 50) / D) ^ 2 := by
            dsimp only [r]
            ring
      _ < (A + L - D * H / (D + 1)) ^ 2 := hsquares
  have hcoefQ : 1 - 3 / D < D ^ 2 / ((D + 1) * (D + 2)) := by
    field_simp
    nlinarith
  have hcoefH : D ^ 2 / ((D + 1) ^ 2 * (D + 2)) ≤ 1 / D := by
    field_simp
    nlinarith
  have hQpos : 0 < Q := by linarith
  have hvcoef : (41 / 25 : ℝ) * (1 - 3 / D) <
      Q * (D ^ 2 / ((D + 1) * (D + 2))) := by
    have hone : 0 < 1 - 3 / D := by
      apply sub_pos.mpr
      exact (div_lt_iff₀ hD0).2 (by linarith)
    nlinarith
  have hHsq : H ^ 2 < (L + 29 / 50) ^ 2 := by nlinarith
  have hHterm : D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) ≤
      (L + 29 / 50) ^ 2 / D := by
    have hcoefH0 : 0 ≤ D ^ 2 / ((D + 1) ^ 2 * (D + 2)) := by positivity
    calc
      D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) =
          (D ^ 2 / ((D + 1) ^ 2 * (D + 2))) * H ^ 2 := by ring
      _ ≤ (D ^ 2 / ((D + 1) ^ 2 * (D + 2))) * (L + 29 / 50) ^ 2 :=
        mul_le_mul_of_nonneg_left hHsq.le hcoefH0
      _ ≤ (1 / D) * (L + 29 / 50) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefH (sq_nonneg _)
      _ = (L + 29 / 50) ^ 2 / D := by ring
  have hvariance : (41 / 25 : ℝ) * (1 - 3 / D) -
      (L + 29 / 50) ^ 2 / D <
        D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) -
          (D * H / (D + 1)) ^ 2 := by
    have hid : D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) -
        (D * H / (D + 1)) ^ 2 =
      Q * (D ^ 2 / ((D + 1) * (D + 2))) -
        D ^ 2 * H ^ 2 / ((D + 1) ^ 2 * (D + 2)) := by
      field_simp
      ring
    rw [hid]
    linarith
  have hdecomp :
      (A + L) ^ 2 - 2 * (A + L) * D * (H / (D + 1)) +
          D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) =
        (A + L - D * H / (D + 1)) ^ 2 +
          (D ^ 2 * ((H ^ 2 + Q) / ((D + 1) * (D + 2))) -
            (D * H / (D + 1)) ^ 2) := by ring
  rw [hdecomp]
  ring_nf at hbias hvariance ⊢
  nlinarith

private noncomputable def sharpMomentErrorPolynomial (x : ℝ) : ℝ :=
  x ^ 2 - 4508 / 3575 * x + 1377173 / 357500

private noncomputable def sharpMomentErrorRatio (x : ℝ) : ℝ :=
  sharpMomentErrorPolynomial (Real.log x) / x

private theorem sharpMomentErrorPolynomial_eq (x : ℝ) :
    sharpMomentErrorPolynomial x =
      (x + 29 / 50) ^ 2 -
        2 * (12117 / 10000) * (1000 / 1001) * (x + 29 / 50) +
        3 * (41 / 25) := by
  unfold sharpMomentErrorPolynomial
  ring

private theorem sharpMomentErrorRatio_antitone :
    AntitoneOn sharpMomentErrorRatio (Ici (1000 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (1000 : ℝ))
  · intro x hx
    have hxne : x ≠ 0 := by simp only [mem_Ici] at hx; linarith
    have hlog := Real.continuousAt_log hxne
    unfold sharpMomentErrorRatio sharpMomentErrorPolynomial
    exact ((((hlog.pow 2).sub (hlog.const_mul (4508 / 3575))).add_const
      (1377173 / 357500)).div continuousAt_id hxne).continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := by simp only [interior_Ici, mem_Ioi] at hx; linarith
    have hlog := Real.hasDerivAt_log hxpos.ne'
    unfold sharpMomentErrorRatio sharpMomentErrorPolynomial
    exact ((((hlog.pow 2).sub (hlog.const_mul (4508 / 3575))).add_const
      (1377173 / 357500)).div (hasDerivAt_id x) hxpos.ne').differentiableAt
        |>.differentiableWithinAt
  · intro x hx
    have hxpos : 0 < x := by simp only [interior_Ici, mem_Ioi] at hx; linarith
    have hx1000 : (1000 : ℝ) < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hlog : (69 / 10 : ℝ) < Real.log x :=
      log_one_thousand_gt.trans (Real.strictMonoOn_log (by norm_num) hxpos hx1000)
    have hnum := (((Real.hasDerivAt_log hxpos.ne').pow 2).sub
      ((Real.hasDerivAt_log hxpos.ne').const_mul (4508 / 3575))).add_const
        (1377173 / 357500)
    have hderiv' := hnum.div (hasDerivAt_id x) hxpos.ne'
    unfold sharpMomentErrorRatio sharpMomentErrorPolynomial
    change deriv (((fun z ↦
      (Real.log ^ 2 - fun y ↦ 4508 / 3575 * Real.log y) z +
        1377173 / 357500) / id)) x ≤ 0
    rw [hderiv'.deriv]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Pi.pow_apply, Pi.sub_apply]
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hxpos
    apply div_nonpos_of_nonpos_of_nonneg _ hx2.le
    have hsimp :
        (2 * Real.log x * x⁻¹ - 4508 / 3575 * x⁻¹) * x =
          2 * Real.log x - 4508 / 3575 := by field_simp
    rw [hsimp]
    nlinarith [sq_nonneg (Real.log x - 69 / 10)]

private theorem sharpMomentErrorRatio_nat_le {d : ℕ} (hd : 1000 ≤ d) :
    sharpMomentErrorRatio d ≤ sharpMomentErrorPolynomial (1727 / 250) / 1000 := by
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hanti := sharpMomentErrorRatio_antitone (by simp) (by simpa using hdR) hdR
  have hloglower : (69 / 10 : ℝ) < Real.log 1000 := log_one_thousand_gt
  have hlogupper : Real.log 1000 < (1727 / 250 : ℝ) := log_one_thousand_lt
  have hpoly : sharpMomentErrorPolynomial (Real.log 1000) ≤
      sharpMomentErrorPolynomial (1727 / 250) := by
    unfold sharpMomentErrorPolynomial
    nlinarith [mul_nonneg (sub_nonneg.mpr hlogupper.le)
      (show 0 ≤ Real.log 1000 + 1727 / 250 - 4508 / 3575 by linarith)]
  calc
    sharpMomentErrorRatio d ≤ sharpMomentErrorRatio 1000 := hanti
    _ = sharpMomentErrorPolynomial (Real.log 1000) / 1000 := rfl
    _ ≤ sharpMomentErrorPolynomial (1727 / 250) / 1000 := by gcongr

/-- Strict `273/100` lower bound for the squared lower tail of the maximum once `d ≥ 1000`. -/
theorem simplexMaximum_lowerTail_sq_gt_sharp {d : ℕ} [NeZero d] (hd : 1000 ≤ d) :
    (273 / 100 : ℝ) < simplexMaximumExpectation d 1
      (fun m ↦ max (Real.log 6 - (d * m - Real.log d)) 0 ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  have hharm : 0 ≤ (harmonic d : ℝ) := by
    have hq : (0 : ℚ) ≤ harmonic d := by
      rw [harmonic]
      exact Finset.sum_nonneg fun i _ ↦ by positivity
    exact_mod_cast hq
  have haffine := affineMoment_strict_lower_sharp
    (D := (d : ℝ)) (H := (harmonic d : ℝ))
    (Q := SimplexIntegration.harmonicPowerSum d 2)
    (L := Real.log d) (A := Real.log 6)
    (by exact_mod_cast hd) hlog hharm (harmonic_sub_log_lt (by omega))
      (harmonicPowerSum_two_gt (by omega)) log_six_gt_sharp
  rw [← sharpMomentErrorPolynomial_eq] at haffine
  have haffine' :
      (12117 / 10000 : ℝ) ^ 2 + 41 / 25 - sharpMomentErrorRatio d <
        simplexMaximumExpectation d 1
          (fun m ↦ (Real.log 6 + Real.log d - d * m) ^ 2) := by
    rw [simplexMaximumExpectation_affine_sq]
    simpa [sharpMomentErrorRatio, SimplexIntegration.harmonicPowerSum_one] using haffine
  have htail := simplexMaximumExpectation_upperTail_sq_le hd1
  have herror := sharpMomentErrorRatio_nat_le hd
  have hendpoint :
      (273 / 100 : ℝ) < (12117 / 10000) ^ 2 + 41 / 25 - 1 / 3 -
        sharpMomentErrorPolynomial (1727 / 250) / 1000 := by
    norm_num [sharpMomentErrorPolynomial]
  rw [simplexMaximumExpectation_lowerTail_eq]
  nlinarith

/-- The sharpened weighted-simplex moment at every positive radius and order at least `1000`. -/
theorem weightedSimplexMoment_gt_sharp {d : ℕ} (hd : 1000 ≤ d)
    {W : ℝ} (hW : 0 < W) :
    (273 / 100 : ℝ) <
      SimplexIntegration.weightedSimplexExpectation d W
        (fun u ↦ (max (Real.log (6 * d) -
          (d : ℝ) * SimplexIntegration.weightedRadius u / W) 0) ^ 2) := by
  let _ : NeZero d := ⟨by omega⟩
  let f : ℝ → ℝ := fun m ↦ max (Real.log 6 - ((d : ℝ) * m - Real.log d)) 0 ^ 2
  have h := simplexMaximum_lowerTail_sq_gt_sharp (d := d) hd
  rw [simplexMaximumExpectation_eq_weightedRadius (W := 1) one_pos
    (fun m ↦ max (Real.log 6 - (d * m - Real.log d)) 0 ^ 2) (by fun_prop)] at h
  have hscale := weightedSimplexExpectation_scale (d := d) hW f
  rw [← hscale] at h
  dsimp only [f] at h
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hdpos.ne']
  have hfun :
      (fun u : Fin d → ℝ ↦ (max (Real.log 6 + Real.log d -
        (d : ℝ) * SimplexIntegration.weightedRadius u / W) 0) ^ 2) =
      (fun u ↦ max (Real.log 6 - ((d : ℝ) *
        (SimplexIntegration.weightedRadius u / W) - Real.log d)) 0 ^ 2) := by
    funext u
    congr 2
    ring
  rw [hfun]
  exact h

end ReedSolomon.HiddenDerivative.RatePartition
