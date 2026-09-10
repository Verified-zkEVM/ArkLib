/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
/-!
# Comparing the two regular-stage charges

Order-zero and order-one stages have different geometric dimensions. Their charges are
monotone in the total jet-degree cap, and an order-one stage costs at least the corresponding
order-zero stage. These facts let separant descent retain the first-derivative cap when
summing costs: only the highest `M` degree slots need the order-one charge.

The parameters `s`, `η`, and `t` represent the split joint, direct joint, and fiber incidence
ratios. The parameter `c` is the common factor `ell * (n - L)` for accidental agreements.
This module proves only algebraic comparisons of those charges; the geometric cardinality
theorem supplies them.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- Joint and accidental-agreement charge for one order-zero stage. -/
def curveStageZero (_K ell h : ℕ) (s c : ℚ) (v τ : ℕ) : ℚ :=
  s * ((h * (1 + τ * (v - 1)) + v * (ell + τ * h) : ℕ) : ℚ) + c * v

/-- Joint and accidental-agreement charge for one order-one stage. The direct joint ratio `η`
is independent of the split joint ratio `s`; both it and the common Taylor exponent are
explicit. -/
def curveStageOne (K ell h : ℕ) (s t c : ℚ) (v r τ : ℕ) (η : ℚ) : ℚ :=
  s * η * (firstOrderCurveJointStageOne K ell h v r τ : ℚ) +
    c * t * (firstOrderCurveFiberStageOne K v r τ : ℚ)

/-- Nonnegative incidence ratios give nonnegative order-zero charges. -/
theorem curveStageZero_nonneg (K ell h : ℕ) {s c : ℚ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (v τ : ℕ) : 0 ≤ curveStageZero K ell h s c v τ := by
  unfold curveStageZero
  positivity

/-- Nonnegative incidence factors give nonnegative order-one charges. -/
theorem curveStageOne_nonneg_of_factors (K ell h : ℕ) {s η t c : ℚ}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (v r τ : ℕ) : 0 ≤ curveStageOne K ell h s t c v r τ η := by
  unfold curveStageOne
  positivity

/-- Enlarging the jet cap can only increase the order-zero charge at any common exponent. -/
theorem curveStageZero_mono_of_exponent (K ell h : ℕ) {s c : ℚ}
    (hs : 0 ≤ s) (hc : 0 ≤ c) (τ : ℕ) :
    Monotone fun v ↦ curveStageZero K ell h s c v (τ := τ) := by
  intro v w hvw
  have hsub : v - 1 ≤ w - 1 := Nat.sub_le_sub_right hvw 1
  have hb : 1 + τ * (v - 1) ≤ 1 + τ * (w - 1) := by gcongr
  have hjoint : h * (1 + τ * (v - 1)) + v * (ell + τ * h) ≤
      h * (1 + τ * (w - 1)) + w * (ell + τ * h) := by gcongr
  unfold curveStageZero
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjoint) hs
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hvw) hc

/-- Enlarging the total jet degree can only increase the order-one charge when the actual
derivative degree is fixed. -/
theorem curveStageOne_mono_total_of_factors (K ell h : ℕ) {s η t c : ℚ}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (ht : 0 ≤ t) (hc : 0 ≤ c) (τ : ℕ)
    {v w r : ℕ} (hrv : r ≤ v) (hvw : v ≤ w) :
    curveStageOne K ell h s t c v r τ η ≤
      curveStageOne K ell h s t c w r τ η := by
  have hjoint := firstOrderCurveJointStageOne_mono_total
    (K := K) (ell := ell) (h := h) (τ := τ) hrv hvw
  have hfiber := firstOrderCurveFiberStageOne_mono_total (K := K) (τ := τ) hrv hvw
  unfold curveStageOne
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjoint) (mul_nonneg hs hη)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfiber) (mul_nonneg hc ht)

/-- Enlarging the actual first-derivative degree can only increase the order-one charge at
a fixed total jet degree. -/
theorem curveStageOne_mono_derivative_of_factors (K ell h : ℕ) {s η t c : ℚ}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (ht : 0 ≤ t) (hc : 0 ≤ c) (τ : ℕ)
    {v r q : ℕ} (hrq : r ≤ q) (hqv : q ≤ v) :
    curveStageOne K ell h s t c v r τ η ≤
      curveStageOne K ell h s t c v q τ η := by
  have hjoint := firstOrderCurveJointStageOne_mono_derivative
    (K := K) (ell := ell) (h := h) (τ := τ) hrq hqv
  have hfiber := firstOrderCurveFiberStageOne_mono_derivative (K := K) (τ := τ) hrq hqv
  unfold curveStageOne
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjoint) (mul_nonneg hs hη)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfiber) (mul_nonneg hc ht)

/-- At incidence ratios at least one, order one dominates order zero at every degree. -/
theorem curveStageZero_le_one_of_factors (K ell h : ℕ) {s η t c : ℚ}
    (hK : 2 ≤ K) (hs : 1 ≤ s) (hη : 1 ≤ η) (ht : 1 ≤ t) (hc : 0 ≤ c)
    (v τ : ℕ) :
    curveStageZero K ell h s c v τ ≤ curveStageOne K ell h s t c v 1 τ η := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have hη0 : 0 ≤ η := le_trans (by norm_num) hη
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  let b := firstOrderTaylorTotalCap v τ
  let cap := firstOrderTaylorDerivativeCap K v 1 τ
  have hb : 1 ≤ b := by unfold b firstOrderTaylorTotalCap; omega
  have hcap : 1 ≤ cap := by
    unfold cap firstOrderTaylorDerivativeCap
    apply le_min hb
    omega
  have hcapb : cap ≤ b := min_le_left _ _
  have hsquare : cap ^ 2 ≤ 2 * b * cap := by nlinarith
  have hzarea : (b : ℤ) ≤ 2 * b * cap - cap ^ 2 := by
    nlinarith
  have harea : b ≤ 2 * b * cap - cap ^ 2 := by exact_mod_cast hzarea
  have hvfiber : v ≤ firstOrderCurveFiberStageOne K v 1 τ := by
    simpa [firstOrderCurveFiberStageOne, b, cap] using
      (AffineHilbert.le_fixedFiberDerivativeImageDegree (j := v) (r := 1)
        (b := b) (c := cap) (by omega))
  have hjoint : h * (1 + τ * (v - 1)) + v * (ell + τ * h) ≤
      firstOrderCurveJointStageOne K ell h v 1 τ := by
    unfold firstOrderCurveJointStageOne
    dsimp only
    apply add_le_add
    · simpa [b, firstOrderTaylorTotalCap, cap, firstOrderTaylorDerivativeCap] using
        Nat.mul_le_mul_left h harea
    · calc
        v * (ell + τ * h) = (ell + τ * h) * v := by ring
        _ ≤ (ell + τ * h) * firstOrderCurveFiberStageOne K v 1 τ :=
          Nat.mul_le_mul_left _ hvfiber
        _ ≤ 2 * ((ell + τ * h) * firstOrderCurveFiberStageOne K v 1 τ) :=
          Nat.le_mul_of_pos_left _ (by decide)
        _ = 2 * (ell + τ * h) * firstOrderCurveFiberStageOne K v 1 τ := by ring
  have hsη : s ≤ s * η := by nlinarith
  have hct : c ≤ c * t := by nlinarith
  unfold curveStageZero curveStageOne
  apply add_le_add
  · exact mul_le_mul hsη (by exact_mod_cast hjoint) (by positivity) (mul_nonneg hs0 hη0)
  · exact mul_le_mul hct (by exact_mod_cast hvfiber) (by positivity) (mul_nonneg hc ht0)

end ReedSolomon.HiddenDerivative
