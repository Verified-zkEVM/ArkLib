/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import Mathlib.Tactic.Linarith

/-!
# Comparing order-zero and order-one stage charges

A stage of the first-order curve bound is charged its joint degree, weighted by a joint incidence
ratio `s`, plus its fixed-fiber degree, weighted by the accidental-agreement factor `c`
(`c = ℓ (n - L)` in the curve bound). An order-one stage also carries the direct joint incidence
factor `η` and the fiber incidence ratio `t`. At an order-zero stage of total jet degree `v`, the
charge is `s (h b + v (ℓ + τ h)) + c v` with `b = 1 + τ (v - 1)` (`orderZeroCurveStageCharge`);
at an order-one stage it is `s η J + c t B` for the joint and fixed-fiber stage degrees `J` and `B`
(`orderOneCurveStageCharge`).

Both charges are monotone in the total jet degree, and the order-one charge is monotone in the
first-derivative degree. When `η` and `t` are at least `1`, an order-one stage costs at least
the order-zero stage of the same total jet degree, so separant descent may charge only the
highest `M` stages at order one.

## Main statements

* `orderZeroCurveStageCharge_mono`, `orderOneCurveStageCharge_mono_total`,
  `orderOneCurveStageCharge_mono_derivative`: monotonicity of the charges.
* `orderZeroCurveStageCharge_le_orderOne`: order one dominates order zero.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

/-- The charge `s (h b + v (ℓ + τ h)) + c v` of an order-zero stage of total jet degree `v`, with
`b = 1 + τ (v - 1)`, joint incidence ratio `s` and accidental-agreement factor `c`. -/
def orderZeroCurveStageCharge (ell h : ℕ) (s c : ℚ) (v τ : ℕ) : ℚ :=
  s * ((h * firstOrderTaylorTotalCap v τ + v * (ell + τ * h) : ℕ) : ℚ) + c * v

/-- The charge `s η J + c t B` of an order-one stage of total jet degree `v` and first-derivative
degree `r`, where `J` and `B` are its joint and fixed-fiber degrees, `s` and `η` are the split and
direct joint incidence factors, `t` is the fiber incidence ratio and `c` is the
accidental-agreement factor. -/
def orderOneCurveStageCharge (K ell h : ℕ) (s t c : ℚ) (v r τ : ℕ) (η : ℚ) : ℚ :=
  s * η * (firstOrderCurveJointStageOne K ell h v r τ : ℚ) +
    c * t * (firstOrderCurveFiberStageOne K v r τ : ℚ)

/-- For `0 ≤ s` and `0 ≤ c`, the order-zero charge is nonnegative. -/
theorem orderZeroCurveStageCharge_nonneg (ell h : ℕ) {s c : ℚ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (v τ : ℕ) : 0 ≤ orderZeroCurveStageCharge ell h s c v τ := by
  unfold orderZeroCurveStageCharge
  positivity

/-- For nonnegative factors, the order-one charge is nonnegative. -/
theorem orderOneCurveStageCharge_nonneg (K ell h : ℕ) {s η t c : ℚ} (hs : 0 ≤ s) (hη : 0 ≤ η)
    (ht : 0 ≤ t) (hc : 0 ≤ c) (v r τ : ℕ) : 0 ≤ orderOneCurveStageCharge K ell h s t c v r τ η := by
  unfold orderOneCurveStageCharge
  positivity

/-- For `0 ≤ s` and `0 ≤ c`, the order-zero charge is monotone in the total jet degree. -/
theorem orderZeroCurveStageCharge_mono (ell h : ℕ) {s c : ℚ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (τ : ℕ) : Monotone fun v ↦ orderZeroCurveStageCharge ell h s c v τ := by
  intro v w hvw
  have hjoint : h * firstOrderTaylorTotalCap v τ + v * (ell + τ * h) ≤
      h * firstOrderTaylorTotalCap w τ + w * (ell + τ * h) := by
    gcongr
    exact firstOrderTaylorTotalCap_mono hvw
  change orderZeroCurveStageCharge ell h s c v τ ≤ orderZeroCurveStageCharge ell h s c w τ
  unfold orderZeroCurveStageCharge
  gcongr

/-- For nonnegative factors and `v ≤ w`, the order-one charge at `v` is at most the one at
`w`. -/
theorem orderOneCurveStageCharge_mono_total (K ell h : ℕ) {s η t c : ℚ} (hs : 0 ≤ s)
    (hη : 0 ≤ η) (ht : 0 ≤ t) (hc : 0 ≤ c) (τ : ℕ) {v w r : ℕ} (hvw : v ≤ w) :
    orderOneCurveStageCharge K ell h s t c v r τ η ≤
      orderOneCurveStageCharge K ell h s t c w r τ η := by
  unfold orderOneCurveStageCharge
  gcongr
  · exact firstOrderCurveJointStageOne_mono_total hvw
  · exact firstOrderCurveFiberStageOne_mono_total hvw

/-- For nonnegative factors and `r ≤ q ≤ v`, the order-one charge at first-derivative degree `r`
is at most the one at `q`. -/
theorem orderOneCurveStageCharge_mono_derivative (K ell h : ℕ) {s η t c : ℚ} (hs : 0 ≤ s)
    (hη : 0 ≤ η) (ht : 0 ≤ t) (hc : 0 ≤ c) (τ : ℕ) {v r q : ℕ} (hrq : r ≤ q) (hqv : q ≤ v) :
    orderOneCurveStageCharge K ell h s t c v r τ η ≤
      orderOneCurveStageCharge K ell h s t c v q τ η := by
  unfold orderOneCurveStageCharge
  gcongr
  · exact firstOrderCurveJointStageOne_mono_derivative hrq hqv
  · exact firstOrderCurveFiberStageOne_mono_derivative hrq hqv

/-- For `2 ≤ K`, `0 ≤ s`, `1 ≤ η`, `1 ≤ t` and `0 ≤ c`, the order-zero charge at total jet degree
`v` is at most the order-one charge at total jet degree `v` and first-derivative degree `1`. -/
theorem orderZeroCurveStageCharge_le_orderOne (K ell h : ℕ) {s η t c : ℚ} (hK : 2 ≤ K)
    (hs : 0 ≤ s) (hη : 1 ≤ η) (ht : 1 ≤ t) (hc : 0 ≤ c) (v τ : ℕ) :
    orderZeroCurveStageCharge ell h s c v τ ≤ orderOneCurveStageCharge K ell h s t c v 1 τ η := by
  have hcap := firstOrderTaylorDerivativeCap_pos (j := v) (r := 1) (τ := τ) hK
  have hfiber : v ≤ firstOrderCurveFiberStageOne K v 1 τ := le_firstOrderCurveFiberStageOne hK
  have hjoint : h * firstOrderTaylorTotalCap v τ + v * (ell + τ * h) ≤
      firstOrderCurveJointStageOne K ell h v 1 τ := by
    unfold firstOrderCurveJointStageOne cappedBidegreeMixedVolume
    refine Nat.add_le_add (Nat.mul_le_mul_left h (le_cappedDegreeMixedVolume hcap)) ?_
    calc
      v * (ell + τ * h) ≤ 1 * (ell + τ * h) * firstOrderCurveFiberStageOne K v 1 τ := by
        rw [one_mul, mul_comm]
        exact Nat.mul_le_mul_left _ hfiber
      _ ≤ 2 * (ell + τ * h) * firstOrderCurveFiberStageOne K v 1 τ := by gcongr; norm_num
  have hsη : s ≤ s * η := le_mul_of_one_le_right hs hη
  have hct : c ≤ c * t := le_mul_of_one_le_right hc ht
  unfold orderZeroCurveStageCharge orderOneCurveStageCharge
  exact add_le_add
    (mul_le_mul hsη (by exact_mod_cast hjoint) (by positivity)
      (mul_nonneg (by linarith) (by linarith)))
    (mul_le_mul hct (by exact_mod_cast hfiber) (by positivity) (mul_nonneg hc (by linarith)))

end ReedSolomon.HiddenDerivative
