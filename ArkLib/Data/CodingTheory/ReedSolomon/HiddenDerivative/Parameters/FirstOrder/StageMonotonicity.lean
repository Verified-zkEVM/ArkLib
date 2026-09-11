/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageCharges

/-!
# Monotonicity in the reconstruction degree

Increasing both Taylor coordinate budgets preserves the cap-sensitive image bounds.
These comparisons retain the intrinsic condition that derivative degree is at most total degree.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

/-- Increasing the reconstruction and denominator degrees increases the fiber stage bound. -/
theorem firstOrderCurveFiberStageOne_mono_reconstruction {K K' j r τ τ' : ℕ}
    (hrj : r ≤ j) (hK : K ≤ K') (hτ : τ ≤ τ') :
    firstOrderCurveFiberStageOne K j r τ ≤ firstOrderCurveFiberStageOne K' j r τ' := by
  have hb : firstOrderTaylorTotalCap j τ ≤ firstOrderTaylorTotalCap j τ' := by
    unfold firstOrderTaylorTotalCap
    gcongr
  have hc : firstOrderTaylorDerivativeCap K j r τ ≤
      firstOrderTaylorDerivativeCap K' j r τ' := by
    unfold firstOrderTaylorDerivativeCap
    apply min_le_min hb
    gcongr
  have hcb : firstOrderTaylorDerivativeCap K j r τ ≤ firstOrderTaylorTotalCap j τ :=
    min_le_left _ _
  have hcb' : firstOrderTaylorDerivativeCap K' j r τ' ≤ firstOrderTaylorTotalCap j τ' :=
    min_le_left _ _
  simp only [firstOrderCurveFiberStageOne,
    AffineHilbert.fixedFiberDerivativeImageDegree_eq hrj hcb,
    AffineHilbert.fixedFiberDerivativeImageDegree_eq hrj hcb']
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hb)

/-- The same reconstruction enlargement increases the joint stage bound. -/
theorem firstOrderCurveJointStageOne_mono_reconstruction {K K' ell h j r τ τ' : ℕ}
    (hrj : r ≤ j) (hK : K ≤ K') (hτ : τ ≤ τ') :
    firstOrderCurveJointStageOne K ell h j r τ ≤
      firstOrderCurveJointStageOne K' ell h j r τ' := by
  have hB := firstOrderCurveFiberStageOne_mono_reconstruction hrj hK hτ
  let b := firstOrderTaylorTotalCap j τ
  let b' := firstOrderTaylorTotalCap j τ'
  let c := firstOrderTaylorDerivativeCap K j r τ
  let c' := firstOrderTaylorDerivativeCap K' j r τ'
  have hb : b ≤ b' := by
    unfold b b' firstOrderTaylorTotalCap
    gcongr
  have hc : c ≤ c' := by
    unfold c c' firstOrderTaylorDerivativeCap
    apply min_le_min hb
    gcongr
  have hcb : c ≤ b := min_le_left _ _
  have hcb' : c' ≤ b' := min_le_left _ _
  have harea : 2 * b * c - c ^ 2 ≤ 2 * b' * c' - c' ^ 2 := by
    have h₁ : c ^ 2 ≤ 2 * b * c := by nlinarith
    have h₂ : c' ^ 2 ≤ 2 * b' * c' := by nlinarith
    have hz : (2 * b * c - c ^ 2 : ℤ) ≤ 2 * b' * c' - c' ^ 2 := by
      nlinarith
    exact_mod_cast hz
  unfold firstOrderCurveJointStageOne AffineHilbert.mixedDerivativeImageDegree
  exact Nat.add_le_add (Nat.mul_le_mul_left h harea)
    (Nat.mul_le_mul (by gcongr) hB)

/-- Promoting an ordinary stage to order one cannot decrease its joint charge. -/
theorem ordinaryJointStage_le_firstOrderCurveJointStageOne {K ell h j r τ : ℕ}
    (hK : 2 ≤ K) :
    h * firstOrderTaylorTotalCap j τ + j * (ell + τ * h) ≤
      firstOrderCurveJointStageOne K ell h j r τ := by
  let b := firstOrderTaylorTotalCap j τ
  let c := firstOrderTaylorDerivativeCap K j r τ
  have hc : 1 ≤ c := by
    unfold c firstOrderTaylorDerivativeCap firstOrderTaylorTotalCap
    apply le_min (by omega)
    omega
  have hcb : c ≤ b := min_le_left _ _
  have harea : b ≤ 2 * b * c - c ^ 2 := by
    have h₁ := Nat.mul_le_mul_left b hc
    have h₂ := Nat.mul_le_mul_left c hcb
    have hsub := Nat.sub_add_cancel (show c ^ 2 ≤ 2 * b * c by nlinarith)
    nlinarith
  have hf := le_firstOrderCurveFiberStageOne (j := j) (r := r) (τ := τ) hK
  change h * b + j * (ell + τ * h) ≤
    h * (2 * b * c - c ^ 2) + 2 * (ell + τ * h) * firstOrderCurveFiberStageOne K j r τ
  rw [Nat.mul_comm j]
  exact Nat.add_le_add (Nat.mul_le_mul_left h harea)
    (Nat.mul_le_mul (by omega) hf)

end ReedSolomon.HiddenDerivative
