/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedBidegree

/-!
# Stage-degree acceptance tests

Stage degrees and the curve bound at small parameters, the affine-degree bounds that the stage
degrees are designed for, the expanded forms of the stage degrees, and cases showing that the
hypotheses `2 ≤ K`, `r ≤ q` and `r ≤ j` are needed.
-/

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

/-! ### Stage degrees at `K = 3`, `j = 3`, `r = 1`, `τ = 2` -/

/-- The total-degree cap is `1 + 2 · 2 = 5`. -/
example : firstOrderTaylorTotalCap 3 2 = 5 := rfl

/-- The first-derivative cap is `min 5 (0 + 2) = 2`. -/
example : firstOrderTaylorDerivativeCap 3 3 1 2 = 2 := rfl

/-- The fixed-fiber degree is `3 · 2 + 1 · (5 - 2) = 9`. -/
example : firstOrderCurveFiberStageOne 3 3 1 2 = 9 := rfl

/-- With `ℓ = h = 1`, the joint degree is `1 · (5 · 2 + 2 · 3) + 2 · 3 · 9 = 70`. -/
example : firstOrderCurveJointStageOne 3 1 1 3 1 2 = 70 := rfl

/-- The fixed-fiber degree is below the uncapped value `j b = 15`. -/
example : firstOrderCurveFiberStageOne 3 3 1 2 ≤ 3 * firstOrderTaylorTotalCap 3 2 :=
  firstOrderCurveFiberStageOne_le_mul_totalCap (by norm_num)

/-! ### The curve bound at `μ = 3`, `M = 1` -/

/-- Two order-zero stages of total jet degrees `1` and `2` give `4 + 9 = 13`. -/
theorem firstOrderCurveJointZero_three_one : firstOrderCurveJointZero 3 1 1 1 2 = 13 := by decide

/-- The order-zero fiber degrees are `1 + 2 = 3`. -/
theorem firstOrderCurveFiberZero_three_one : firstOrderCurveFiberZero 3 1 = 3 := by decide

/-- The single order-one stage has total jet degree `3` and first-derivative degree `1`. -/
theorem firstOrderCurveFiberOne_three_one : firstOrderCurveFiberOne 3 3 1 2 = 9 := by decide

/-- The joint degree of the single order-one stage. -/
theorem firstOrderCurveJointOne_three_one : firstOrderCurveJointOne 3 3 1 1 1 2 = 70 := by
  decide

/-- At `n = 8`, `k = 2`, `L = 3`, `A = 4` and `η = 1`, the ratios are `λ₁ = 3` and `λ₂ = 7/2`,
and the bound is `1 + 3 · 13 + 3 · 70 + 5 · (3 + 7/2 · 9) = 845/2`. -/
example : firstOrderCurveBound 8 3 2 3 4 3 1 1 1 2 1 = 845 / 2 := by
  simp only [firstOrderCurveBound, firstOrderCurveJointZero_three_one,
    firstOrderCurveFiberZero_three_one, firstOrderCurveFiberOne_three_one,
    firstOrderCurveJointOne_three_one]
  norm_num

/-- A larger direct incidence factor gives a larger bound. -/
example : firstOrderCurveBound 8 3 2 3 4 3 1 1 1 2 1 ≤ firstOrderCurveBound 8 3 2 3 4 3 1 1 1 2 2 :=
  firstOrderCurveBound_mono_directFactor 8 3 2 3 4 3 1 1 1 2 (by norm_num)

/-! ### The affine-degree bounds -/

/-- The fixed-fiber stage degree bounds the affine degree of the pullback of a curve with bounds
`(j, r)` along the Taylor monomial map. -/
example {k : Type*} [Field k] {K j r τ : ℕ} (hK : 2 ≤ K) {g : MvPolynomial (Fin 2) k}
    (hg0 : g ≠ 0) (hg : g ∈ restrictCappedDegree (Fin 2) k 1 j r) :
    affineDegree ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1
      (firstOrderTaylorTotalCap j τ) (firstOrderTaylorDerivativeCap K j r τ)))) ≤
      (firstOrderCurveFiberStageOne K j r τ : ℕ) :=
  affineDegree_comap_cappedDegree_span_singleton_le (by simp [firstOrderTaylorTotalCap])
    (firstOrderTaylorDerivativeCap_pos hK) hg0 hg

/-- The joint stage degree bounds the affine degree of the pullback of a hypersurface with
bounds `(h, j, r)` along the Taylor monomial map with challenge coordinate. -/
example {k : Type*} [Field k] {K ell h j r τ : ℕ} (hK : 2 ≤ K) (hell : 0 < ell)
    {g : MvPolynomial (Option (Fin 2)) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedBidegree (Fin 2) k 1 h j r) :
    affineDegree ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents (Fin 2) 1
      (ell + τ * h) (firstOrderTaylorTotalCap j τ) (firstOrderTaylorDerivativeCap K j r τ)))) ≤
      (firstOrderCurveJointStageOne K ell h j r τ : ℕ) :=
  affineDegree_comap_cappedBidegree_span_singleton_le (by omega)
    (by simp [firstOrderTaylorTotalCap]) (firstOrderTaylorDerivativeCap_pos hK) hg0 hg

/-! ### Expanded forms -/

/-- The fixed-fiber stage degree is `j c + r (b - c)`. -/
example (K j r τ : ℕ) :
    firstOrderCurveFiberStageOne K j r τ =
      j * firstOrderTaylorDerivativeCap K j r τ +
        r * (firstOrderTaylorTotalCap j τ - firstOrderTaylorDerivativeCap K j r τ) :=
  rfl

/-- The joint stage degree is `h (2 b c - c²) + 2 (ℓ + τ h) B` for the fixed-fiber degree `B`. -/
example (K ell h j r τ : ℕ) :
    firstOrderCurveJointStageOne K ell h j r τ =
      h * (2 * firstOrderTaylorTotalCap j τ * firstOrderTaylorDerivativeCap K j r τ -
        firstOrderTaylorDerivativeCap K j r τ ^ 2) +
      2 * (ell + τ * h) * firstOrderCurveFiberStageOne K j r τ := by
  rw [firstOrderCurveJointStageOne, cappedBidegreeMixedVolume,
    cappedDegreeMixedVolume_self (firstOrderTaylorDerivativeCap_le_totalCap ..), Nat.mul_sub,
    sq, mul_comm (firstOrderTaylorDerivativeCap K j r τ) (2 * _)]
  rfl

/-- The joint stage degree increases with the total jet degree also when `r > j`. -/
example : firstOrderCurveJointStageOne 1 0 1 1 2 0 ≤ firstOrderCurveJointStageOne 1 0 1 2 2 0 :=
  firstOrderCurveJointStageOne_mono_total (by norm_num)

/-! ### Boundary cases -/

/-- `le_firstOrderCurveFiberStageOne` needs `2 ≤ K`: at `K = 1`, `j = 2`, `r = 0`, `τ = 0` the
first-derivative cap is `0` and the fixed-fiber degree is `0 < 2`. -/
example : firstOrderCurveFiberStageOne 1 2 0 0 = 0 := rfl

/-- `firstOrderCurveFiberStageOne_mono_derivative` needs `r ≤ q`: at `K = 3`, `j = 3`, `τ = 2`
the fixed-fiber degree is `14` at `r = 2` and `9` at `r = 1`. -/
example : firstOrderCurveFiberStageOne 3 3 2 2 = 14 ∧ firstOrderCurveFiberStageOne 3 3 1 2 = 9 :=
  ⟨rfl, rfl⟩

/-- `firstOrderCurveFiberStageOne_le_mul_totalCap` needs `r ≤ j`: at `K = 1`, `j = 1`, `r = 2`,
`τ = 0` the fixed-fiber degree is `2`, and `j b = 1`. -/
example : firstOrderCurveFiberStageOne 1 1 2 0 = 2 ∧ 1 * firstOrderTaylorTotalCap 1 0 = 1 :=
  ⟨rfl, rfl⟩

end ReedSolomon.HiddenDerivative
