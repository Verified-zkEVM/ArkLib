/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.BranchwiseRate
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.FiniteRateParameters
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridRateEnvelope
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageComparison
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.Uniform
import Mathlib.Order.Interval.Finset.Nat

/-!
# First-order parameter acceptance tests

Small concrete checks for the first-order rate bounds, hybrid constants, rounded counts and curve
charges.
-/

namespace ReedSolomon.HiddenDerivative

open Filter Topology

private theorem rateSwitch_lt_half : firstOrderRateSwitch < 1 / 2 := by
  have h : (7 : ℝ) < 2 * Real.sqrt 13 := by
    have h13 : (7 / 2 : ℝ) < Real.sqrt 13 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  unfold firstOrderRateSwitch
  linarith

private theorem half_rate_threshold_lt_three_four :
    firstOrderRateThreshold (1 / 2) < 3 / 4 := by
  refine (firstOrderRateThreshold_lt_sqrt (by norm_num) (by norm_num)).trans ?_
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

private theorem lowRate_eighth_regime : FirstOrderLowRateRegime (1 / 8) := by
  rw [firstOrderLowRateRegime_iff_lt_rateSwitch, firstOrderRateSwitch]
  have hsqrt : Real.sqrt 13 < 29 / 8 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-! ### Rate bounds and branch selection -/

/-- At `R = 1/2`, the threshold lies strictly between `R` and `√R`. -/
example : (1 / 2 : ℝ) < firstOrderRateThreshold (1 / 2) ∧
    firstOrderRateThreshold (1 / 2) < Real.sqrt (1 / 2) := by
  exact ⟨rate_lt_firstOrderRateThreshold (by norm_num) (by norm_num),
    firstOrderRateThreshold_lt_sqrt (by norm_num) (by norm_num)⟩

/-- The clean expression is above one at `R = 1/2`, `a = 3/4`. -/
example : 1 < firstOrderCleanExpression (1 / 2) (3 / 4) :=
  firstOrderCleanExpression_gt_one (by norm_num) (by norm_num)
    half_rate_threshold_lt_three_four

/-- The exact rank density is below its cubic envelope at `β = 3/4`. -/
example : firstOrderRankDensity (3 / 4) ≤ firstOrderRankCubicEnvelope (3 / 4) :=
  firstOrderRankDensity_le_cubicEnvelope (3 / 4)

/-- The threshold equation holds at `R = 1/2`. -/
example : firstOrderCleanExpression (1 / 2) (firstOrderRateThreshold (1 / 2)) = 1 :=
  firstOrderCleanExpression_threshold_eq_one (by norm_num) (by norm_num)

/-- Below the branch switch, the stationary root gives `β > 1/2` and `ρ < a`. -/
example : FirstOrderLowRateRegime (1 / 10) ∧ 1 / 2 < firstOrderLowRateBeta (1 / 10) ∧
    (1 / 10 : ℝ) < firstOrderLowRateThreshold (1 / 10) := by
  have hlow : FirstOrderLowRateRegime (1 / 10) := by
    rw [firstOrderLowRateRegime_iff_lt_rateSwitch, firstOrderRateSwitch]
    have h : Real.sqrt 13 < 109 / 30 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
  exact ⟨hlow, half_lt_firstOrderLowRateBeta (by norm_num) hlow,
    rate_lt_firstOrderLowRateThreshold (by norm_num) hlow⟩

/-- At rate `1/8`, the branch beta is positive. -/
example : 0 < firstOrderBranchBeta (1 / 8) (3 / 4) :=
  firstOrderBranchBeta_pos (by norm_num) (by norm_num) (by norm_num)

/-- At rate `1/8` and agreement `1`, the low-rate source-minus-rank margin is positive. -/
example : 0 < firstOrderSourceDensity (1 / 8) 1 (firstOrderLowRateBeta (1 / 8)) -
    firstOrderRankDensity (firstOrderLowRateBeta (1 / 8)) := by
  apply firstOrderLowRate_margin_pos (by norm_num) lowRate_eighth_regime
  have ht : firstOrderLowRateScale (1 / 8) = 1 / 4 := by
    rw [firstOrderLowRateScale,
      show (1 / 8 : ℝ) / 2 = (1 / 4 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : 0 ≤ (1 / 4 : ℝ))]
  have hu : firstOrderLowRateStationaryU (1 / 8) < 1 := by
    by_contra h
    have hge : 1 ≤ firstOrderLowRateStationaryU (1 / 8) := le_of_not_gt h
    have hc := firstOrderLowRateStationaryU_cubic (rho := (1 / 8 : ℝ)) (by norm_num)
    rw [ht] at hc
    unfold firstOrderStationaryCubic at hc
    have hbound : 4 ≤ firstOrderLowRateStationaryU (1 / 8) ^ 2 *
        (firstOrderLowRateStationaryU (1 / 8) + 3) := by
      calc
        4 = (1 : ℝ) ^ 2 * (1 + 3) := by norm_num
        _ ≤ firstOrderLowRateStationaryU (1 / 8) ^ 2 *
            (firstOrderLowRateStationaryU (1 / 8) + 3) := by gcongr
    linarith
  rw [firstOrderLowRateThreshold_eq_scale_mul_one_add (by norm_num), ht]
  nlinarith [hu]

/-- At rate `1/8`, the positive stationary root exists and is the unique nonnegative root. -/
example : ∃ u : ℝ, 0 < u ∧
    firstOrderStationaryCubic u = firstOrderLowRateScale (1 / 8) ∧
    firstOrderStationaryCubic (firstOrderLowRateStationaryU (1 / 8)) =
      firstOrderLowRateScale (1 / 8) ∧
    u = firstOrderLowRateStationaryU (1 / 8) := by
  obtain ⟨u, hu, hcubic⟩ := exists_firstOrderStationaryRoot (rho := (1 / 8 : ℝ)) (by norm_num)
  exact ⟨u, hu, hcubic, firstOrderLowRateStationaryU_cubic (by norm_num),
    firstOrderLowRateStationaryU_unique (by norm_num) hu.le hcubic⟩

/-- The source-minus-envelope factorization at the chosen rate ratio. -/
example :
    firstOrderSourceDensity (1 / 2) (3 / 4) (firstOrderRateBeta (1 / 2) (3 / 4)) -
        firstOrderRankCubicEnvelope (firstOrderRateBeta (1 / 2) (3 / 4)) =
      firstOrderRateBeta (1 / 2) (3 / 4) / 2 *
        (firstOrderCleanExpression (1 / 2) (3 / 4) - 1) := by
  rw [firstOrderSourceDensity_sub_cubicEnvelope _ _ _ (by norm_num),
    firstOrderRateBeta_bracket _ _ (by norm_num) (by norm_num)]

/-- The piecewise ratio at `R = 1/2` lies below `a/R` when `a = 3/4`. -/
example : firstOrderBranchBeta (1 / 2) (3 / 4) < (3 / 4) / (1 / 2) := by
  have ha : firstOrderBranchThreshold (1 / 2) < 3 / 4 := by
    rw [firstOrderBranchThreshold_eq_clean rateSwitch_lt_half.le]
    exact half_rate_threshold_lt_three_four
  exact firstOrderBranchBeta_lt_agreement_div_rate (by norm_num) (by norm_num) ha

/-- The piecewise density surplus is positive at `R = 1/2`, `a = 3/4`. -/
example : firstOrderRankDensity (firstOrderBranchBeta (1 / 2) (3 / 4)) <
    firstOrderSourceDensity (1 / 2) (3 / 4) (firstOrderBranchBeta (1 / 2) (3 / 4)) :=
  firstOrderBranch_surplus_pos (by norm_num) (by norm_num)
    (by rw [firstOrderBranchThreshold_eq_clean rateSwitch_lt_half.le];
        exact half_rate_threshold_lt_three_four) (by norm_num)

/-! ### Rounded counts -/

/-- The derivative-order-one certified bound is `5` for multiplicity `2`, cap `1`. -/
example : certifiedEnlargedRankBound 1 2 1 0 = 5 := by
  rw [certifiedEnlargedRankBound_one_eq_firstOrderRankCount]
  decide

/-- The signed cubic count bounds the rank count at multiplicity `2`, cap `1`. -/
example : (firstOrderRankCount 2 1 : ℝ) ≤ firstOrderRankCubicUpperCount 2 1 :=
  firstOrderRankCount_le_cubicUpperCount 2 1

/-- The rounded rank estimate at `m = 4`, `β = 1/2`. -/
example : (firstOrderRankCount 4 ⌊(1 / 2 : ℝ) * 4⌋₊ : ℝ) ≤
    (4 : ℝ) ^ 3 * ((1 / 2 : ℝ) / 2 - (1 / 2) ^ 2 / 2 + (1 / 2) ^ 3 / 3) + 3 * 4 ^ 2 :=
  firstOrderRankCount_floor_le 4 (by norm_num) (by norm_num)

/-- At `m = 4` and `β = 1`, the exact upper-branch rank density gives `35 ≤ 4³ + 5·4²`. -/
example : ((35 : ℕ) : ℝ) ≤
    (4 : ℕ) ^ 3 * firstOrderRankDensity 1 + (2 * 1 + 3) * (4 : ℕ) ^ 2 := by
  have h := firstOrderRankCount_floor_le_density_add_rounding_upper
    (beta := 1) (by norm_num) 4
  have hM : ⌊(1 : ℝ) * (4 : ℕ)⌋₊ = 4 := by norm_num
  have hcount : firstOrderRankCount 4 4 = 35 := by decide
  rw [hM, hcount] at h
  norm_num [firstOrderRankDensity] at h ⊢

/-- At the branch boundary, the uniform rank estimate gives `23 ≤ 4³/6 + 4²·4`. -/
example : ((23 : ℕ) : ℝ) ≤
    (4 : ℕ) ^ 3 * firstOrderRankDensity (1 / 2) + (2 * (1 / 2) + 3) * (4 : ℕ) ^ 2 := by
  have h := firstOrderRankCount_floor_le_density_add_rounding
    (beta := 1 / 2) (by norm_num) 4
  have hM : ⌊(1 / 2 : ℝ) * (4 : ℕ)⌋₊ = 2 := by norm_num
  rw [hM, show firstOrderRankCount 4 2 = 23 by decide] at h
  norm_num [firstOrderRankDensity] at h ⊢

/-- At `R = 1/2`, `a = 1`, `β = 1/4`, `m = 64`, both rounding and finite-surplus bounds hold. -/
example :
    (64 : ℝ) ^ 3 * ((1 / 4 : ℝ) * 1 ^ 2 / (2 * (1 / 2)) -
      1 * (1 / 4) ^ 2 / 2 + (1 / 2) * (1 / 4) ^ 3 / 6) ≤
      firstOrderSourceCount (1 / 2) 1 64 ⌊(1 / 4 : ℝ) * 64⌋₊ 128 ∧
    (64 : ℝ) ^ 3 * (((1 / 4 : ℝ) * 1 ^ 2 / (2 * (1 / 2)) -
      1 * (1 / 4) ^ 2 / 2 + (1 / 2) * (1 / 4) ^ 3 / 6) -
      ((1 / 4 : ℝ) / 2 - (1 / 4) ^ 2 / 2 + (1 / 4) ^ 3 / 3)) - 3 * 64 ^ 2 ≤
      firstOrderSourceCount (1 / 2) 1 64 ⌊(1 / 4 : ℝ) * 64⌋₊ 128 -
        firstOrderRankCount 64 ⌊(1 / 4 : ℝ) * 64⌋₊ := by
  exact ⟨cube_mul_sourceDensity_le_firstOrderSourceCount (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    cube_mul_densityGap_sub_le_sourceCount_sub_rankCount (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-! ### Finite rate parameters -/

private def concreteFiniteParameters : FirstOrderFiniteRateParameters (1 / 2 : ℝ) (3 / 4 : ℝ) :=
  ⟨4, by norm_num, by norm_num [FirstOrderFiniteRateTest, firstOrderRateDerivativeCap,
    firstOrderRateJetDegree, firstOrderRateBeta, firstOrderSourceCount, firstOrderRankCount,
    Finset.sum_range_succ]⟩

/-- The rational finite test computes the same strict surplus, `17 < 18`. -/
example : FirstOrderRationalFiniteTest (1 / 2 : ℚ) (3 / 4 : ℚ) 4 := by
  norm_num [FirstOrderRationalFiniteTest, firstOrderRationalSourceCount,
    firstOrderRankCount, Finset.sum_range_succ]

/-- At the concrete certificate, the scaled kernel-height estimate is its challenge degree `102`. -/
example : 1 * concreteFiniteParameters.rankCount * concreteFiniteParameters.jetDegree /
      (18 - 1 * concreteFiniteParameters.rankCount) ≤
    concreteFiniteParameters.challengeDegree := by
  have hsurplus := concreteFiniteParameters.sourceCount_gt_rankCount
  have h := scaledKernelHeight_le_floor (n := 1) (N := 18)
    (r := concreteFiniteParameters.rankCount) (mu := concreteFiniteParameters.jetDegree)
    hsurplus (by
      norm_num [FirstOrderFiniteRateParameters.sourceCount, concreteFiniteParameters,
        FirstOrderFiniteRateParameters.derivativeCap, FirstOrderFiniteRateParameters.jetDegree,
        firstOrderRateDerivativeCap, firstOrderRateJetDegree, firstOrderRateBeta,
        firstOrderSourceCount, Finset.sum_range_succ])
  change 1 * concreteFiniteParameters.rankCount * concreteFiniteParameters.jetDegree /
      (18 - 1 * concreteFiniteParameters.rankCount) ≤
        max 1 ⌊(concreteFiniteParameters.rankCount : ℝ) * concreteFiniteParameters.jetDegree /
          (concreteFiniteParameters.sourceCount - concreteFiniteParameters.rankCount)⌋₊
  exact h.trans (le_max_right _ _)

/-- At rate `1/2`, agreement `3/4`, block length `4`, the scaled source count is at most `91`. -/
example :
    4 * firstOrderSourceCount (1 / 2) (3 / 4) 4 1 6 ≤
      firstOrderDimensionCount 2 3 4 1 6 := by
  apply firstOrderSourceCount_mul_le_firstOrderDimensionCount <;> norm_num

/-- A positive residual parameter preserves the source-to-rank residual comparison. -/
example : (2 : ℝ) * max (3 * (1 / 2 : ℝ) - (1 / 2) * 1) 0 ≤ max (3 * 2 - 1 * 1) 0 := by
  have h := mul_max_rateResidual_le_max_residual (rate := 1 / 2) (a := 1)
    (n := 2) (D := 1) (A := 2) (m := 3) (t := 1) (by norm_num) (by norm_num)
  norm_num at h ⊢

/-! ### Hybrid constants -/

/-- The fiber stage sum at `D = 2`, `μ = 3`, `e = M = 2` is bounded by `2DT`. -/
example : (regularFiberStageSum 2 3 2 : ℝ) ≤ 2 * 2 * stageStaircase 3 2 :=
  regularFiberStageSum_cast_le (by norm_num) (by norm_num) (by norm_num)

/-- The joint stage sum at `D = 2`, `h = 1`, `μ = 3`, `e = M = 2` is bounded by its charge. -/
example : (regularJointStageSum 2 1 3 2 : ℝ) ≤
    (12 * 2 ^ 2 * 1 + 4 * 2) * stageStaircase 3 2 := by
  have h := regularJointStageSum_cast_le (D := 2) (h := 1) (μ := 3) (M := 2) (e := 2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  all_goals exact h

/-- The list charge increases from stage `0` to stage `1` at `θ = D = 1`, `μ = 2`. -/
example : firstOrderListCharge 1 1 2 0 ≤ firstOrderListCharge 1 1 2 1 :=
  firstOrderListCharge_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Both balanced-split coordinate ratios are at most `2θ` for `n = 10`, `D = 1`, `A = 4`. -/
example : retainedCoordinateRatio 10 4 (balancedSplit 1 4) ≤
      2 * agreementIncidenceRatio 10 1 4 ∧
    fixedCoordinateRatio 10 1 (balancedSplit 1 4) ≤ 2 * agreementIncidenceRatio 10 1 4 := by
  exact ⟨retainedCoordinateRatio_balancedSplit_le (by norm_num) (by norm_num),
    fixedCoordinateRatio_balancedSplit_le 10 1 4⟩

/-- The optimized list charge is below its closed constant at `θ = D = 1`, `μ = 2`, `M = 1`. -/
example : maxFirstOrderListCharge 1 1 2 1 ≤ firstOrderListConstant 1 1 2 1 :=
  maxFirstOrderListCharge_le_firstOrderListConstant (by norm_num) (by norm_num) (by norm_num)

/-- The optimized exception charge is below its closed constant for `n = 4`, `D = 1`, `A = 3`. -/
example : maxMinFirstOrderExceptionCharge (agreementIncidenceRatio 4 1 3) 4 1 3 1 2 0 ≤
    firstOrderExceptionConstant (agreementIncidenceRatio 4 1 3) 4 1 1 2 0 :=
  maxMinFirstOrderExceptionCharge_le_firstOrderExceptionConstant (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Concrete list and balanced-split exception charges satisfy their direct closed bounds. -/
example : firstOrderListCharge 1 1 2 1 ≤ firstOrderListConstant 1 1 2 1 ∧
    firstOrderExceptionCharge (agreementIncidenceRatio 4 1 3) 4 1 3 1 2 1
        (balancedSplit 1 3) ≤
      firstOrderExceptionConstant (agreementIncidenceRatio 4 1 3) 4 1 1 2 1 := by
  exact ⟨firstOrderListCharge_le_firstOrderListConstant (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),
    firstOrderExceptionCharge_balancedSplit_le (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)⟩

/-! ### Rate and polynomial envelopes -/

/-- For rate fraction `1/4` and agreement fraction `1/2`, the incidence ratio is at most `4`. -/
example : agreementIncidenceRatio 4 1 2 ≤ 1 / ((1 / 2 : ℝ) - 1 / 4) := by
  exact agreementIncidenceRatio_le_one_div_sub (n := 4) (D := 1) (A := 2)
    (ρ := 1 / 4) (a := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The cubic envelope at `C = θ = 1`, `q = n = μ = 2`, and `D = M = 1`. -/
example : firstOrderListConstant 1 1 2 1 ≤ 48 := by
  have h := firstOrderListConstant_le_cubic (C := 1) (q := 2) (θ := 1) (n := 2) (D := 1)
    (μ := 2) (M := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [stageStaircase])
  norm_num at h ⊢
  exact h

/-- The quintic envelope at `C = θ = 1`, `q = n = μ = 2`, and `D = M = h = 1`. -/
example : firstOrderExceptionConstant 1 2 1 1 2 1 ≤ 5760 := by
  have h := firstOrderExceptionConstant_le_quintic (C := 1) (q := 2) (θ := 1) (n := 2) (D := 1)
    (h := 1) (μ := 2) (M := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [stageStaircase])
  norm_num at h ⊢
  exact h

/-! ### Curve charges -/

/-- Increasing total degree or derivative degree increases the concrete stage charges. -/
example : orderZeroCurveStageCharge 1 1 1 1 1 1 ≤ orderZeroCurveStageCharge 1 1 1 1 2 1 ∧
    orderOneCurveStageCharge 3 1 1 1 1 1 1 1 1 1 ≤
      orderOneCurveStageCharge 3 1 1 1 1 1 2 1 1 1 ∧
    orderOneCurveStageCharge 3 1 1 1 1 1 2 0 1 1 ≤
      orderOneCurveStageCharge 3 1 1 1 1 1 2 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (orderZeroCurveStageCharge_mono 1 1 (s := 1) (c := 1)
      (by norm_num) (by norm_num) 1) (by norm_num)
  · exact (orderOneCurveStageCharge_mono_total 3 1 1 (s := 1) (η := 1) (t := 1) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1) (by norm_num)
  · exact orderOneCurveStageCharge_mono_derivative 3 1 1 (s := 1) (η := 1) (t := 1) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num)

/-- The order-one fiber degree is bounded by `j` times the total Taylor cap. -/
example : 2 ≤ firstOrderCurveFiberStageOne 3 2 1 2 ∧
    firstOrderCurveFiberStageOne 3 3 1 2 ≤ 3 * firstOrderTaylorTotalCap 3 2 := by
  exact ⟨le_firstOrderCurveFiberStageOne (by norm_num),
    firstOrderCurveFiberStageOne_le_mul_totalCap (by norm_num)⟩

/-- The fiber and joint stage degrees are monotone in total jet degree for concrete parameters. -/
example : firstOrderCurveFiberStageOne 3 2 1 2 ≤ firstOrderCurveFiberStageOne 3 3 1 2 ∧
    firstOrderCurveJointStageOne 3 1 1 2 1 2 ≤ firstOrderCurveJointStageOne 3 1 1 3 1 2 := by
  exact ⟨firstOrderCurveFiberStageOne_mono_total (by norm_num),
    firstOrderCurveJointStageOne_mono_total (by norm_num)⟩

/-- The fiber and joint stage degrees are monotone in derivative degree at concrete parameters. -/
example : firstOrderCurveFiberStageOne 3 3 1 2 ≤ firstOrderCurveFiberStageOne 3 3 2 2 ∧
    firstOrderCurveJointStageOne 3 1 1 3 1 2 ≤ firstOrderCurveJointStageOne 3 1 1 3 2 2 := by
  exact ⟨firstOrderCurveFiberStageOne_mono_derivative (by norm_num) (by norm_num),
    firstOrderCurveJointStageOne_mono_derivative (by norm_num) (by norm_num)⟩

/-- The curve bound is monotone when the direct incidence factor rises from `1` to `2`. -/
example : firstOrderCurveBound 8 3 2 3 4 3 1 1 1 2 1 ≤
    firstOrderCurveBound 8 3 2 3 4 3 1 1 1 2 2 :=
  firstOrderCurveBound_mono_directFactor 8 3 2 3 4 3 1 1 1 2 (by norm_num)

/-- At `K = 3`, the order-zero charge is below the order-one charge at `v = 3`. -/
example : orderZeroCurveStageCharge 1 1 1 1 3 2 ≤
    orderOneCurveStageCharge 3 1 1 1 1 1 3 1 2 1 :=
  orderZeroCurveStageCharge_le_orderOne 3 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 3 2

/-! ### Fixed shifted-height certificate -/

/-- At `n = A = 3` and `k = 2`, the fixed height-851 source has a strict slot surplus. -/
example : firstOrderCurveShiftedRowSlotBound 1 3 12 4 22 3 1 851 <
    firstOrderCurveShiftedHeightSlotCount 1 3 12 4 22 1 851 := by
  have h := uniformFirstOrder_parameters 3 2 3 (by norm_num) (by norm_num)
  exact h.2.2.2

set_option maxRecDepth 4096 in
/-- The fixed graded-rank profile through grade `22`. -/
example : List.ofFn (fun t : Fin 23 ↦ uniformFirstOrderGradedRankProfile t) =
    [12, 22, 30, 36, 40, 35, 30, 25, 20, 16, 12, 9, 6, 4, 2, 1,
      0, 0, 0, 0, 0, 0, 0] := by decide

set_option maxRecDepth 4096 in
/-- The fixed graded-rank profile sums to `300` through grade `22`. -/
example : ∑ t ∈ Finset.range 23, uniformFirstOrderGradedRankProfile t = 300 := by decide

set_option maxRecDepth 4096 in
/-- The grade-weighted fixed profile sums to `1570` through grade `22`. -/
example : ∑ t ∈ Finset.range 23, t * uniformFirstOrderGradedRankProfile t = 1570 := by decide

end ReedSolomon.HiddenDerivative
