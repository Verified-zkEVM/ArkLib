/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Bounds
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthParameters
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.FiniteLengthSelectors
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# First-order Reed–Solomon list-bound acceptance cases

Concrete examples exercise the automatic complete-list theorem and the profile-based finite-family
theorem over `ℚ`.
-/

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative
open ReedSolomon.FirstOrder ReedSolomon.FirstOrder.Squarefree

private def rationalEvaluationDomain : Fin 4 ↪ ℚ :=
  ⟨fun i ↦ (i.val : ℚ), fun i j h ↦ by
    change (i.val : ℚ) = (j.val : ℚ) at h
    exact Fin.ext (by exact_mod_cast h)⟩

private noncomputable def classicalRationalClosePolynomialSet (A : ℕ) : Set ℚ[X] :=
  @closePolynomialSet ℚ (inferInstance : Field ℚ)
    (fun x y ↦ Classical.propDecidable (x = y)) 4 rationalEvaluationDomain (fun _ ↦ 0) 2 A

private noncomputable def classicalRationalLowDimensionClosePolynomialSet : Set ℚ[X] :=
  @closePolynomialSet ℚ (inferInstance : Field ℚ)
    (fun x y ↦ Classical.propDecidable (x = y)) 4 rationalEvaluationDomain (fun _ ↦ 0) 1 1

private theorem half_rate_threshold_lt_three_quarters :
    firstOrderRateThreshold (1 / 2 : ℝ) < 3 / 4 := by
  rw [firstOrderRateThreshold]
  have hroot : Real.sqrt (27 / 8 : ℝ) < 33 / 16 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 33 / 16)]
    norm_num
  rw [show (1 / 2 : ℝ) * (5 - 1 / 2) * (2 - 1 / 2) = 27 / 8 by norm_num]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 8 - 1 / 2)]
  nlinarith

open Classical in
/-- The complete list over `ℚ` is finite and contains the zero polynomial. -/
example :
    (classicalRationalClosePolynomialSet (Nat.ceil ((3 / 4 : ℝ) * 4))).Finite ∧
      (0 : ℚ[X]) ∈ classicalRationalClosePolynomialSet (Nat.ceil ((3 / 4 : ℝ) * 4)) ∧
      ((classicalRationalClosePolynomialSet (Nat.ceil ((3 / 4 : ℝ) * 4))).ncard : ℝ) ≤
        firstOrderListConstant
          (agreementIncidenceRatio 4 (2 - 1) (Nat.ceil ((3 / 4 : ℝ) * 4))) (2 - 1)
          (automaticJetDegree (1 / 2) (3 / 4)) (automaticDerivativeCap (1 / 2) (3 / 4)) := by
  obtain ⟨hfinite, _hraw, _hceil, hclosed⟩ :=
    automaticFirstOrder_closePolynomialSet_at_ceil_finite_and_card_le
      (rho := 1 / 2) (a := 3 / 4) (n := 4) (k := 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      half_rate_threshold_lt_three_quarters (by norm_num : (3 / 4 : ℝ) < 1)
      (by norm_num : 0 < 4) (by norm_num : 2 ≤ 2)
      (by norm_num : (2 : ℝ) ≤ (1 / 2) * 4)
      rationalEvaluationDomain (fun _ ↦ 0)
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  change (classicalRationalClosePolynomialSet (Nat.ceil ((3 / 4 : ℝ) * 4))).Finite at hfinite
  change
    ((classicalRationalClosePolynomialSet (Nat.ceil ((3 / 4 : ℝ) * 4))).ncard : ℝ) ≤
      firstOrderListConstant
        (agreementIncidenceRatio 4 (2 - 1) (Nat.ceil ((3 / 4 : ℝ) * 4))) (2 - 1)
        (automaticJetDegree (1 / 2) (3 / 4))
        (automaticDerivativeCap (1 / 2) (3 / 4)) at hclosed
  refine ⟨hfinite, ?_⟩
  refine ⟨?_, hclosed⟩
  unfold classicalRationalClosePolynomialSet closePolynomialSet
  simp only [Set.mem_ofPred_eq]
  exact ⟨WithBot.bot_lt_coe 2,
    by norm_num [polynomialAgreementSet, rationalEvaluationDomain]⟩

open Classical in
/-- The automatic finite-rate theorem bounds the complete rational close-polynomial set. -/
example :
    (classicalRationalClosePolynomialSet 3).Finite ∧
      ((classicalRationalClosePolynomialSet 3).ncard : ℝ) ≤
        maxFirstOrderListCharge (agreementIncidenceRatio 4 1 3) 1
          (automaticJetDegree (1 / 2) (3 / 4))
          (automaticDerivativeCap (1 / 2) (3 / 4)) := by
  obtain ⟨hfinite, hraw, _, _⟩ :=
    automaticFirstOrder_closePolynomialSet_finite_and_card_le
      (rho := 1 / 2) (a := 3 / 4) (n := 4) (D := 1) (A := 3) (k := 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      half_rate_threshold_lt_three_quarters (by norm_num : (3 / 4 : ℝ) < 1)
      (by norm_num : 0 < 4) (by norm_num) (by norm_num : 2 ≤ 2)
      (by norm_num : (2 : ℝ) ≤ (1 / 2) * 4) (by norm_num : (3 / 4 : ℝ) * 4 ≤ 3)
      (by norm_num : 3 ≤ 4) rationalEvaluationDomain (fun _ ↦ 0)
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  change (classicalRationalClosePolynomialSet 3).Finite at hfinite
  change ((classicalRationalClosePolynomialSet 3).ncard : ℝ) ≤
    maxFirstOrderListCharge (agreementIncidenceRatio 4 1 3) 1
      (automaticJetDegree (1 / 2) (3 / 4))
      (automaticDerivativeCap (1 / 2) (3 / 4)) at hraw
  exact ⟨hfinite, hraw⟩

open Classical in
/-- The explicit first-order envelope bounds a concrete rational complete list. -/
example :
    let D := 2 - 1
    let θ := agreementIncidenceRatio 4 D 3
    let M := automaticDerivativeCap (1 / 2) (3 / 4)
    let μ := automaticJetDegree (1 / 2) (3 / 4)
    let T := stageStaircase μ M
    let Λ : ℝ := 2 * D * θ * T + (μ - M : ℕ)
    (classicalRationalClosePolynomialSet 3).Finite ∧
      ((classicalRationalClosePolynomialSet 3).ncard : ℝ) ≤ Λ := by
  exact automatic_first_order_list_bound (1 / 2) (3 / 4)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    half_rate_threshold_lt_three_quarters (by norm_num : (3 / 4 : ℝ) < 1)
    4 2 3 (by norm_num : 0 < 4) (by norm_num : 2 ≤ 2)
    (by norm_num : (2 : ℝ) ≤ (1 / 2) * 4)
    (by norm_num : (3 / 4 : ℝ) * 4 ≤ 3) (by norm_num : 3 ≤ 4)
    rationalEvaluationDomain (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) (fun _ ↦ 0)

open Classical in
/-- Positive slack gives a finite rational list with the first-order envelope bound. -/
example :
    let a := firstOrderRateThreshold (1 / 2 : ℝ) + (1 / 8 : ℝ)
    let D := 2 - 1
    let θ := agreementIncidenceRatio 4 D 4
    let M := automaticDerivativeCap (1 / 2) a
    let μ := automaticJetDegree (1 / 2) a
    let T := stageStaircase μ M
    let Λ : ℝ := 2 * D * θ * T + (μ - M : ℕ)
    (classicalRationalClosePolynomialSet 4).Finite ∧
      ((classicalRationalClosePolynomialSet 4).ncard : ℝ) ≤ Λ := by
  have haOne : firstOrderRateThreshold (1 / 2 : ℝ) + (1 / 8 : ℝ) < 1 := by
    linarith [half_rate_threshold_lt_three_quarters]
  have hA : (firstOrderRateThreshold (1 / 2 : ℝ) + (1 / 8 : ℝ)) * 4 ≤
      (4 : ℝ) := by
    linarith [half_rate_threshold_lt_three_quarters]
  exact automatic_first_order_list_bound_of_slack (1 / 2) (1 / 8)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 8) haOne 4 2 4
    (by norm_num : 0 < 4) (by norm_num : 2 ≤ 2)
    (by norm_num : (2 : ℝ) ≤ (1 / 2) * 4) hA (by norm_num : 4 ≤ 4)
    rationalEvaluationDomain (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) (fun _ ↦ 0)

open Classical in
/-- The squarefree automatic bound applies to a concrete rational complete list. -/
example :
    (classicalRationalClosePolynomialSet 4).Finite ∧
      ((classicalRationalClosePolynomialSet 4).ncard : ℝ) ≤
        FirstOrder.Squarefree.automaticSquarefreeListBoundConstant (1 / 2) * 4 /
          (1 / 8 : ℝ) ^ 2 := by
  have haOne : firstOrderRateThreshold (1 / 2 : ℝ) + (1 / 8 : ℝ) < 1 := by
    linarith [half_rate_threshold_lt_three_quarters]
  have hA : (firstOrderRateThreshold (1 / 2 : ℝ) + (1 / 8 : ℝ)) * 4 ≤
      (4 : ℝ) := by
    linarith [half_rate_threshold_lt_three_quarters]
  exact automatic_first_order_squarefree_list_bound_of_slack (1 / 2) (1 / 8)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 8) haOne 4 2 4
    (by norm_num : 0 < 4) (by norm_num : 2 ≤ 2)
    (by norm_num : (2 : ℝ) ≤ (1 / 2) * 4) hA (by norm_num : 4 ≤ 4)
    rationalEvaluationDomain (fun _ ↦ 0)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

private def smallFirstOrderProfile :
    ReedSolomon.HiddenDerivative.CurveProfile.LineProfile :=
  { n := 2
    k := 2
    agreement := 2
    multiplicity := 2
    firstDerivativeCap := 0
    totalJetCap := 1
    batchingDegree := 1
    supportDimension := 7
    localRank := 3
    columnY₀Weight := 3
    height := 1
    heightSlots := 11 }

private def finiteEvaluationDomain : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ (i.val : ℚ), by
    intro i j h
    change (i.val : ℚ) = (j.val : ℚ) at h
    exact Fin.ext (by exact_mod_cast h)⟩

private noncomputable def classicalRationalTwoPointClosePolynomialSet : Set ℚ[X] :=
  @closePolynomialSet ℚ (inferInstance : Field ℚ)
    (fun x y ↦ Classical.propDecidable (x = y)) 2 finiteEvaluationDomain (fun _ ↦ 0) 2 2

private theorem finiteLengthPositiveCapCertificate :
    Nonempty (FirstOrderSymbolicCertificate (F := ℚ) 1 2 1 1 1 2 1
      finiteEvaluationDomain (fun _ ↦ 0) (fun _ ↦ 0)
      (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1))) := by
  have hheight : firstOrderCurveShiftedRowSlotBound 1 2 1 1 1 2 1 1 <
      firstOrderCurveShiftedHeightSlotCount 1 2 1 1 1 1 1 := by decide
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (F := ℚ) (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1) (k := 2) (h := 1)
    (by norm_num) (by norm_num) (by norm_num) finiteEvaluationDomain (fun _ ↦ 0)
    (fun _ ↦ 0) hheight

open Classical in
/-- A positive-cap certificate bounds a concrete two-point rational close list. -/
example :
    classicalRationalTwoPointClosePolynomialSet.Finite ∧
      (0 : ℚ[X]) ∈ classicalRationalTwoPointClosePolynomialSet ∧
      ((classicalRationalTwoPointClosePolynomialSet.ncard : ℝ)) ≤
        7 * (1 : ℝ) ^ 3 * 2 / finiteLengthSlack (1 / 4) 2 ^ 2 := by
  obtain ⟨cert⟩ := finiteLengthPositiveCapCertificate
  have hbound := closePolynomialSet_finite_and_card_le_finiteLength_of_certificate
    (C := 1) (eta := 1 / 4) (k := 2) (A := 2) (n := 2)
    finiteEvaluationDomain (fun _ ↦ 0)
    (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 1) (μ := 1)) cert
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0)) (by norm_num) (by norm_num)
    (by norm_num [finiteLengthSlack]) (by norm_num) (by norm_num [finiteLengthSlack])
  have hzero :
      (0 : ℚ[X]) ∈ classicalRationalTwoPointClosePolynomialSet := by
    unfold classicalRationalTwoPointClosePolynomialSet closePolynomialSet
    simp only [Set.mem_ofPred_eq]
    exact ⟨WithBot.bot_lt_coe 2,
      by norm_num [polynomialAgreementSet, finiteEvaluationDomain]⟩
  exact ⟨hbound.1, hzero, hbound.2⟩

/-- A verified profile bounds a concrete nonempty family of agreeing polynomials. -/
example :
    (({0} : Finset ℚ[X]).card : ℚ) ≤ tightListEnvelope smallFirstOrderProfile := by
  apply finiteListBound_of_profile (p := smallFirstOrderProfile) (by decide) rfl
    (by decide) (by decide) finiteEvaluationDomain (fun _ ↦ 0)
    (Or.inl ringChar.eq_zero)
  intro P hP
  have hPzero : P = 0 := by simpa using hP
  subst P
  constructor
  · simp
  · simp [smallFirstOrderProfile, finiteEvaluationDomain]

/-- The squarefree profile envelope also bounds the same concrete polynomial family. -/
example :
    (({0} : Finset ℚ[X]).card : ℝ) ≤ squarefreeListEnvelope smallFirstOrderProfile := by
  apply finiteSquarefreeListBound_of_profile (p := smallFirstOrderProfile) (by decide) rfl
    (by decide) (by decide) (by decide) finiteEvaluationDomain (fun _ ↦ 0)
    (Or.inl ringChar.eq_zero) {0}
  intro P hP
  have hPzero : P = 0 := by simpa using hP
  subst P
  constructor
  · simp
  · simp [smallFirstOrderProfile, finiteEvaluationDomain]

/-- Incidence gives a nonempty finite-length list bound for dimension one over `ℚ`. -/
example :
    classicalRationalLowDimensionClosePolynomialSet.Finite ∧
      (0 : ℚ[X]) ∈ classicalRationalLowDimensionClosePolynomialSet ∧
      ((classicalRationalLowDimensionClosePolynomialSet.ncard : ℝ)) ≤
        7 * (1 : ℝ) ^ 3 * 4 / finiteLengthSlack (1 / 4) 4 ^ 2 := by
  have hbound := closePolynomialSet_finite_and_card_le_finiteLength_of_dimension_le_one
    (C := 1) (eta := 1 / 4) (k := 1) (A := 1)
    rationalEvaluationDomain (fun _ ↦ 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [finiteLengthSlack])
  have hzero : (0 : ℚ[X]) ∈ classicalRationalLowDimensionClosePolynomialSet := by
    unfold classicalRationalLowDimensionClosePolynomialSet closePolynomialSet
    simp only [Set.mem_ofPred_eq]
    exact ⟨WithBot.bot_lt_coe 1,
      by norm_num [polynomialAgreementSet, rationalEvaluationDomain]⟩
  exact ⟨hbound.1, hzero, hbound.2⟩

/-- Concrete finite-length selectors have a positive margin, count gap, and common bounds. -/
example :
    0 < finiteLengthDensityMargin (1 / 2) (1 / 8) 4 ∧
      3 * (finiteLengthMultiplicity (1 / 2) (1 / 8) 4 : ℝ) ^ 3 *
          finiteLengthDensityMargin (1 / 2) (1 / 8) 4 / 4 ≤
        finiteLengthSourceCount (1 / 2) (1 / 8) 4 -
          finiteLengthRankCount (1 / 2) (1 / 8) 4 ∧
      ((finiteLengthMultiplicity (1 / 2) (1 / 8) 4 : ℝ) ≤
          finiteLengthParameterBoundConstant (1 / 2) /
            finiteLengthSlack (1 / 8) 4 ∧
        (finiteLengthDerivativeCap (1 / 2) (1 / 8) 4 : ℝ) ≤
          finiteLengthParameterBoundConstant (1 / 2) /
            finiteLengthSlack (1 / 8) 4 ∧
        (finiteLengthJetDegree (1 / 2) (1 / 8) 4 : ℝ) ≤
          finiteLengthParameterBoundConstant (1 / 2) /
            finiteLengthSlack (1 / 8) 4) ∧
      (finiteLengthChallengeHeight (1 / 2) (1 / 8) 4 : ℝ) ≤
        finiteLengthParameterBoundConstant (1 / 2) /
          finiteLengthSlack (1 / 8) 4 ^ 2 := by
  have hthreshold : firstOrderRateThreshold (1 / 2 : ℝ) < 3 / 4 :=
    half_rate_threshold_lt_three_quarters
  have hrateThreshold : (1 / 2 : ℝ) < firstOrderRateThreshold (1 / 2) :=
    rate_lt_firstOrderRateThreshold (R := 1 / 2) (by norm_num) (by norm_num)
  have haOne : firstOrderRateThreshold (1 / 2 : ℝ) + 1 / 8 < 1 := by
    linarith
  have hbetaHalf : finiteLengthDerivativeRatio (1 / 2) (1 / 8) ≤ 1 / 2 := by
    have hagreement : (1 / 2 : ℝ) <
        automaticAgreement (1 / 2) (firstOrderRateThreshold (1 / 2) + 1 / 8) := by
      rw [automaticAgreement_eq_min]
      apply lt_min
      · linarith [hrateThreshold]
      · linarith [hrateThreshold]
    unfold finiteLengthDerivativeRatio automaticDerivativeRatio firstOrderRateBeta
    norm_num
    linarith
  have hmargin := finiteLengthDensityMargin_pos (rho := 1 / 2) (eta := 1 / 8) (n := 4)
    (by norm_num) (by norm_num) (by norm_num) haOne (by norm_num) hbetaHalf
  have hgap := finiteLength_count_gap (rho := 1 / 2) (eta := 1 / 8) (n := 4)
    (by norm_num) (by norm_num) (by norm_num) haOne (by norm_num) hbetaHalf
  have hparameters := finiteLength_multiplicity_derivativeCap_jetDegree_bounds
    (rho := 1 / 2) (eta := 1 / 8) (n := 4)
    (by norm_num) (by norm_num) (by norm_num) haOne (by norm_num) hbetaHalf
  have hheight := finiteLengthChallengeHeight_le_common_inv_slack_sq
    (rho := 1 / 2) (eta := 1 / 8) (n := 4)
    (by norm_num) (by norm_num) (by norm_num) haOne (by norm_num) hbetaHalf
  exact ⟨hmargin, hgap, hparameters, hheight⟩

/-- The line-MCA envelope has a concrete inverse-`eta` bound. -/
example :
    finiteLengthMcaEnvelope 1 4 1 1 1 1 ≤
      140 * (1 : ℝ) ^ 6 * 4 ^ 2 / (1 / 4 : ℝ) ^ 4 := by
  apply finiteLengthMcaEnvelope_le_inv_eta (C := 1) (eta := 1 / 4) (lambda := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [finiteLengthSlack]
  · norm_num
  · norm_num
  · norm_num
  · norm_num [finiteLengthSlack]
  · norm_num [finiteLengthSlack]
  · norm_num [finiteLengthSlack]

/-- The squarefree list envelope applies with positive slack and finite length. -/
example :
    (firstOrderCurveFiberStageOne (1 + 1) 1 1 (regularTaylorExponent 1) : ℝ) * 1 +
        ordinaryDegreeEnvelope 1 1 ≤
      7 * (1 : ℝ) ^ 3 * (4 : ℝ) / finiteLengthSlack (1 / 4 : ℝ) 4 ^ 2 := by
  apply squarefreeListExpression_le_finiteLength (C := 1) (eta := 1 / 4)
    (n := 4) (D := 1) (B := 1) (M := 1) (lambda := 1)
  all_goals norm_num [finiteLengthSlack]

/-- The line-MCA expression has the fourth-power finite-length envelope. -/
example :
    finiteLengthMcaEnvelope 1 4 1 1 1 1 ≤
      140 * (1 : ℝ) ^ 6 * 4 ^ 2 / finiteLengthSlack (1 / 4 : ℝ) 4 ^ 4 := by
  apply finiteLengthMcaEnvelope_le (C := 1) (eta := 1 / 4) (lambda := 1)
  all_goals norm_num [finiteLengthSlack]

/-- The inverse-slack line envelope gives a concrete rate-envelope instance. -/
example :
    finiteLengthMcaEnvelope 1 4 1 1 1 1 ≤ 140 * (1 : ℝ) ^ 6 * 4 ^ 2 * 1 ^ 4 := by
  apply finiteLengthMcaEnvelope_le_rateEnvelope (C := 1) (q := 1) (lambda := 1)
  all_goals norm_num
