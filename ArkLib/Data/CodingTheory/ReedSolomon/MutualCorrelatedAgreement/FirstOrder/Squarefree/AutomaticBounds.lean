/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.AutomaticBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.NumericalBounds

/-!
# Inverse-square list bound for the automatic first-order recipe

This file combines the existing inverse-slack bounds on the two degree caps with the squarefree
product/resultant list expression.  It records the positive-derivative branch; the zero-derivative
branch is handled by the ordinary theorem in the public semantic facade.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open ReedSolomon.HiddenDerivative

noncomputable section

/-- A rate-only coefficient for the squarefree inverse-square list envelope. -/
def automaticSquarefreeListBoundConstant (rho : ℝ) : ℝ :=
  7 * automaticHybridEnvelopeConstant rho ^ 3

/-- On the positive-derivative branch, the automatic squarefree list expression is
`O_rho(n / eta^2)`. -/
theorem automaticSquarefreeListExpression_le
    {rho eta : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (hn : 1 ≤ n) (hD : 1 ≤ D) (hDn : D ≤ n) (hDA : D < A)
    (hDrate : (D : ℝ) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A)
    (hM : 1 ≤ automaticDerivativeCap rho (automaticFirstOrderThreshold rho + eta)) :
    let B := automaticJetDegree rho (automaticFirstOrderThreshold rho + eta)
    let M := automaticDerivativeCap rho (automaticFirstOrderThreshold rho + eta)
    let lambda := hybridTheta n D A
    (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) * lambda +
        ordinaryDegreeEnvelope B M ≤
      automaticSquarefreeListBoundConstant rho * n / eta ^ 2 := by
  dsimp only
  let C := automaticHybridEnvelopeConstant rho
  let q := 1 / eta
  let B := automaticJetDegree rho (automaticFirstOrderThreshold rho + eta)
  let M := automaticDerivativeCap rho (automaticFirstOrderThreshold rho + eta)
  let lambda := hybridTheta n D A
  have hC : 1 ≤ C := one_le_automaticHybridEnvelopeConstant rho
  have hetaOne : eta ≤ 1 := by
    have hgap := automatic_eta_lt_rateGap hrho hrhoOne heta haOne
    have hthresholdPos := (rho_lt_automaticFirstOrderThreshold hrho hrhoOne).trans' hrho
    unfold automaticRateGap at hgap
    linarith
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact (one_le_div heta).2 hetaOne
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold hybridTheta
    positivity
  have hthresholdGap : 0 < automaticFirstOrderThreshold rho - rho :=
    sub_pos.mpr (rho_lt_automaticFirstOrderThreshold hrho hrhoOne)
  have hlambdaRate := hybridTheta_le_rate_gap hDn hDA hDrate hA
    (show rho < automaticFirstOrderThreshold rho + eta by
      exact (rho_lt_automaticFirstOrderThreshold hrho hrhoOne).trans (by linarith))
  have hlambda : lambda ≤ C := by
    calc
      lambda ≤ 1 / (automaticFirstOrderThreshold rho + eta - rho) := hlambdaRate
      _ ≤ 1 / (automaticFirstOrderThreshold rho - rho) := by
        exact div_le_div_of_nonneg_left zero_le_one hthresholdGap (by linarith)
      _ ≤ C := rateGapInv_le_automaticHybridEnvelopeConstant rho
  have hB : (B : ℝ) ≤ C * q := by
    calc
      (B : ℝ) ≤ automaticJetBoundConstant rho / eta :=
        automaticJetDegree_le_inv_eta hrho hrhoOne heta haOne
      _ = automaticJetBoundConstant rho * q := by dsimp only [q]; ring
      _ ≤ C * q := by
        gcongr
        exact automaticJetBoundConstant_le_envelope rho
  have hMB : M ≤ B := by
    dsimp only [M, B]
    unfold automaticDerivativeCap
    exact min_le_right _ _
  have hbound := squarefreeListExpression_le_rate_envelope hC hq hn hD hDn
    (by simpa only [M] using hM) hMB hlambda0 hlambda hB
  dsimp only [C, q, B, M, lambda] at hbound ⊢
  unfold automaticSquarefreeListBoundConstant
  field_simp [ne_of_gt heta] at hbound ⊢
  nlinarith

end

end ReedSolomon.FirstOrder.Squarefree
