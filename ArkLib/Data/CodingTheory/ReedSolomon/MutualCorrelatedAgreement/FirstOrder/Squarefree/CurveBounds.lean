/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Certificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.NumericalBounds

/-!
# Closed bounds for the retained squarefree curve transfer

The semantic theorem retains the exact split-dependent regular-stage expression.  This file
proves the balanced-split comparison used by the finite-length line corollary while leaving the
general polynomial-curve expression available to application tables.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open ReedSolomon.HiddenDerivative

/-- The displayed finite-length line-MCA envelope, with its ordinary tail written separately. -/
def retainedSquarefreeLineMCAEnvelope
    (lambda : ℝ) (n D B M H : ℕ) : ℝ :=
  retainedOrdinaryMCARaw lambda n D 1 B M H +
    (48 * D ^ 2 * H + 16 * D : ℕ) * lambda ^ 2 * B * M +
      (8 * D * (n - D - 1) : ℕ) * lambda * B * M

/-- At the balanced split, the exact line-curve charge is at most the displayed finite-length
envelope. -/
theorem retainedSquarefreeCurveMCARaw_balanced_line_le
    {n D A B M H : ℕ} (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B) :
    retainedSquarefreeCurveMCARaw (hybridTheta n D A)
        n D 1 (hybridBalancedL D A) A B M H ≤
      retainedSquarefreeLineMCAEnvelope (hybridTheta n D A) n D B M H := by
  let theta := hybridTheta n D A
  let L := hybridBalancedL D A
  have htheta : 0 ≤ theta := (hybridTheta_one_le hDA hAn).trans' zero_le_one
  have hret := hybridBalancedL_retention hDA hAn
  have hLbounds := hybridBalancedL_bounds hDA
  have hlambdaOne : hybridLambdaOne n A L ≤ 2 * theta := by
    simpa only [L, theta] using hret.1
  have hlambdaTwo : hybridLambdaTwo n D L ≤ 2 * theta := by
    simpa only [L, theta] using hret.2.1
  have htail : n - L ≤ n - D - 1 := by
    simpa only [L] using hret.2.2
  have hjointNat := firstOrderCurveJointStageOne_le_hybridEnvelope
    (D := D) (h := H) (j := B) (q := M) hD hM hMB
  have hfiberNat := firstOrderCurveFiberStageOne_le_four_mul hD hM hMB
  have hmoment : M * (2 * B - M) ≤ 2 * B * M := by
    calc
      M * (2 * B - M) ≤ M * (2 * B) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * B * M := by ring
  have hjoint :
      (firstOrderCurveJointStageOne (D + 1) 1 H B M (2 * D - 1) : ℝ) ≤
        (24 * D ^ 2 * H + 8 * D : ℕ) * B * M := by
    have hjointCast :
        (firstOrderCurveJointStageOne (D + 1) 1 H B M (2 * D - 1) : ℝ) ≤
          ((12 * D ^ 2 * H + 4 * D) * (M * (2 * B - M)) : ℕ) := by
      exact_mod_cast hjointNat
    calc
      (firstOrderCurveJointStageOne (D + 1) 1 H B M (2 * D - 1) : ℝ) ≤
          ((12 * D ^ 2 * H + 4 * D) * (M * (2 * B - M)) : ℕ) := hjointCast
      _ ≤ ((12 * D ^ 2 * H + 4 * D) * (2 * B * M) : ℕ) := by
        exact_mod_cast Nat.mul_le_mul_left (12 * D ^ 2 * H + 4 * D) hmoment
      _ = ((24 * D ^ 2 * H + 8 * D : ℕ) : ℝ) * B * M := by
        push_cast
        ring
  have hfiber :
      (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) ≤
        (4 * D * B * M : ℕ) := by
    exact_mod_cast hfiberNat
  have hregularEq :
      (regularSymbolicCurveMCADerivativeBoundTwo n 1 (D + 1) (D + 1)
          L A B M H (2 * D - 1) : ℝ) =
        hybridLambdaOne n A L * theta *
            firstOrderCurveJointStageOne (D + 1) 1 H B M (2 * D - 1) +
          (n - L : ℕ) * hybridLambdaTwo n D L *
            firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) := by
    simpa only [Nat.sub_zero, hybridTau, L, theta] using
      (regularSymbolicCurveMCADerivativeBoundTwo_eq_hybrid_stage
        (n := n) (D := D) (A := A) (L := L) (h := H) (mu := B) (e := M) (j := 0)
        hLbounds.1 hLbounds.2 hAn)
  have hlambdaOne0 : 0 ≤ hybridLambdaOne n A L := by
    unfold hybridLambdaOne
    positivity
  have hlambdaTwo0 : 0 ≤ hybridLambdaTwo n D L := by
    unfold hybridLambdaTwo
    positivity
  have hjoint0 :
      0 ≤ (firstOrderCurveJointStageOne (D + 1) 1 H B M (2 * D - 1) : ℝ) := by
    positivity
  have hfiber0 :
      0 ≤ (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) := by
    positivity
  have hregular :
      (regularSymbolicCurveMCADerivativeBoundTwo n 1 (D + 1) (D + 1)
          L A B M H (2 * D - 1) : ℝ) ≤
        (48 * D ^ 2 * H + 16 * D : ℕ) * theta ^ 2 * B * M +
          (8 * D * (n - D - 1) : ℕ) * theta * B * M := by
    rw [hregularEq]
    calc
      hybridLambdaOne n A L * theta *
            firstOrderCurveJointStageOne (D + 1) 1 H B M (2 * D - 1) +
          (n - L : ℕ) * hybridLambdaTwo n D L *
            firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) ≤
        (2 * theta) * theta * ((24 * D ^ 2 * H + 8 * D : ℕ) * B * M) +
          (n - D - 1 : ℕ) * (2 * theta) * (4 * D * B * M : ℕ) := by
            gcongr
      _ = (48 * D ^ 2 * H + 16 * D : ℕ) * theta ^ 2 * B * M +
          (8 * D * (n - D - 1) : ℕ) * theta * B * M := by
            push_cast
            ring
  unfold retainedSquarefreeCurveMCARaw retainedSquarefreeLineMCAEnvelope
  dsimp only [L, theta] at hregular
  linarith

end ReedSolomon.FirstOrder.Squarefree
