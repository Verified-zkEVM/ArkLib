/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.HybridConstants
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Bounds

/-!
# Closed numerical envelopes for squarefree first-order counting

The semantic count retains the exact cap-sensitive Taylor degree.  These lemmas provide the
coarser product envelopes used only by rate-level corollaries.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open ReedSolomon.HiddenDerivative

/-- The regular fixed-word image costs at most `4 D B M`. -/
theorem firstOrderCurveFiberStageOne_le_four_mul
    {D B M : ℕ} (hD : 1 ≤ D) (hM : 1 ≤ M) (hMB : M ≤ B) :
    firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) ≤ 4 * D * B * M := by
  have hsharp := firstOrderCurveFiberStageOne_le_hybridEnvelope hD hM hMB
  calc
    firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) ≤
        2 * D * M * (2 * B - M) := by
      simpa only [hybridTau] using hsharp
    _ ≤ 4 * D * B * M := by
      have : 2 * B - M ≤ 2 * B := Nat.sub_le _ _
      calc
        2 * D * M * (2 * B - M) ≤ 2 * D * M * (2 * B) :=
          Nat.mul_le_mul_left _ this
        _ = 4 * D * B * M := by ring

/-- The source-cap squarefree list expression has the simple paper-level envelope
`4 λ D B M + 2 B M + B`. -/
theorem squarefreeListExpression_le
    {D B M : ℕ} {lambda : ℝ}
    (hD : 1 ≤ D) (hM : 1 ≤ M) (hMB : M ≤ B) (hlambda : 0 ≤ lambda) :
    (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) * lambda +
        ordinaryDegreeEnvelope B M ≤
      4 * D * B * M * lambda + 2 * B * M + B := by
  have hstage : (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) ≤
      4 * D * B * M := by
    exact_mod_cast firstOrderCurveFiberStageOne_le_four_mul hD hM hMB
  have htail : (ordinaryDegreeEnvelope B M : ℝ) ≤ B + 2 * B * M := by
    exact_mod_cast ordinaryDegreeEnvelope_le B M
  nlinarith [mul_le_mul_of_nonneg_right hstage hlambda]

/-- A common bound for the incidence ratio and both degree caps yields the inverse-square
slack envelope used by the public rate theorem. -/
theorem squarefreeListExpression_le_rate_envelope
    {C q lambda : ℝ} {n D B M : ℕ}
    (hC : 1 ≤ C) (hq : 1 ≤ q) (hn : 1 ≤ n) (hD : 1 ≤ D) (hDn : D ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C * q) :
    (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) * lambda +
        ordinaryDegreeEnvelope B M ≤
      7 * C ^ 3 * n * q ^ 2 := by
  have hraw := squarefreeListExpression_le hD hM hMB hlambda0
  have hD' : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have hM' : (M : ℝ) ≤ C * q := (Nat.cast_le.mpr hMB).trans hB
  have hrough :
      4 * (D : ℝ) * B * M * lambda + 2 * (B : ℝ) * M + B ≤
        4 * (n : ℝ) * (C * q) * (C * q) * C +
          2 * (C * q) * (C * q) + C * q := by
    gcongr
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hx : 1 ≤ C * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hq)]
  have hCN : 1 ≤ C * (n : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hN)]
  have htwo : (C * q) * (C * q) ≤ C ^ 3 * n * q ^ 2 := by
    have hnonneg : 0 ≤ (C * q) ^ 2 := sq_nonneg _
    have hmul : (C * q) ^ 2 ≤ (C * q) ^ 2 * (C * n) := by
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hCN)]
    nlinarith [hmul]
  have hone : C * q ≤ C ^ 3 * n * q ^ 2 := by
    have hsquare : C * q ≤ (C * q) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hC0 hq0) (sub_nonneg.mpr hx)]
    exact hsquare.trans (by simpa only [pow_two] using htwo)
  calc
    (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) * lambda +
          ordinaryDegreeEnvelope B M ≤
        4 * (D : ℝ) * B * M * lambda + 2 * (B : ℝ) * M + B := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hraw
    _ ≤ 4 * (n : ℝ) * (C * q) * (C * q) * C +
          2 * (C * q) * (C * q) + C * q := hrough
    _ = 4 * (C ^ 3 * n * q ^ 2) + 2 * ((C * q) * (C * q)) + C * q := by ring
    _ ≤ 4 * (C ^ 3 * n * q ^ 2) + 2 * (C ^ 3 * n * q ^ 2) +
          C ^ 3 * n * q ^ 2 := by gcongr
    _ = 7 * C ^ 3 * n * q ^ 2 := by ring

end ReedSolomon.FirstOrder.Squarefree
