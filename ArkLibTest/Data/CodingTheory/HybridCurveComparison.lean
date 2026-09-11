/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveComparison

/-! Import-level checks for the zero-derivative endpoint and max-then-min comparison. -/

namespace ReedSolomon

open HiddenDerivative

example :
    hybridCurveOptimized 16 (2 - 1) 1 10 7 22 0 ≤
      ((firstOrderCurveBound 16 4 2 6 10 22 0 1 7 (2 * 4 - 3)
        (firstOrderCurveDirectRatio 16 2 10) : ℚ) : ℝ) := by
  exact hybridCurveOptimized_le_firstOrderCurveBound
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example :
    hybridCurveOptimized 16 (2 - 1) 1 10 7 22 4 ≤
      curveRetentionMinimum (2 - 1) 10
        (hybridCurveFullDifferentiationEnvelope 16 2 4 1 10 7 22 4) := by
  exact hybridCurveOptimized_le_min_fullDifferentiationEnvelope
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end ReedSolomon
