/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail

/-! # Acceptance cases for squarefree list bounds -/

open ReedSolomon.HiddenDerivative

namespace ReedSolomon.FirstOrder.Squarefree

/-- The squarefree list expression has the product bound at `D = 1`, `B = 4`, `M = 2`. -/
example :
    (firstOrderCurveFiberStageOne 2 4 2 (regularTaylorExponent 1) : ℝ) * (1 : ℝ) +
        ordinaryDegreeEnvelope 4 2 ≤ 52 := by
  have h := squarefreeListExpression_le (D := 1) (B := 4) (M := 2) (lambda := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  simpa using h

/-- The rate envelope gives `448` at `C = 1`, `q = n = B = 4`, `D = 1`, `M = 2`. -/
example :
    (firstOrderCurveFiberStageOne 2 4 2 (regularTaylorExponent 1) : ℝ) * (1 : ℝ) +
        ordinaryDegreeEnvelope 4 2 ≤ 7 * (1 : ℝ) ^ 3 * 4 * 4 ^ 2 := by
  have h := squarefreeListExpression_le_rate_envelope
    (C := 1) (q := 4) (lambda := 1) (n := 4) (D := 1) (B := 4) (M := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end ReedSolomon.FirstOrder.Squarefree
