/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.UniformMca
import ArkLib.Data.Polynomial.Differential.Types
import Mathlib.Tactic.NormNum

/-! # Acceptance cases for singular tails and squarefree list bounds -/

open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative

namespace ReedSolomon.FirstOrder.Squarefree

/-- A double root of `X²` kills the specialized singular tail. -/
example : singularTail (1 : ℚ[X]) (X ^ 2 : ℚ[X][X]) 2 = 0 := by
  have h := singularTail_map_eq_zero_of_common_root (1 : ℚ[X]) (X ^ 2 : ℚ[X][X]) two_pos
    (by simp) (RingHom.id ℚ[X]) 0 (by simp) (by simp)
  simpa using h

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
