/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.SharpGeneralEquation
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.TaylorCutoff
import Mathlib.Algebra.Field.ZMod
/-!
# Tight polynomial-curve degree formula tests

These examples ensure the sharp regular-stage formulas use the supplied common Taylor exponent,
including the `K = 2` boundary.
-/

namespace ReedSolomon

/-- At `K = 2`, the tight exponent gives challenge degree `ell + h`. -/
example : sourceCurveCutChallengeDegree 3 2 5 (τ := 2 * 2 - 3) = 8 := by
  norm_num [sourceCurveCutChallengeDegree]

/-- At `K = 2`, the same exponent gives jet degree `v`. -/
example : sourceCurveCutJetDegree 2 4 (τ := 2 * 2 - 3) = 4 := by
  norm_num [sourceCurveCutJetDegree]

/-- The tight order-zero mixed degree uses `h*b + v*a`. -/
example : sourceCurveInitialMixedDegreeOne 3 2 4 5 (τ := 1) = 52 := by
  norm_num [sourceCurveInitialMixedDegreeOne, sourceCurveCutChallengeDegree,
    sourceCurveCutJetDegree]

/-- The tight order-one mixed degree uses `h*b^2 + 2*v*a*b`. -/
example : sourceCurveInitialMixedDegreeTwo 3 2 4 5 (τ := 1) = 336 := by
  norm_num [sourceCurveInitialMixedDegreeTwo, sourceCurveCutChallengeDegree,
    sourceCurveCutJetDegree]

/-- The arbitrary-order formula specializes to the order-one formula. -/
example : sourceCurveInitialMixedDegree 1 3 2 4 5 (τ := 1) =
    sourceCurveInitialMixedDegreeTwo 3 2 4 5 (τ := 1) := by
  norm_num [sourceCurveInitialMixedDegree, sourceCurveInitialMixedDegreeTwo,
    sourceCurveCutChallengeDegree, sourceCurveCutJetDegree]

/-- The strengthened order-one budget accepts an independent direct joint factor. -/
example : regularSymbolicCurveMCASharpBoundTwo 11 3 2 3 5 8 4 5
    (τ := 1) (η := 3 / 2) = 1746 := by
  norm_num [regularSymbolicCurveMCASharpBoundTwo, sourceCurveInitialMixedDegreeTwo,
    sourceCurveCutChallengeDegree, sourceCurveCutJetDegree]

/-- The arbitrary-order product gives the same order-one budget at the direct joint factor. -/
example : regularSymbolicCurveMCASharpBound 1 11 3 2 3 5 8 4 5 (τ := 1) =
    regularSymbolicCurveMCASharpBoundTwo 11 3 2 3 5 8 4 5 (τ := 1) (η := 3 / 2) := by
  norm_num [regularSymbolicCurveMCASharpBound, regularSymbolicCurveMCASharpBoundTwo,
    sourceCurveInitialMixedDegree, sourceCurveInitialMixedDegreeTwo,
    sourceCurveCutChallengeDegree, sourceCurveCutJetDegree,
    AffineHilbert.dimensionSensitiveIncidenceProduct]

/-- Characteristic equal to the Taylor cutoff is allowed: only pivots strictly below it
are needed, and the total jet cap is checked separately. -/
example : (ringChar (ZMod 5) = 0 ∨ 3 < ringChar (ZMod 5)) ∧
    (ringChar (ZMod 5) = 0 ∨ 5 ≤ ringChar (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact geometric_characteristic_components (K := 5) (ν := 3) (by norm_num)
    (by right; norm_num [ZMod.ringChar_zmod_n])

/-- The zero-characteristic branch places no finite upper bound on either parameter. -/
example (K ν : ℕ) (hK : 0 < K) :
    (ringChar ℚ = 0 ∨ ν < ringChar ℚ) ∧ (ringChar ℚ = 0 ∨ K ≤ ringChar ℚ) := by
  exact geometric_characteristic_components hK (Or.inl (by simp))

end ReedSolomon
