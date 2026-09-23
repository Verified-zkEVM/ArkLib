/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveRank
import Mathlib.Algebra.Field.ZMod

/-!
# First-order curve-rank acceptance tests

These examples instantiate the translated-kernel characterization and the numerical rank-profile
bound over a small finite field.
-/

open PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative
open scoped BigOperators Matrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A nonzero constant coefficient vector is characterized by the one-point translated kernel. -/
example :
    (firstOrderCurveGradedConstraintMatrix 1 1 1 0 0 1
      (fun _ ↦ (0 : ZMod 5)) (fun _ ↦ (0 : (ZMod 5)[X])) *ᵥ
        (fun _ ↦ (1 : (ZMod 5)[X]))) = 0 ↔
      ∀ _i : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ZMod 5)) 0
        (SourceColumn.interpolant
          (firstOrderColumns (D := 1) (A := 1) (m := 1) (M := 0) (μ := 0))
          (fun _ ↦ (1 : (ZMod 5)[X]))) := by
  exact firstOrderCurveGradedConstraintMatrix_kernel_iff 1 1 1 0 0 1
    (by decide) (fun _ ↦ (0 : ZMod 5)) (fun _ ↦ (0 : (ZMod 5)[X]))
    (fun _ ↦ (1 : (ZMod 5)[X]))

/-- The nonempty origin profile at this parameter choice is bounded by its numerical profile. -/
example : firstOrderOriginGradedRank (F := ZMod 5) 1 1 1 0 0 ≤ 1 := by
  simpa [firstOrderGradedRankBound, firstOrderGradedSourceCount] using
    firstOrderOriginGradedRank_le_bound (F := ZMod 5) 1 1 1 0 0
