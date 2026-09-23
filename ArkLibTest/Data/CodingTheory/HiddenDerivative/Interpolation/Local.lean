/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintKernel
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.IntermediateSpace
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RemainderMap

/-!
# Local interpolation acceptance cases

A concrete kernel element, grading instance, intermediate-space dimension, and normalized
constraint identity.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

example : exhibitedKernelMultiplier 2 1 1 (1 : LocalPolynomial ℚ 2) ∈
    LinearMap.ker (enlargedLocalConstraintMap (d := 2) 3) :=
  exhibitedKernelMultiplier_mem_ker (by norm_num) 1

example : (unscaledLocalSubstitution (R := ℤ) 1 0 0 (X (some 0))).IsWeightedHomogeneous
    (localJetDegreeWeight 1) 1 := by
  simpa using unscaledLocalSubstitution_isWeightedHomogeneous (R := ℤ) (d := 1) 0
    (isWeightedHomogeneous_X ℤ jetDegreeWeight (some 0))

example : Module.finrank ℚ (localIntermediateSpace ℚ 1 2 1 0) = 6 := by
  rw [finrank_localIntermediateSpace (by norm_num)]
  decide

example :
    (normalizedLocalConstraintAt (R := ℤ) (d := 1) 1 0 2 (X (some 0) - C 2) = 0 ↔
      SatisfiesLocalConstraints (R := ℤ) (d := 1) 1 0 2 (X (some 0) - C 2)) ∧
    LinearMap.ker (normalizedLocalConstraintAt (R := ℤ) (d := 1) 1 0 2) =
      LinearMap.ker (localConstraintCoordinatesAt (R := ℤ) (d := 1) 1 0 2) :=
  ⟨normalizedLocalConstraintAt_eq_zero_iff 1 0 2 _,
    normalizedLocalConstraintAt_ker_eq_coordinates 1 0 2⟩
