/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintKernel
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.IntermediateSpace
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RemainderMap
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ZeroOrder

/-!
# Local interpolation acceptance cases

A concrete kernel element, grading instance, intermediate-space dimension, and normalized
constraint identity.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- After changing coefficients, the constant constraint of `X + Y₀` at `(2, 3)` is `5`. -/
example :
    (MvPolynomial.map (Int.castRingHom ℚ)
      (localConstraintAt 1 (2 : ℤ) (3 : ℤ)
        ((X (none : JetVariable 1) : DifferentialPolynomial ℤ 1) +
          (X (some (0 : Fin 2)) : DifferentialPolynomial ℤ 1)))).coeff 0 = 5 := by
  rw [map_localConstraintAt]
  simp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [coeff_projectLowContact]
  have hcontact : localContactOrder 1 (0 : LocalVariable 1 →₀ ℕ) < 1 := by
    simp [localContactOrder]
  rw [ite_eq_left hcontact]
  simp only [eq_intCast, Int.cast_ofNat, Nat.reduceAdd, Fin.isValue, map_add, map_X,
    unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_zero,
    AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, coeff_C, coeff_zero_X,
    add_zero]
  have hprod :
      ((X (localT 1) * X (localE 1) : LocalPolynomial ℚ 1).coeff 0) = 0 := by
    rw [← constantCoeff_eq]
    simp
  have hcorrection : (localCorrection (R := ℚ) 1).coeff 0 = 0 := by
    rw [← constantCoeff_eq]
    simp [localCorrection]
  rw [hcorrection, hprod]
  norm_num

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

example : Module.finrank ℚ (localConstraintAt (d := 0) 2 (0 : ℚ) 0).range ≤ 3 := by
  exact (finrank_range_localConstraintAt_zeroOrder_le 2 (0 : ℚ) 0).trans (by decide)

example :
    (normalizedLocalConstraintAt (R := ℤ) (d := 1) 1 0 2 (X (some 0) - C 2) = 0 ↔
      SatisfiesLocalConstraints (R := ℤ) (d := 1) 1 0 2 (X (some 0) - C 2)) ∧
    LinearMap.ker (normalizedLocalConstraintAt (R := ℤ) (d := 1) 1 0 2) =
      LinearMap.ker (localConstraintCoordinatesAt (R := ℤ) (d := 1) 1 0 2) :=
  ⟨normalizedLocalConstraintAt_eq_zero_iff 1 0 2 _,
    normalizedLocalConstraintAt_ker_eq_coordinates 1 0 2⟩
