/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintKernel
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Identity
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

open Polynomial in
example : normalizedBackwardTaylorError (2 : ℤ) (Polynomial.X ^ 2 : ℤ[X]) 1 = -Polynomial.X := by
  have hP : (Polynomial.X ^ 2 : ℤ[X]).eval 2 = 4 := by norm_num
  have hidentity := localPolynomialEvaluation_comp_unscaled_backwardError
    (d := 1) 2 4 (Polynomial.X ^ 2) hP
  have hcanonical := (localPolynomialEvaluation_comp_unscaled_eq_iff
    (d := 1) 2 4 (Polynomial.X ^ 2) _).mp hidentity
  have hC2 : (Polynomial.C (2 : ℤ) : ℤ[X]) = 2 := by norm_num
  have hC4 : (Polynomial.C (4 : ℤ) : ℤ[X]) = 4 := by norm_num
  have htaylor : taylor (2 : ℤ) (Polynomial.X ^ 2 : ℤ[X]) =
      Polynomial.X ^ 2 + Polynomial.C 4 * Polynomial.X + Polynomial.C 4 := by
    rw [taylor_X_pow, hC2, hC4]
    ring
  have hderiv : (Polynomial.X ^ 2 : ℤ[X]).derivative = Polynomial.C 2 * Polynomial.X := by
    rw [Polynomial.derivative_X_pow]
    norm_num
  have hmove : movingHasseSum (2 : ℤ) (Polynomial.X ^ 2 : ℤ[X]) 1 =
      Polynomial.X * (Polynomial.C 2 * Polynomial.X + Polynomial.C 4) := by
    rw [movingHasseSum_one, hderiv, taylor_mul, taylor_C, taylor_X]
    simp only [hC2, hC4]
    ring
  have hcandidate : taylor (2 : ℤ) (Polynomial.X ^ 2 : ℤ[X]) =
    Polynomial.C 4 + movingHasseSum (2 : ℤ) (Polynomial.X ^ 2 : ℤ[X]) 1 +
        Polynomial.X * (-Polynomial.X) := by
    rw [htaylor, hmove]
    simp only [hC2, hC4]
    ring
  have hmul : Polynomial.X * normalizedBackwardTaylorError (2 : ℤ)
      (Polynomial.X ^ 2 : ℤ[X]) 1 = Polynomial.X * (-Polynomial.X) := by
    calc
      Polynomial.X * normalizedBackwardTaylorError (2 : ℤ) (Polynomial.X ^ 2 : ℤ[X]) 1 =
          taylor (2 : ℤ) (Polynomial.X ^ 2 : ℤ[X]) - Polynomial.C 4 -
            movingHasseSum (2 : ℤ) (Polynomial.X ^ 2 : ℤ[X]) 1 := by rw [hcanonical]; ring
      _ = Polynomial.X * (-Polynomial.X) := by rw [hcandidate]; ring
  exact Polynomial.isRegular_X.left hmul
