/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintKernel
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Contact
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.GradedRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Identity
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.IntermediateSpace
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.KernelSliceIndependence
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Rank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RankBudget
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RemainderMap
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Translation
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ZeroOrder

/-!
# Local interpolation acceptance cases

A concrete kernel element, grading instance, intermediate-space dimension, and normalized
constraint identity.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

private theorem satisfiesLocalConstraintsOneYZeroSub (d : ℕ) (center received : ℤ) :
    SatisfiesLocalConstraints (d := d) 1 center received (X (some 0) - C received) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply, projectLowContact,
    weightedTruncation_eq_zero_iff]
  have h : (unscaledLocalSubstitution d center received).toLinearMap
      (X (some 0) - C received) =
        X (localT d) * (X (localE d) + localJetSum d) := by
    simp only [AlgHom.toLinearMap_apply, map_sub, unscaledLocalSubstitution_Y_zero, algHom_C,
      algebraMap_eq, mul_add, T_mul_localJetSum]
    ring
  rw [h]
  simpa using mul_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := ℤ) (localContactWeight d) (localT d) le_rfl)
    (by simp : X (localE d) + localJetSum d ∈
      restrictWeightedOrder (R := ℤ) (localContactWeight d) 0)

/-- At a nonzero center, the order-one constraint gives the factor `X - 2` of `X² - 4`. -/
example : (Polynomial.X - Polynomial.C (2 : ℤ)) ∣
    (Polynomial.X ^ 2 - 4 : Polynomial ℤ) := by
  have hP : Polynomial.eval 2 (Polynomial.X ^ 2 : Polynomial ℤ) = 4 := by norm_num
  have h := X_sub_C_pow_dvd_differentialSpecialization_of_contact
    (d := 1) (Q := X (some 0) - C (4 : ℤ)) (P := Polynomial.X ^ 2) (m := 1)
    (center := 2) (received := 4) hP (satisfiesLocalConstraintsOneYZeroSub 1 2 4)
  simpa [differentialSpecialization, differentialSpecializationHom] using h

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

example : Module.finrank ℚ (LinearMap.range
    (exactLocalConstraintAt (A := 1) (M := 0) (W := 0) (by norm_num : 1 < 2)
      2 (0 : ℚ) 0)) ≤ 4 := by
  have h := finrank_range_exactLocalConstraintAt_le_localResidualCoordinateBudget
    (F := ℚ) (d := 1) (D := 2) (A := 1) (M := 0) (W := 0)
    (by norm_num) (by norm_num) 2 (0 : ℚ) 0
  have hfloor : exactInterpolationJetDegreeFloor 2 1 1 2 = 1 := by
    norm_num [exactInterpolationJetDegreeFloor]
  rw [hfloor] at h
  have hbudget : localResidualCoordinateBudget 1 2 0 2 = 4 := by decide
  simpa [hbudget] using h

example : Module.finrank ℚ (ExhibitedKernelFamilySource ℚ 1 2 1 0) = 1 := by
  rw [finrank_exhibitedKernelFamilySource (by norm_num)]
  decide

example : Module.finrank ℚ (LinearMap.range
    (exactLocalConstraintAt (A := 1) (M := 1) (W := 0) (by norm_num : 1 < 2)
      2 (0 : ℚ) 0)) ≤ 5 := by
  let S : Submodule ℚ (LocalPolynomial ℚ 1) := localIntermediateSpace ℚ 1 2 1 0
  have : Module.Finite ℚ (localIntermediateSpace ℚ 1 2 1 0) :=
    localIntermediateSpace_finite (by norm_num) 2 1 0
  have hS (Q : DifferentialPolynomial ℚ 1) (hQ :
      Q ∈ exactInterpolationSpace ℚ 2 1 1 2 1 0 (by norm_num)) :
      translatedLocalTruncation 2 (0 : ℚ) 0 Q ∈ S :=
    translatedLocalTruncation_mem_localIntermediateSpace (by norm_num) 0 0 hQ
  let g : ExhibitedKernelFamilySource ℚ 1 2 1 0 →ₗ[ℚ]
      LinearMap.ker ((enlargedLocalConstraintMap (R := ℚ) 2).domRestrict S) :=
    exhibitedKernelFamilyKernelMap (R := ℚ) (d := 1) (by norm_num) 2 1 0
  have hg : Function.Injective g := exhibitedKernelFamilyKernelMap_injective
    (R := ℚ) (d := 1) (by norm_num) 2 1 0
  have h := finrank_range_exactLocalConstraintAt_le_sub (A := 1) (D := 2) (d := 1)
    (M := 1) (W := 0) (by norm_num) 2 (0 : ℚ) 0 S hS g hg
  rw [finrank_localIntermediateSpace (F := ℚ) (d := 1) (by norm_num) 2 1 0,
    finrank_exhibitedKernelFamilySource (F := ℚ) (d := 1) (by norm_num) 2 1 0] at h
  norm_num at h
  exact h

example :
    (localDerivativeCoordinateBudget 2 1 1 : ℝ) ≤
      (1 : ℝ) ^ 2 / (Nat.factorial 2 : ℝ) ^ 2 *
        Real.exp ((2 : ℝ) / 1 * (1 + (3 : ℕ).choose 2)) *
          (1 / (3 * ((2 : ℝ) / 1) ^ 2) + 1 / ((2 : ℝ) / 1)) := by
  have h := localDerivativeCoordinateBudget_le_geometric 2 1 1 (by norm_num) one_pos
  rw [show localDerivativeCoordinateBudget 2 1 1 = 2 by decide] at h ⊢
  norm_num at h ⊢
  exact h

example : globalPointTranslation (d := 1) (2 : ℤ) 3
    (globalPointTranslation 4 5 (X none)) = X none + C 6 := by
  rw [← AlgHom.comp_apply, globalPointTranslation_comp, globalPointTranslation_X]
  ring_nf

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
