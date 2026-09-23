/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap

/-!
# Local constraint map acceptance tests

`Y₀ - received` satisfies the multiplicity-one local constraints at every point, because its
substitution is `T (E + localJetSum d)`, of contact order at least one. `Y₀` itself fails them
when `received ≠ 0`, since its substitution has constant coefficient `received`. With
multiplicity zero there are no constraints. The factorization and coefficient statements are
checked over `ℤ`, which is not a field, and the global map over the infinite index type `ℕ`.
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

/-- `Y₀ - received` satisfies the multiplicity-one constraints at every point. -/
example (d : ℕ) (center received : ℚ) :
    SatisfiesLocalConstraints (d := d) 1 center received (X (some 0) - C received) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply, projectLowContact,
    weightedTruncation_eq_zero_iff]
  have h : (unscaledLocalSubstitution d center received).toLinearMap (X (some 0) - C received) =
      X (localT d) * (X (localE d) + localJetSum d) := by
    simp only [AlgHom.toLinearMap_apply, map_sub, unscaledLocalSubstitution_Y_zero, algHom_C,
      algebraMap_eq, mul_add, T_mul_localJetSum]
    ring
  rw [h]
  simpa using mul_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := ℚ) (localContactWeight d) (localT d) le_rfl)
    (by simp : X (localE d) + localJetSum d ∈
      restrictWeightedOrder (R := ℚ) (localContactWeight d) 0)

/-- `Y₀` fails the multiplicity-one constraints at a point with nonzero received value. -/
example (d : ℕ) (center : ℚ) :
    ¬SatisfiesLocalConstraints (d := d) 1 center 1 (X (some 0)) := by
  intro h
  have h0 := (satisfiesLocalConstraints_iff_coeff_eq_zero 1 center 1 _).mp h 0
    (by simp [localContactOrder])
  rw [unscaledLocalSubstitution_Y_zero, ← constantCoeff_eq] at h0
  simp [localCorrection] at h0

/-- Multiplicity zero imposes no constraints. -/
example (d : ℕ) (center received : ℚ) (Q : DifferentialPolynomial ℚ d) :
    SatisfiesLocalConstraints 0 center received Q :=
  (projectLowContact_eq_zero_iff 0 _).mpr fun _ he => absurd he (Nat.not_lt_zero _)

/-- Over `ℤ`, applied to one polynomial: the point-dependent map factors through the enlarged
map. -/
example (m : ℕ) (center received : ℤ) (Q : DifferentialPolynomial ℤ 2) :
    localConstraintAt m center received Q =
      enlargedLocalConstraintMap m (translatedLocalTruncation m center received Q) :=
  localConstraintAt_apply_eq_enlarged_translated m center received Q

/-- Over `ℤ`: truncating modulo `T^m` first does not change the enlarged map. -/
example (m : ℕ) (F : LocalPolynomial ℤ 2) :
    enlargedLocalConstraintMap m (truncateLocalT m F) = enlargedLocalConstraintMap m F := by
  simp

/-- `truncateLocalT 2` removes `T²` and keeps `T E`. -/
example :
    truncateLocalT (R := ℚ) (d := 1) 2 (X (localT 1) ^ 2 + X (localT 1) * X (localE 1)) =
      X (localT 1) * X (localE 1) := by
  ext e
  rw [coeff_truncateLocalT]
  split_ifs with h
  · have hT : (X (localT 1) ^ 2 : LocalPolynomial ℚ 1).coeff e = 0 := by
      rw [X_pow_eq_monomial, coeff_monomial, ite_eq_right_iff]
      rintro rfl
      simp at h
    simp [hT]
  · have hTE : (X (localT 1) * X (localE 1) : LocalPolynomial ℚ 1).coeff e = 0 := by
      rw [X, X, monomial_mul_monomial, coeff_monomial, ite_eq_right_iff]
      rintro rfl
      simp [localT, localE, localAux] at h
    exact hTE.symm

/-- The global map over the infinite index type `ℕ` evaluates one point at a time. -/
example {D A d M W m : ℕ} (hdD : d < D) (centers received : ℕ → ℚ)
    (v : ExactInterpolationCoefficients ℚ D A d m M W hdD) (i : ℕ) :
    globalExactCoefficientConstraintMap hdD centers received v i =
      exactCoefficientLocalConstraintAt hdD m (centers i) (received i) v := by
  simp
