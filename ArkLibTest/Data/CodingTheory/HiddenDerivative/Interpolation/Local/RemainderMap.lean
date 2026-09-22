/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RemainderMap

/-!
# Normalized remainder map acceptance tests

At `d = 2` the exponent of `E` goes to the exponent of `T² E`, whose `T`-degree is the contact
order `2` of `E`. At `d = 1` the monomial `E`, of contact order one, is deleted by reduction
modulo `T` after normalization, as it is by the projection to contact order below one. The
low-contact projection is not reduction modulo `T^m` on the unscaled image: at `d = 1` and `m = 2`
the monomial `T E` has `T`-degree one but contact order two. Finally the kernel statements are
instantiated at a concrete agreement.

For the contact corollary `X_sub_C_pow_dvd_differentialSpecialization_of_normalizedLocalConstraint`:
the normalized remainder of `Y₀ - received` of order one vanishes, which recovers the factor
theorem for `P - P(center)`; and the agreement hypothesis `P(center) = received` is needed, since
for `P = 0`, `received = 1` the remainder still vanishes but `X ∤ -1`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At `d = 2`, normalization gives the exponent of `E` the `T`-degree `2`. -/
example : normalizeLocalExponent 2 (Finsupp.single (localE 2) 1) (localT 2) = 2 := by
  rw [normalizeLocalExponent_T_eq_contact, localContactOrder_eq]
  simp [localT, localE, localAux]

/-- At `d = 2`, normalization sends `5 E` to `5 T² E`. -/
example :
    normalizeError (R := ℤ) 2 (C 5 * X (localE 2)) = C 5 * (X (localT 2) ^ 2 * X (localE 2)) := by
  simp [map_ofNat]

/-- At `d = 1`, reduction modulo `T` deletes the normalized image `T E` of `E`, matching the
projection of `E` to contact order below one. -/
example : truncateLocalT (R := ℤ) (d := 1) 1 (normalizeError 1 (X (localE 1))) = 0 ∧
    projectLowContact (R := ℤ) (d := 1) 1 (X (localE 1)) = 0 := by
  have hproj : projectLowContact (R := ℤ) (d := 1) 1 (X (localE 1)) = 0 := by
    ext e
    rw [coeff_projectLowContact, coeff_X]
    split_ifs with hlt heq <;> try rfl
    subst heq
    simp [localContactOrder_eq, localT, localE, localAux] at hlt
  exact ⟨by rw [truncateLocalT_normalizeError, hproj, map_zero], hproj⟩

/-- Reduction modulo `T²` is not the contact projection: at `d = 1` it keeps `T E`, which has
contact order two. -/
example : truncateLocalT (R := ℤ) (d := 1) 2 (X (localT 1) * X (localE 1)) ≠
    projectLowContact 2 (X (localT 1) * X (localE 1)) := by
  intro h
  have hc := congrArg (fun p => p.coeff (Finsupp.single (localT 1) 1 + Finsupp.single (localE 1) 1))
    h
  simp only [coeff_truncateLocalT, coeff_projectLowContact, localContactOrder_eq] at hc
  rw [X, X, monomial_mul_monomial, coeff_monomial] at hc
  simp [localT, localE, localAux] at hc

/-- The normalized remainder of `Y₀ - 2` vanishes at the agreement `(center, received) = (0, 2)`
exactly when the contact-order constraints hold, and the kernels agree. -/
example (m : ℕ) :
    (normalizedLocalConstraintAt (R := ℤ) (d := 1) m 0 2 (X (some 0) - C 2) = 0 ↔
      SatisfiesLocalConstraints (R := ℤ) (d := 1) m 0 2 (X (some 0) - C 2)) ∧
    LinearMap.ker (normalizedLocalConstraintAt (R := ℤ) (d := 1) m 0 2) =
      LinearMap.ker (localConstraintCoordinatesAt (R := ℤ) (d := 1) m 0 2) :=
  ⟨normalizedLocalConstraintAt_eq_zero_iff m 0 2 _,
    normalizedLocalConstraintAt_ker_eq_coordinates m 0 2⟩

/-- The normalized remainder of order one of `Y₀ - received` vanishes at `(center, received)`. -/
private theorem normalizedLocalConstraintAt_one_Y_zero_sub {R : Type*} [CommRing R] (d : ℕ)
    (center received : R) :
    normalizedLocalConstraintAt (d := d) 1 center received (X (some 0) - C received) = 0 := by
  rw [normalizedLocalConstraintAt_eq_zero_iff, SatisfiesLocalConstraints, localConstraintAt,
    LinearMap.comp_apply, projectLowContact, weightedTruncation_eq_zero_iff]
  have h : (unscaledLocalSubstitution d center received).toLinearMap (X (some 0) - C received) =
      X (localT d) * (X (localE d) + localJetSum d) := by
    simp only [AlgHom.toLinearMap_apply, map_sub, unscaledLocalSubstitution_Y_zero, algHom_C,
      algebraMap_eq, mul_add, T_mul_localJetSum]
    ring
  rw [h]
  simpa using mul_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := R) (localContactWeight d) (localT d) le_rfl)
    (by simp : X (localE d) + localJetSum d ∈
      restrictWeightedOrder (R := R) (localContactWeight d) 0)

/-- Order one over `ℤ`: the normalized-remainder contact corollary recovers the factor theorem
for `P - P(center)`. -/
example (d : ℕ) (P : Polynomial ℤ) (center : ℤ) :
    Polynomial.X - Polynomial.C center ∣ P - Polynomial.C (P.eval center) := by
  have h := X_sub_C_pow_dvd_differentialSpecialization_of_normalizedLocalConstraint
    (X (some 0) - C (P.eval center)) P center _ rfl
    (normalizedLocalConstraintAt_one_Y_zero_sub d center (P.eval center))
  simpa [differentialSpecialization, differentialSpecializationHom] using h

/-- The agreement hypothesis is needed: for `P = 0`, `center = 0` and `received = 1`, the
normalized remainder of order one of `Y₀ - 1` vanishes, but `X ∤ Q(X, P) = -1`. -/
example : normalizedLocalConstraintAt (d := 0) 1 (0 : ℤ) 1 (X (some 0) - C 1) = 0 ∧
    ¬ (Polynomial.X - Polynomial.C 0) ^ 1 ∣
      differentialSpecialization (X (some 0) - C 1 : DifferentialPolynomial ℤ 0) 0 := by
  refine ⟨normalizedLocalConstraintAt_one_Y_zero_sub 0 0 1, fun h => ?_⟩
  have h' : (Polynomial.X : Polynomial ℤ) ∣ -1 := by
    simpa [differentialSpecialization, differentialSpecializationHom] using h
  have := Polynomial.eval_dvd (x := 0) h'
  simp at this
