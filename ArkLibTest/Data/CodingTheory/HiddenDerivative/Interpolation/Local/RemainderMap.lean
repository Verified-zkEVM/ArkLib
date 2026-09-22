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
