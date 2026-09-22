/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Contact

/-!
# Local contact acceptance tests

* Order zero: the constraints
  are vacuous and the conclusion is divisibility by `(X - center) ^ 0 = 1`.
* Order one: `Y₀ - received` satisfies the multiplicity-one constraints at every point, and the
  contact theorem then gives `(X - center) ∣ P - received` for every `P` with
  `P(center) = received`, over any commutative ring and for every jet order `d`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Over `ℤ` with `d = 0`: order zero imposes nothing and concludes nothing. -/
example (Q : DifferentialPolynomial ℤ 0) (P : Polynomial ℤ) (center received : ℤ)
    (hP : P.eval center = received) :
    SatisfiesLocalConstraints 0 center received Q ∧
      (Polynomial.X - Polynomial.C center) ^ 0 ∣ differentialSpecialization Q P := by
  have hQ : SatisfiesLocalConstraints 0 center received Q :=
    (satisfiesLocalConstraints_iff_coeff_eq_zero 0 center received Q).mpr
      fun _ he ↦ absurd he (Nat.not_lt_zero _)
  exact ⟨hQ, X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P center received hP hQ⟩

/-- `Y₀ - received` satisfies the multiplicity-one constraints. -/
private theorem satisfiesLocalConstraints_one_Y_zero_sub {R : Type*} [CommRing R] (d : ℕ)
    (center received : R) :
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
    (X_mem_restrictWeightedOrder (R := R) (localContactWeight d) (localT d) le_rfl)
    (by simp : X (localE d) + localJetSum d ∈
      restrictWeightedOrder (R := R) (localContactWeight d) 0)

/-- Order one over `ℤ`: the contact theorem recovers the factor theorem for `P - P(center)`. -/
example (d : ℕ) (P : Polynomial ℤ) (center : ℤ) :
    Polynomial.X - Polynomial.C center ∣ P - Polynomial.C (P.eval center) := by
  have h := X_sub_C_pow_dvd_differentialSpecialization_of_contact
    (X (some 0) - C (P.eval center)) P center _ rfl
    (satisfiesLocalConstraints_one_Y_zero_sub d center (P.eval center))
  simpa [differentialSpecialization, differentialSpecializationHom] using h

/-- The shifted-jet form at order one: `X ∣ P(center + X) - P(center)`. -/
example (d : ℕ) (P : Polynomial ℚ) (center : ℚ) :
    Polynomial.X ∣ Polynomial.taylor center P - Polynomial.C (P.eval center) := by
  have h := X_pow_dvd_shiftedJetSubstitution_of_contact
    (X (some 0) - C (P.eval center)) P center _ rfl
    (satisfiesLocalConstraints_one_Y_zero_sub d center (P.eval center))
  simpa using h
