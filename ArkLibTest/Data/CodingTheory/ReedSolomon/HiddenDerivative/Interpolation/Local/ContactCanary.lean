/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Contact
import Mathlib.Data.ZMod.Basic
/-!
# Boundary canaries for local contact

These examples exercise the two boundary cases used by the local-contact proof.  Order zero has
no low-contact coefficients even though the auxiliary variable also has weight zero.  The
characteristic-two example has local form `T * E`, so its exact contact order is `1 + 1 = 2`; its
canonical differential specialization is the nonzero polynomial `(X - 1)^2`.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Polynomial

private def quadraticContactEquation : DifferentialPolynomial (ZMod 2) 1 :=
  MvPolynomial.X (some 0) -
    (MvPolynomial.X none - MvPolynomial.C 1) *
      MvPolynomial.X (some (Fin.succ (0 : Fin 1)))

private theorem unscaled_quadraticContactEquation :
    unscaledLocalSubstitution 1 (1 : ZMod 2) 0 quadraticContactEquation =
      MvPolynomial.X (localT 1) * MvPolynomial.X (localE 1) := by
  simp only [quadraticContactEquation, map_sub, map_mul,
    unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_zero,
    unscaledLocalSubstitution_Y_succ, map_one]
  simp [localCorrection]

private theorem coeff_T_mul_E_eq_zero_of_contact_lt_two
    (e : LocalVariable 1 →₀ ℕ) (he : localContactOrder 1 e < 2) :
    MvPolynomial.coeff e
        (MvPolynomial.X (localT 1) * MvPolynomial.X (localE 1) :
          LocalPolynomial (ZMod 2) 1) = 0 := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul,
    MvPolynomial.coeff_monomial]
  split_ifs with h
  · subst e
    simp [localContactOrder, Finsupp.weight_single] at he
  · rfl

private theorem quadraticContactEquation_satisfies :
    SatisfiesLocalConstraints 2 (1 : ZMod 2) 0 quadraticContactEquation := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply]
  change projectLowContact (R := ZMod 2) (d := 1) 2
    (unscaledLocalSubstitution 1 1 0 quadraticContactEquation) = 0
  rw [unscaled_quadraticContactEquation, projectLowContact_eq_zero_iff]
  exact coeff_T_mul_E_eq_zero_of_contact_lt_two

/-- In characteristic two, the signs in the hidden correction still cancel to local form
`T * E`.  The resulting nonzero specialization `(X - 1)^2` has exactly the promised multiplicity
two at the nonzero center `1`. -/
theorem characteristic_two_exact_contact_two_canary :
    differentialSpecialization quadraticContactEquation
        ((Polynomial.X - Polynomial.C 1) ^ 2 : (ZMod 2)[X]) =
          (Polynomial.X - Polynomial.C 1) ^ 2 ∧
      (Polynomial.X - Polynomial.C 1) ^ 2 ∣
        differentialSpecialization quadraticContactEquation
          ((Polynomial.X - Polynomial.C 1) ^ 2 : (ZMod 2)[X]) := by
  have hP : ((Polynomial.X - Polynomial.C 1) ^ 2 : (ZMod 2)[X]).eval 1 = 0 := by simp
  have hderiv :
      Polynomial.derivative
          ((Polynomial.X - Polynomial.C 1) ^ 2 : (ZMod 2)[X]) = 0 := by
    simp [Polynomial.derivative_pow, show (2 : ZMod 2) = 0 by decide]
  constructor
  · simp only [quadraticContactEquation, differentialSpecialization, map_sub, map_mul,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Fin.val_zero,
      Fin.val_succ, Nat.zero_add, Polynomial.hasseDeriv_zero']
    rw [Polynomial.hasseDeriv_one', hderiv]
    ring
  · simpa using X_sub_C_pow_dvd_differentialSpecialization_of_contact
      quadraticContactEquation
        ((Polynomial.X - Polynomial.C 1) ^ 2 : (ZMod 2)[X]) 1 0 hP
          quadraticContactEquation_satisfies

end ReedSolomon.HiddenDerivative
