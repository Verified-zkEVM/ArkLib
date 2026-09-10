/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import CompPoly.Multivariate.Operations
public import Mathlib.Algebra.MvPolynomial.PDeriv
/-!
# Computable partial derivatives of multivariate polynomials

This file implements partial differentiation directly on `CMvPolynomial` terms and proves that
it agrees with `MvPolynomial.pderiv` under CompPoly's semantic conversion. It is a critical bridge
for constructing executable Jacobians and Taylor-chart equations without using the noncomputable
`toCMvPolynomial` conversion.
-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

theorem toFinsupp_apply {n : ℕ} (monomial : CMvMonomial n) (i : Fin n) :
    monomial.toFinsupp i = monomial.get i := rfl

/-- Subtract one from coordinate `i` of a computable monomial, truncated at zero. -/
def eraseOne {n : ℕ} (i : Fin n) (monomial : CMvMonomial n) : CMvMonomial n :=
  Vector.ofFn fun j ↦ if j = i then monomial.get j - 1 else monomial.get j

theorem toFinsupp_eraseOne {n : ℕ} (i : Fin n) (monomial : CMvMonomial n) :
    (eraseOne i monomial).toFinsupp = monomial.toFinsupp - Finsupp.single i 1 := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [eraseOne, toFinsupp_apply]
  · simp [eraseOne, toFinsupp_apply, hji]

/-- Computable partial derivative with respect to variable `i`. -/
def partialDerivative {n : ℕ} (i : Fin n) (p : CMvPolynomial n R) : CMvPolynomial n R :=
  Std.ExtTreeMap.foldl
    (fun acc monomial coefficient ↦
      acc + CMvPolynomial.monomial (eraseOne i monomial)
        (coefficient * (monomial.get i : R)))
    0 p.1

/-- Computable partial differentiation agrees with `MvPolynomial.pderiv`. -/
theorem fromCMvPolynomial_partialDerivative {n : ℕ} (i : Fin n)
    (p : CMvPolynomial n R) :
    fromCMvPolynomial (partialDerivative i p) =
      MvPolynomial.pderiv i (fromCMvPolynomial p) := by
  have hfold : partialDerivative i p =
      Finsupp.sum (AddMonoidAlgebra.coeff (fromCMvPolynomial p))
        (fun monomial coefficient ↦
          CMvPolynomial.monomial
            (eraseOne i (CMvMonomial.ofFinsupp monomial))
            (coefficient * (monomial i : R))) := by
    unfold partialDerivative
    rw [foldl_add_comm]
    rw [CPoly.foldl_eq_sum]
    congr 1
    funext monomial coefficient
    simp [CMvMonomial.ofFinsupp]
  rw [hfold, fromCMvPolynomial_finsupp_sum]
  simp_rw [fromCMvPolynomial_monomial, toFinsupp_eraseOne,
    CMvMonomial.toFinsupp_ofFinsupp]
  conv_rhs =>
    rw [← MvPolynomial.support_sum_monomial_coeff (fromCMvPolynomial p)]
    rw [map_sum (MvPolynomial.pderiv i)]
  simp only [MvPolynomial.pderiv_monomial]
  rw [Finsupp.sum, MvPolynomial.finsupp_support_eq_support]
  rfl

end CPoly.CMvPolynomial
