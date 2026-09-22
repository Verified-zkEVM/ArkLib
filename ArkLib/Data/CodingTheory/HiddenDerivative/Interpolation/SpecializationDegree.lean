/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index

/-!
# Specialization degree of exact interpolation polynomials

Every member `Q` of the exact interpolation space has `differentialWeightedDegree D Q < m * A`
(`differentialWeightedDegree_lt_of_mem_exactInterpolationSpace`), and substituting a polynomial
`P` of degree at most `D` into `Q` gives degree at most `differentialWeightedDegree D Q`
(`PolynomialDifferential.natDegree_differentialSpecialization_le`). Hence
`Q(X, P, D¹P, ..., DᵈP)` has degree below `m * A`. This is the degree half of the global
vanishing argument: in `Interpolation.Global.Multiplicity`, contact of order `m` at `A` distinct
agreement points then forces the specialization to vanish.

## Main statements

* `eq_zero_of_mem_exactInterpolationSpace_of_mul_eq_zero`: the space is `{0}` when `m * A = 0`.
* `natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace`: the bound for a member
  of the space.
* `natDegree_differentialSpecialization_exactInterpolationPolynomial_lt`: the bound for the
  polynomial with given coefficient coordinates.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/
SpecializationDegree.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. Both
theorems keep their statements; they hold over any commutative semiring, as in the source.
`eq_zero_of_mem_exactInterpolationSpace_of_mul_eq_zero` is new; it removes the positivity
hypothesis from the global vanishing theorem in `Interpolation.Global.Multiplicity`.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.HiddenDerivative

variable {R : Type*} [CommSemiring R] {D A d m M W : ℕ}

/-- When `m * A = 0` the exact interpolation space is `{0}`: every exponent would need weight
below `0`. -/
theorem eq_zero_of_mem_exactInterpolationSpace_of_mul_eq_zero (hzero : m * A = 0) (hdD : d < D)
    {Q : DifferentialPolynomial R d} (hQ : Q ∈ exactInterpolationSpace R D A d m M W hdD) :
    Q = 0 := by
  rw [← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro u hu
  have := (mem_exactInterpolationSpace_iff.mp hQ u hu).2.2
  omega

/-- If `Q` lies in the exact interpolation space and `P` has degree at most `D`, then
`Q(X, P, D¹P, ..., DᵈP)` has degree below `m * A`. The hypothesis `0 < m * A` is needed: for
`m * A = 0` the space is `{0}` and `0` has natural degree `0`, which is not below `0`. -/
theorem natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace
    (hbudget : 0 < m * A) (hdD : d < D) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ exactInterpolationSpace R D A d m M W hdD) (P : R[X]) (hP : P.natDegree ≤ D) :
    (differentialSpecialization Q P).natDegree < m * A :=
  (natDegree_differentialSpecialization_le Q P hP).trans_lt
    (differentialWeightedDegree_lt_of_mem_exactInterpolationSpace hbudget hdD hQ)

/-- Coefficient form of `natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace`:
the polynomial with coefficient coordinates `c` in the exact monomial basis specializes at any `P`
of degree at most `D` to a polynomial of degree below `m * A`. -/
theorem natDegree_differentialSpecialization_exactInterpolationPolynomial_lt
    (hbudget : 0 < m * A) (hdD : d < D) (c : ExactInterpolationCoefficients R D A d m M W hdD)
    (P : R[X]) (hP : P.natDegree ≤ D) :
    (differentialSpecialization
      (exactInterpolationPolynomial hdD c : DifferentialPolynomial R d) P).natDegree < m * A :=
  natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace hbudget hdD
    (exactInterpolationPolynomial hdD c).property P hP

end ReedSolomon.HiddenDerivative
