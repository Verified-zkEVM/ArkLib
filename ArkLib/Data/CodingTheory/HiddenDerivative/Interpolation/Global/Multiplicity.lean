/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Contact
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SpecializationDegree
public import ArkLib.ToMathlib.Polynomial.RootMultiplicity

/-!
# Global vanishing of interpolation polynomials at agreeing polynomials

Let `Q` be in the exact interpolation space and satisfy the local constraints of order `m` at every
evaluation point `(points i, received i)`. If `P` has degree at most `D` and agrees with the
received word at `A` indices with distinct evaluation points, then `Q(X, P, D¹P, ..., DᵈP) = 0`.

Each agreement gives `(X - points i) ^ m ∣ Q(X, P, ...)`
(`X_sub_C_pow_dvd_differentialSpecialization_of_contact`), the specialization has degree below
`m * A` (`natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace`), and a
polynomial over a domain with `A` distinct roots of multiplicity `m` and degree below `m * A` is
zero (`Polynomial.eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn`).

The same argument works with any `Q` whose weighted degree `differentialWeightedDegree D Q` is
below `m * A`, bounding the specialization's degree by `natDegree_differentialSpecialization_le`
instead of by membership in the exact space.

## Main statements

* `differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements`.
* `differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt`: the weighted-degree form.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Global/
Multiplicity.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements` keeps its
  statement, with `[Field F]` generalized to `[CommRing R] [IsDomain R]` and the hypothesis
  `0 < m * A` dropped.
* `differentialSpecialization_eq_zero_of_global_multiplicity` is
  `Polynomial.eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn` applied to
  `W = differentialSpecialization Q P` and is not restated.
* `differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt` is the argument of the
  source's `HiddenDerivativeInterpolationCertificate.specializes_to_zero` (in
  `Interpolation/Certificates.lean`), stated for any `Q` over a domain, with the local
  constraints required only on the agreement indices.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.HiddenDerivative

variable {ι R : Type*} [CommRing R] [IsDomain R] {D A d m M W : ℕ}

/-- Let `Q` be in the exact interpolation space and satisfy the local constraints of order `m` at
every `(points i, received i)`. If `P` has degree at most `D` and `P (points i) = received i` for
every `i` in `indices`, the points are distinct on `indices` and `A ≤ #indices`, then
`Q(X, P, D¹P, ..., DᵈP) = 0`.

`indices` may contain more than `A` indices, and the points only need to be distinct on
`indices`. No positivity of `m * A` is needed: when `m * A = 0` the exact space is `{0}`. The
domain hypothesis is used only in the final root count. -/
theorem differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
    (hdD : d < D) (points received : ι → R) (indices : Finset ι)
    {Q : DifferentialPolynomial R d} (hQspace : Q ∈ exactInterpolationSpace R D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (points i) (received i) Q)
    (P : R[X]) (hPdegree : P.natDegree ≤ D) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : A ≤ indices.card) (hagreements : ∀ i ∈ indices, P.eval (points i) = received i) :
    differentialSpecialization Q P = 0 := by
  rcases Nat.eq_zero_or_pos (m * A) with hzero | hbudget
  · rw [eq_zero_of_mem_exactInterpolationSpace_of_mul_eq_zero hzero hdD hQspace]
    exact map_zero (differentialSpecializationHom (d := d) P)
  exact eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn points indices m A hpoints hcard
    (fun i hi ↦ X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P (points i) (received i)
      (hagreements i hi) (hconstraints i))
    (natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace hbudget hdD hQspace P
      hPdegree)

/-- Let `Q` have weighted degree `differentialWeightedDegree D Q < m * A` and satisfy the local
constraints of order `m` at `(points i, received i)` for every `i` in `indices`. If `P` has degree
at most `D`, `P (points i) = received i` for every `i` in `indices`, the points are distinct on
`indices` and `A ≤ #indices`, then `Q(X, P, D¹P, ..., DᵈP) = 0`.

Each agreement gives `(X - points i) ^ m ∣ Q(X, P, ...)`, and the specialization has degree at most
the weighted degree, hence below `m * A`. The degree bound on `P` is needed because the weights
`differentialWeight D` bound the degrees of `P` and its Hasse derivatives only when
`P.natDegree ≤ D`. The domain hypothesis is used only in the final root count. -/
theorem differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (points received : ι → R) (indices : Finset ι) {Q : DifferentialPolynomial R d}
    (hdegree : differentialWeightedDegree D Q < m * A)
    (hconstraints : ∀ i ∈ indices, SatisfiesLocalConstraints m (points i) (received i) Q)
    (P : R[X]) (hPdegree : P.natDegree ≤ D) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : A ≤ indices.card) (hagreements : ∀ i ∈ indices, P.eval (points i) = received i) :
    differentialSpecialization Q P = 0 :=
  eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn points indices m A hpoints hcard
    (fun i hi ↦ X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P (points i) (received i)
      (hagreements i hi) (hconstraints i hi))
    ((natDegree_differentialSpecialization_le Q P hPdegree).trans_lt hdegree)

end ReedSolomon.HiddenDerivative
