/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Contact
public import ArkLib.Data.CodingTheory.HiddenDerivative.NormalizedSubstitution
public import ArkLib.Data.MvPolynomial.MapExponents

/-!
# The normalized remainder map and the contact-order constraint map

The local interpolation condition can be written with the free remainder as `T^(d+1) E`
(`normalizedLocalSubstitution`, then reduction modulo `T^m`), or with the error coordinate scaled
so that the same term is `T E` (`unscaledLocalSubstitution`, then the projection to contact order
below `m`). This file proves that the two maps have the same kernel over every commutative ring.

The error normalization `E ↦ T^d E` sends each monomial to a monomial: it is `mapExponents` of the
injective exponent map `normalizeLocalExponent d : e ↦ e + d · e(E) · single T`, which carries
contact order to `T`-degree. Hence reduction modulo `T^m` after normalization is normalization
after the low-contact projection (`truncateLocalT_normalizeError`), and since normalization is
injective, the normalized remainder vanishes exactly when the contact-order constraints hold.
Combined with `X_sub_C_pow_dvd_differentialSpecialization_of_contact`, a vanishing normalized
remainder at `(center, P(center))` forces `(X - center) ^ m ∣ Q(X, P, D¹P, ..., DᵈP)`.

## Main statements

* `normalizeError_eq_mapExponents`, `normalizeError_injective`.
* `truncateLocalT_normalizeError`.
* `normalizedLocalConstraintAt_eq_normalize_localConstraintAt`,
  `normalizedLocalConstraintAt_eq_zero_iff`,
  `normalizedLocalConstraintAt_ker_eq_localConstraintAt`,
  `normalizedLocalConstraintAt_ker_eq_coordinates`.
* `X_sub_C_pow_dvd_differentialSpecialization_of_normalizedLocalConstraint`: the normalized
  remainder constraint forces contact of order `m` at every agreement point.

## References

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/RemainderMap.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `normalizeLocalExponent` and its `_apply_T`, `_apply_E`, `_apply_Y` and `_injective` lemmas are
  unchanged. The private `normalizeLocalExponent_single_*` lemmas are not needed.
* `normalizeErrorByExponent` is `MvPolynomial.mapExponents (normalizeLocalExponent d)`, so
  `normalizeError_eq_normalizeErrorByExponent` is `normalizeError_eq_mapExponents`, and the private
  `normalizeError_monomial` is public. `normalizeError_injective` is unchanged in statement and
  is an instance of `MvPolynomial.mapExponents_injective`.
* `normalizeLocalExponent_T_eq_contact` is unchanged; `weight_normalizeLocalExponent` restates it
  as the weight identity used by `MvPolynomial.weightedTruncation_mapExponents`.
* The private `filterLocalMonomials_monomial` is the generic `MvPolynomial.filterSupport_monomial`.
* `truncateLocalT_normalizeError`, `normalizedLocalConstraintAt`,
  `normalizedLocalConstraintAt_eq_normalize_localConstraintAt`,
  `normalizedLocalConstraintAt_eq_zero_iff`,
  `normalizedLocalConstraintAt_ker_eq_localConstraintAt` and
  `normalizedLocalConstraintAt_ker_eq_coordinates` are unchanged.

* `X_sub_C_pow_dvd_differentialSpecialization_of_normalizedLocalConstraint` is unchanged. It is
  `X_sub_C_pow_dvd_differentialSpecialization_of_contact` composed with
  `normalizedLocalConstraintAt_eq_zero_iff`; the monomial divisibility argument behind it is the
  generic `MvPolynomial.pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder` in
  `ArkLib.Data.MvPolynomial.WeightedOrder`, which `Local/Contact.lean` already uses, so no new
  generic lemma is needed.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d m : ℕ}

/-- The exponent map induced by `E ↦ T^d E`: the exponent `(i, u, β)` of `T^i E^u Y^β` goes to
`(i + d u, u, β)`. -/
def normalizeLocalExponent (d : ℕ) : (LocalVariable d →₀ ℕ) →+ (LocalVariable d →₀ ℕ) where
  toFun e := e + Finsupp.single (localT d) (d * e (localE d))
  map_zero' := by simp
  map_add' e f := by
    ext v
    simp [mul_add, add_assoc, add_left_comm]

@[simp]
theorem normalizeLocalExponent_apply_T (d : ℕ) (e : LocalVariable d →₀ ℕ) :
    normalizeLocalExponent d e (localT d) = e (localT d) + d * e (localE d) := by
  simp [normalizeLocalExponent]

@[simp]
theorem normalizeLocalExponent_apply_E (d : ℕ) (e : LocalVariable d →₀ ℕ) :
    normalizeLocalExponent d e (localE d) = e (localE d) := by
  simp [normalizeLocalExponent, localT, localE, localAux]

@[simp]
theorem normalizeLocalExponent_apply_Y (d : ℕ) (e : LocalVariable d →₀ ℕ) (j : Fin d) :
    normalizeLocalExponent d e (localY j) = e (localY j) := by
  simp [normalizeLocalExponent, localT, localY]

/-- The exponent map `(i, u, β) ↦ (i + d u, u, β)` is injective: `u` and `β` are unchanged, and
then `i` is recovered from `i + d u`. This holds also for `d = 0`, where the map is the
identity. -/
theorem normalizeLocalExponent_injective (d : ℕ) :
    Function.Injective (normalizeLocalExponent d) := by
  intro e f h
  have hE : e (localE d) = f (localE d) := by
    simpa using congrArg (fun g => g (localE d)) h
  ext v
  rcases v with _ | (_ | j)
  · have hT := congrArg (fun g => g (localT d)) h
    simp only [normalizeLocalExponent_apply_T, hE] at hT
    exact Nat.add_right_cancel hT
  · exact hE
  · have hY := congrArg (fun g => g (localY j)) h
    simp only [normalizeLocalExponent_apply_Y] at hY
    exact hY

/-- Normalization turns contact order into `T`-degree: the new `T` exponent is `i + d u`. -/
theorem normalizeLocalExponent_T_eq_contact (d : ℕ) (e : LocalVariable d →₀ ℕ) :
    normalizeLocalExponent d e (localT d) = localContactOrder d e := by
  rw [normalizeLocalExponent_apply_T, localContactOrder_eq]

/-- The weight form of `normalizeLocalExponent_T_eq_contact`: the `T`-weight after normalization
is the contact weight before it. -/
theorem weight_normalizeLocalExponent (d : ℕ) (e : LocalVariable d →₀ ℕ) :
    (normalizeLocalExponent d e).weight (localTWeight d) = e.weight (localContactWeight d) := by
  rw [weight_localTWeight, normalizeLocalExponent_T_eq_contact]
  rfl

/-- Error normalization is the relabelling of exponents by `normalizeLocalExponent`, since it
sends each variable to a monomial with coefficient one. -/
theorem normalizeError_eq_mapExponents (d : ℕ) :
    normalizeError (R := R) d = mapExponents (normalizeLocalExponent d) := by
  refine algHom_ext fun v => ?_
  conv_rhs => rw [X, mapExponents_monomial]
  rcases v with _ | (_ | j)
  · rw [show (none : LocalVariable d) = localT d from rfl, normalizeError_T, X]
    congr 1
    ext v
    simp [normalizeLocalExponent, localT, localE, localAux]
  · rw [show (some none : LocalVariable d) = localE d from rfl, normalizeError_E,
      X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
    congr 1
    ext v
    simp [normalizeLocalExponent, localT, localE, localAux, add_comm]
  · rw [show (some (some j) : LocalVariable d) = localY j from rfl, normalizeError_Y, X]
    congr 1
    ext v
    simp [normalizeLocalExponent, localT, localE, localAux, localY]

/-- Error normalization of a monomial: `c T^i E^u Y^β ↦ c T^(i + d u) E^u Y^β`. -/
theorem normalizeError_monomial (d : ℕ) (e : LocalVariable d →₀ ℕ) (c : R) :
    normalizeError d (monomial e c) = monomial (normalizeLocalExponent d e) c := by
  rw [normalizeError_eq_mapExponents, mapExponents_monomial]

/-- Error normalization is injective over every commutative ring. -/
theorem normalizeError_injective (d : ℕ) :
    Function.Injective (normalizeError (R := R) d) := by
  rw [normalizeError_eq_mapExponents]
  exact mapExponents_injective (normalizeLocalExponent_injective d)

/-- Reduction modulo `T^m` after normalization is normalization after the projection to contact
order below `m`. -/
theorem truncateLocalT_normalizeError (m : ℕ) (F : LocalPolynomial R d) :
    truncateLocalT (R := R) (d := d) m (normalizeError d F) =
      normalizeError d (projectLowContact m F) := by
  rw [normalizeError_eq_mapExponents, truncateLocalT, projectLowContact]
  exact weightedTruncation_mapExponents _ (weight_normalizeLocalExponent d) m F

/-- The normalized local remainder map at `(center, received)`: substitute with the free
remainder written `T^(d+1) E`, then reduce modulo `T^m`. -/
def normalizedLocalConstraintAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (truncateLocalT (R := R) (d := d) m).comp
    (normalizedLocalSubstitution d center received).toLinearMap

/-- The normalized remainder map is error normalization applied to the contact-order constraint
map. -/
theorem normalizedLocalConstraintAt_eq_normalize_localConstraintAt
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    normalizedLocalConstraintAt m center received Q =
      normalizeError d (localConstraintAt m center received Q) := by
  simp only [normalizedLocalConstraintAt, localConstraintAt, LinearMap.coe_comp,
    AlgHom.coe_toLinearMap, Function.comp_apply,
    normalizedLocalSubstitution_eq_normalize_comp_unscaled, AlgHom.coe_comp,
    truncateLocalT_normalizeError]

/-- The normalized remainder of `Q` vanishes exactly when `Q` satisfies the contact-order local
constraints, over every commutative ring. -/
theorem normalizedLocalConstraintAt_eq_zero_iff
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    normalizedLocalConstraintAt m center received Q = 0 ↔
      SatisfiesLocalConstraints m center received Q := by
  rw [normalizedLocalConstraintAt_eq_normalize_localConstraintAt, SatisfiesLocalConstraints,
    (normalizeError_injective d).eq_iff' (map_zero _)]

/-- The normalized remainder map and the contact-order constraint map have the same kernel. -/
theorem normalizedLocalConstraintAt_ker_eq_localConstraintAt (m : ℕ) (center received : R) :
    LinearMap.ker (normalizedLocalConstraintAt (d := d) m center received) =
      LinearMap.ker (localConstraintAt (d := d) m center received) := by
  ext Q
  exact normalizedLocalConstraintAt_eq_zero_iff m center received Q

/-- The normalized remainder map has the kernel of the low-contact coefficient vector. -/
theorem normalizedLocalConstraintAt_ker_eq_coordinates (m : ℕ) (center received : R) :
    LinearMap.ker (normalizedLocalConstraintAt (d := d) m center received) =
      LinearMap.ker (localConstraintCoordinatesAt (d := d) m center received) := by
  ext Q
  rw [LinearMap.mem_ker, LinearMap.mem_ker, normalizedLocalConstraintAt_eq_zero_iff,
    satisfiesLocalConstraints_iff_coordinates_eq_zero]

/-- If the normalized remainder of `Q` at `(center, received)` vanishes and
`P(center) = received`, then `(X - center) ^ m` divides `Q(X, P, D¹P, ..., DᵈP)`, over every
commutative ring. The hypothesis `P(center) = received` is needed because the remainder map sees
`P` only through the received value at `center`. -/
theorem X_sub_C_pow_dvd_differentialSpecialization_of_normalizedLocalConstraint
    (Q : DifferentialPolynomial R d) (P : Polynomial R) (center received : R)
    (hP : P.eval center = received) (hQ : normalizedLocalConstraintAt m center received Q = 0) :
    (Polynomial.X - Polynomial.C center) ^ m ∣ differentialSpecialization Q P :=
  X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P center received hP
    ((normalizedLocalConstraintAt_eq_zero_iff m center received Q).mp hQ)

end ReedSolomon.HiddenDerivative
