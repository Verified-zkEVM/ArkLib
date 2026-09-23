/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index
public import ArkLib.Data.CodingTheory.HiddenDerivative.Substitution
public import ArkLib.Data.MvPolynomial.WeightedOrder

/-!
# Linear maps for the hidden-derivative local constraints

This file defines the homogeneous linear constraints that a differential polynomial must satisfy
at one received point `(center, received)`. After the unscaled local substitution, the
constraint is that every monomial `T^i E^b Y^c` of contact order `i + d * b < m` has coefficient
zero. `localConstraintAt` returns the part of the substituted polynomial that must vanish, and
`localConstraintCoordinatesAt` returns the same coefficients as a vector.

The point-dependent map factors through a map that does not depend on the point: first
translate `X = center + T`, `Y₀ = received + T U` and reduce modulo `T^m`
(`translatedLocalTruncation`), then rewrite `U = E + localJetSum d` and keep the low-contact
part (`enlargedLocalConstraintMap`). The reduction modulo `T^m` before the rewrite does not
change the result, because the rewrite sends every generator of `T`-weight `t` to a polynomial
of contact order at least `t`. This is an instance of
`MvPolynomial.weightedTruncation_bind₁_weightedTruncation`. The factorization is what the local
rank bounds in `Interpolation/Local/Rank.lean` use: every local constraint map on the exact
interpolation space factors through one fixed linear map.

All maps are linear over an arbitrary commutative ring `R`.

## Main statements

* `satisfiesLocalConstraints_iff_coordinates_eq_zero` and
  `satisfiesLocalConstraints_iff_coeff_eq_zero`: the polynomial, coordinate, and coefficient
  forms of the local constraints agree.
* `enlargedLocalConstraintMap_truncateLocalT`: reducing modulo `T^m` before the rewrite does not
  change the enlarged constraints.
* `localConstraintAt_eq_enlarged_comp_translated`: the point-dependent map is
  `enlargedLocalConstraintMap m ∘ translatedLocalTruncation m center received`.
* `exactLocalConstraintAt_eq_enlarged_comp`: the same factorization on the exact interpolation
  space.
* `map_unscaledLocalSubstitution`, `map_projectLowContact` and
  `SatisfiesLocalConstraints.map`: coefficient changes commute with the local constraints.
* `globalExactCoefficientConstraintMap`: all local constraints, over an arbitrary index type of
  received points, as one linear map on exact interpolation coefficients.

Parts of this file are adapted, with permission, from Kai Zhe Zheng's `kz99/rs-ld-mca`
formalization.

## References

* [BCPZZ26]
* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]
variable {d D A M W : ℕ}

/-! ### Coefficient projections -/

/-- Reduction modulo `T^m`: keep the monomials whose `T` exponent is below `m`. -/
def truncateLocalT (m : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  weightedTruncation (localTWeight d) m

/-- Keep the monomials of contact order below `m`. -/
def projectLowContact (m : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  weightedTruncation (localContactWeight d) m

/-- The coefficient of `truncateLocalT m F` at `e` is that of `F` if the `T` exponent of `e` is
below `m`, and zero otherwise. -/
@[simp]
theorem coeff_truncateLocalT (m : ℕ) (F : LocalPolynomial R d) (e : LocalVariable d →₀ ℕ) :
    (truncateLocalT (R := R) m F).coeff e = if e (localT d) < m then F.coeff e else 0 := by
  rw [truncateLocalT, coeff_weightedTruncation, weight_localTWeight]

/-- The coefficient of `projectLowContact m F` at `e` is that of `F` if `e` has contact order
below `m`, and zero otherwise. -/
@[simp]
theorem coeff_projectLowContact (m : ℕ) (F : LocalPolynomial R d) (e : LocalVariable d →₀ ℕ) :
    (projectLowContact (R := R) m F).coeff e =
      if localContactOrder d e < m then F.coeff e else 0 :=
  coeff_weightedTruncation _ m F e

/-- Exponents of contact order below `m`. This type is empty for `m = 0` and infinite for `m > 0`:
the visible jets have contact weight zero, and so does `E` when `d = 0`, so every power of `Y₁`
(for `d > 0`) or of `E` (for `d = 0`) has contact order `0`. -/
abbrev LowContactIndex (d m : ℕ) :=
  {e : LocalVariable d →₀ ℕ // localContactOrder d e < m}

/-- All coefficients of contact order below `m`, as a vector indexed by `LowContactIndex d m`. -/
def lowContactCoefficients (m : ℕ) :
    LocalPolynomial R d →ₗ[R] (LowContactIndex d m → R) :=
  LinearMap.pi fun e : LowContactIndex d m => lcoeff R e.1

/-- The low-contact part vanishes exactly when every coefficient of contact order below `m`
vanishes. -/
theorem projectLowContact_eq_zero_iff (m : ℕ) (F : LocalPolynomial R d) :
    projectLowContact (R := R) m F = 0 ↔
      ∀ e, localContactOrder d e < m → F.coeff e = 0 :=
  filterSupport_eq_zero_iff _ F

/-- The low-contact coefficient vector vanishes exactly when every coefficient of contact order
below `m` vanishes. -/
theorem lowContactCoefficients_eq_zero_iff (m : ℕ) (F : LocalPolynomial R d) :
    lowContactCoefficients (R := R) m F = 0 ↔
      ∀ e, localContactOrder d e < m → F.coeff e = 0 := by
  constructor
  · intro h e he
    simpa [lowContactCoefficients] using congrFun h ⟨e, he⟩
  · intro h
    ext e
    simpa [lowContactCoefficients] using h e.1 e.2

/-- The polynomial and coordinate forms of the low-contact projection have the same kernel. -/
theorem projectLowContact_eq_zero_iff_lowContactCoefficients_eq_zero
    (m : ℕ) (F : LocalPolynomial R d) :
    projectLowContact (R := R) m F = 0 ↔ lowContactCoefficients (R := R) m F = 0 := by
  rw [projectLowContact_eq_zero_iff, lowContactCoefficients_eq_zero_iff]

/-! ### Point-dependent and enlarged maps -/

/-- The point-independent map: rewrite `U = E + localJetSum d`, then keep the monomials of
contact order below `m`. -/
def enlargedLocalConstraintMap (m : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (projectLowContact m).comp (rewriteUToE d).toLinearMap

/-- Translation to the local variables `T, U, Y` followed by reduction modulo `T^m`. -/
def translatedLocalTruncation (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (truncateLocalT m).comp (translateToU d center received).toLinearMap

/-- The local constraint map at `(center, received)`: the low-contact part of the unscaled local
substitution. -/
def localConstraintAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (projectLowContact m).comp (unscaledLocalSubstitution d center received).toLinearMap

/-- The local constraints at `(center, received)` as a coefficient vector. -/
def localConstraintCoordinatesAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] (LowContactIndex d m → R) :=
  (lowContactCoefficients m).comp (unscaledLocalSubstitution d center received).toLinearMap

/-- `Q` satisfies the local constraints of multiplicity `m` at `(center, received)`: after the
unscaled local substitution, every monomial of contact order below `m` has coefficient zero. -/
def SatisfiesLocalConstraints (m : ℕ) (center received : R)
    (Q : DifferentialPolynomial R d) : Prop :=
  localConstraintAt m center received Q = 0

/-- The local constraints hold exactly when their coordinate vector vanishes. -/
theorem satisfiesLocalConstraints_iff_coordinates_eq_zero
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    SatisfiesLocalConstraints m center received Q ↔
      localConstraintCoordinatesAt m center received Q = 0 :=
  projectLowContact_eq_zero_iff_lowContactCoefficients_eq_zero m _

/-- The local constraints hold exactly when every low-contact coefficient of the substituted
polynomial vanishes. -/
theorem satisfiesLocalConstraints_iff_coeff_eq_zero
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    SatisfiesLocalConstraints m center received Q ↔
      ∀ e, localContactOrder d e < m →
        (unscaledLocalSubstitution d center received Q).coeff e = 0 :=
  projectLowContact_eq_zero_iff m _

/-- The unscaled local substitution commutes with changing the coefficient ring. -/
theorem map_unscaledLocalSubstitution {S : Type*} [CommRing S] (φ : R →+* S)
    (center received : R) (Q : DifferentialPolynomial R d) :
    MvPolynomial.map φ (unscaledLocalSubstitution d center received Q) =
      unscaledLocalSubstitution d (φ center) (φ received) (MvPolynomial.map φ Q) := by
  simp only [unscaledLocalSubstitution, MvPolynomial.map_bind₁]
  have hhom :
      MvPolynomial.bind₁
          (fun i ↦ MvPolynomial.map φ (unscaledLocalImage d center received i)) =
        MvPolynomial.bind₁ (unscaledLocalImage d (φ center) (φ received)) := by
    apply MvPolynomial.algHom_ext
    intro v
    rcases v with _ | j
    · simp [unscaledLocalImage]
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · simp [unscaledLocalImage, localCorrection]
      · simp [unscaledLocalImage]
  rw [hhom]

/-- Low-contact projection commutes with changing the coefficient ring. -/
theorem map_projectLowContact {S : Type*} [CommRing S] (φ : R →+* S) (m : ℕ)
    (P : LocalPolynomial R d) :
    MvPolynomial.map φ (projectLowContact m P) =
      projectLowContact m (MvPolynomial.map φ P) := by
  ext e
  rw [MvPolynomial.coeff_map, projectLowContact, MvPolynomial.coeff_weightedTruncation,
    projectLowContact, MvPolynomial.coeff_weightedTruncation]
  by_cases he : e.weight (localContactWeight d) < m <;>
    simp [he, MvPolynomial.coeff_map]

/-- Local constraints are preserved by every coefficient-ring homomorphism. -/
theorem SatisfiesLocalConstraints.map {S : Type*} [CommRing S] (φ : R →+* S) (m : ℕ)
    (center received : R) (Q : DifferentialPolynomial R d)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    SatisfiesLocalConstraints m (φ center) (φ received) (MvPolynomial.map φ Q) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply] at hQ ⊢
  rw [← map_unscaledLocalSubstitution, ← map_projectLowContact]
  simpa using congrArg (MvPolynomial.map φ) hQ

/-! ### Truncation factorization -/

/-- The rewrite `U = E + localJetSum d` sends each variable of `T`-weight `t` to a polynomial of
contact order at least `t`. Only `T` has positive `T`-weight, and it is sent to itself. -/
theorem rewriteUToEImage_mem_restrictWeightedOrder (v : LocalVariable d) :
    rewriteUToEImage (R := R) d v ∈
      restrictWeightedOrder (R := R) (localContactWeight d) (localTWeight d v) := by
  rcases v with _ | _ | _
  · exact X_mem_restrictWeightedOrder _ (localT d) le_rfl
  all_goals simp [rewriteUToEImage, localTWeight]

/-- Reduction modulo `T^m` does not change the enlarged low-contact constraints. -/
@[simp]
theorem enlargedLocalConstraintMap_truncateLocalT (m : ℕ) (F : LocalPolynomial R d) :
    enlargedLocalConstraintMap m (truncateLocalT m F) = enlargedLocalConstraintMap (R := R) m F :=
  weightedTruncation_bind₁_weightedTruncation rewriteUToEImage_mem_restrictWeightedOrder m F

/-- The point-dependent local constraint map factors through the point-independent enlarged
map. -/
theorem localConstraintAt_eq_enlarged_comp_translated (m : ℕ) (center received : R) :
    localConstraintAt (d := d) m center received =
      (enlargedLocalConstraintMap m).comp (translatedLocalTruncation m center received) := by
  refine LinearMap.ext fun Q => ?_
  change projectLowContact m (unscaledLocalSubstitution d center received Q) =
    enlargedLocalConstraintMap m (truncateLocalT m (translateToU d center received Q))
  rw [enlargedLocalConstraintMap_truncateLocalT,
    unscaledLocalSubstitution_eq_rewrite_comp_translate]
  rfl

/-- Pointwise form of `localConstraintAt_eq_enlarged_comp_translated`. -/
theorem localConstraintAt_apply_eq_enlarged_translated
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    localConstraintAt m center received Q =
      enlargedLocalConstraintMap m (translatedLocalTruncation m center received Q) :=
  DFunLike.congr_fun (localConstraintAt_eq_enlarged_comp_translated m center received) Q

/-! ### Exact interpolation coordinates -/

/-- The local constraint map restricted to the exact interpolation space. -/
def exactLocalConstraintAt (hdD : d < D) (m : ℕ) (center received : R) :
    exactInterpolationSpace R D A d m M W hdD →ₗ[R] LocalPolynomial R d :=
  (localConstraintAt m center received).domRestrict (exactInterpolationSpace R D A d m M W hdD)

/-- On the exact interpolation space, the local constraint map is the enlarged map composed with
the restricted translated truncation. -/
theorem exactLocalConstraintAt_eq_enlarged_comp (hdD : d < D) (m : ℕ) (center received : R) :
    exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received =
      (enlargedLocalConstraintMap m).comp
        ((translatedLocalTruncation m center received).domRestrict
          (exactInterpolationSpace R D A d m M W hdD)) := by
  rw [exactLocalConstraintAt, localConstraintAt_eq_enlarged_comp_translated]
  rfl

/-- The local constraint map on exact interpolation coefficients. -/
def exactCoefficientLocalConstraintAt (hdD : d < D) (m : ℕ) (center received : R) :
    ExactInterpolationCoefficients R D A d m M W hdD →ₗ[R] LocalPolynomial R d :=
  exactInterpolationCoefficientEvaluator hdD (localConstraintAt m center received)

/-- A single coefficient column is sent to the local constraints of its monomial. -/
@[simp]
theorem exactCoefficientLocalConstraintAt_single {m : ℕ} (hdD : d < D)
    (u : ExactInterpolationIndex D A d m M W hdD) (a center received : R) :
    exactCoefficientLocalConstraintAt (M := M) (W := W) hdD m center received
        (Finsupp.single u a) =
      localConstraintAt m center received (monomial u.1 a) := by
  simp [exactCoefficientLocalConstraintAt]

/-- The local constraints at every received point `(centers i, received i)`, as one linear map
on exact interpolation coefficients. The index type is arbitrary; the codomain is the full
product. -/
def globalExactCoefficientConstraintMap {ι : Type*} {m : ℕ} (hdD : d < D)
    (centers received : ι → R) :
    ExactInterpolationCoefficients R D A d m M W hdD →ₗ[R] (ι → LocalPolynomial R d) :=
  LinearMap.pi fun i =>
    exactCoefficientLocalConstraintAt (M := M) (W := W) hdD m (centers i) (received i)

/-- Coordinate `i` of `globalExactCoefficientConstraintMap` is the local constraint map at
`(centers i, received i)`. -/
@[simp]
theorem globalExactCoefficientConstraintMap_apply {ι : Type*} {m : ℕ} (hdD : d < D)
    (centers received : ι → R) (v : ExactInterpolationCoefficients R D A d m M W hdD) (i : ι) :
    globalExactCoefficientConstraintMap hdD centers received v i =
      exactCoefficientLocalConstraintAt (M := M) (W := W) hdD m (centers i) (received i) v :=
  rfl

end ReedSolomon.HiddenDerivative
