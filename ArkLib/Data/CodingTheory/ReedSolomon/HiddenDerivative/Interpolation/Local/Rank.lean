/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional

/-!
# Rank bounds for the local constraint maps

Let `S` be a finite-dimensional space of local polynomials that contains the translated
truncation `translatedLocalTruncation m center received Q` of every `Q` in the exact
interpolation space. Then the local constraint map on the exact interpolation space factors as

```text
exactLocalConstraintAt = (enlargedLocalConstraintMap m restricted to S) ∘ (translation into S),
```

so its rank is at most the rank of the enlarged map on `S`. If in addition a space `K` maps
injectively into the kernel of the enlarged map on `S`, the rank is at most
`finrank S - finrank K`. The bound depends on `S` and `K` but not on the received point, which is
what makes it uniform over all points at once.

Neither bound claims equality with the true rank: `K` need not span the kernel.

## Main statements

* `exactLocalConstraintAt_eq_enlarged_domRestrict_comp`: the factorization through `S`.
* `finrank_range_exactLocalConstraintAt_le_enlarged`: the rank is at most the rank of the
  enlarged map on `S`.
* `finrank_range_exactLocalConstraintAt_le_sub`: the rank is at most `finrank S - finrank K`.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Rank.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source's two linear-algebra
lemmas `finrank_range_le_sub_finrank_of_injective_to_ker` and `finrank_range_comp_le_outer` are
now `LinearMap.finrank_range_le_sub_of_injective_ker` and `LinearMap.finrank_range_comp_le_left`
in `ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional`. The source's
`finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound` and
`finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound` are stated for one specific space
(`localIntermediateSpace`), one specific kernel family, and the explicit count
`certifiedEnlargedRankBound d m M W`; `finrank_range_exactLocalConstraintAt_le_sub` is their
common form for an arbitrary finite-dimensional `S` and an arbitrary injection into the kernel.

Deferred to the next slice: the intermediate space `localIntermediateSpace` and the proof that it
contains the translated truncations (`Interpolation/Local/IntermediateSpace.lean`), the exhibited
kernel family and its injectivity (`ConstraintKernel.lean`, `KernelSliceIndependence.lean`), the
dimension counts (`Counting.lean`), and
`ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound`. With those, the source theorems are
instances of `finrank_range_exactLocalConstraintAt_le_sub`.

* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], ECCC TR26-164, Section 3.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], exact finite interpolation analysis.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Module

variable {d D A M W : ℕ}

/-- The translated truncation of the exact interpolation space, as a map into a space `S` that
contains all of its values. -/
def translatedExactLocalTruncation {R : Type*} [CommRing R] (hdD : d < D) (m : ℕ)
    (center received : R) (S : Submodule R (LocalPolynomial R d))
    (hS : ∀ Q ∈ exactInterpolationSpace R D A d m M W hdD,
      translatedLocalTruncation m center received Q ∈ S) :
    exactInterpolationSpace R D A d m M W hdD →ₗ[R] S :=
  ((translatedLocalTruncation m center received).domRestrict
    (exactInterpolationSpace R D A d m M W hdD)).codRestrict S fun Q => hS Q.1 Q.2

/-- The exact local constraint map factors through any space `S` that contains the translated
truncations of the exact interpolation space. -/
theorem exactLocalConstraintAt_eq_enlarged_domRestrict_comp {R : Type*} [CommRing R]
    (hdD : d < D) (m : ℕ) (center received : R) (S : Submodule R (LocalPolynomial R d))
    (hS : ∀ Q ∈ exactInterpolationSpace R D A d m M W hdD,
      translatedLocalTruncation m center received Q ∈ S) :
    exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received =
      ((enlargedLocalConstraintMap m).domRestrict S).comp
        (translatedExactLocalTruncation hdD m center received S hS) := by
  rw [exactLocalConstraintAt_eq_enlarged_comp]
  rfl

/-- The rank of the exact local constraint map is at most the rank of the enlarged map on `S`.
`S` must be finite-dimensional because `finrank` of an infinite-dimensional space is zero. -/
theorem finrank_range_exactLocalConstraintAt_le_enlarged {F : Type*} [Field F]
    (hdD : d < D) (m : ℕ) (center received : F) (S : Submodule F (LocalPolynomial F d))
    [FiniteDimensional F S]
    (hS : ∀ Q ∈ exactInterpolationSpace F D A d m M W hdD,
      translatedLocalTruncation m center received Q ∈ S) :
    finrank F (LinearMap.range
        (exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received)) ≤
      finrank F (LinearMap.range ((enlargedLocalConstraintMap (R := F) m).domRestrict S)) := by
  rw [exactLocalConstraintAt_eq_enlarged_domRestrict_comp hdD m center received S hS]
  exact LinearMap.finrank_range_comp_le_left _ _

/-- If `K` maps injectively into the kernel of the enlarged map on `S`, then the exact local
constraint map has rank at most `finrank S - finrank K`, at every received point for which `S`
contains the translated truncations. -/
theorem finrank_range_exactLocalConstraintAt_le_sub {F K : Type*} [Field F] [AddCommGroup K]
    [Module F K] (hdD : d < D) (m : ℕ) (center received : F)
    (S : Submodule F (LocalPolynomial F d)) [FiniteDimensional F S]
    (hS : ∀ Q ∈ exactInterpolationSpace F D A d m M W hdD,
      translatedLocalTruncation m center received Q ∈ S)
    (g : K →ₗ[F] LinearMap.ker ((enlargedLocalConstraintMap (R := F) m).domRestrict S))
    (hg : Function.Injective g) :
    finrank F (LinearMap.range
        (exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received)) ≤
      finrank F S - finrank F K :=
  (finrank_range_exactLocalConstraintAt_le_enlarged hdD m center received S hS).trans
    (LinearMap.finrank_range_le_sub_of_injective_ker _ g hg)

end ReedSolomon.HiddenDerivative
