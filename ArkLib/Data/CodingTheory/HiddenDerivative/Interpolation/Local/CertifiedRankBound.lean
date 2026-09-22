/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.KernelSliceIndependence
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Rank

/-!
# The certified bound on the local constraint rank

The exact local constraint map at a received point has rank at most
`certifiedEnlargedRankBound d m M W`. This is `finrank_range_exactLocalConstraintAt_le_sub` with
`S = localIntermediateSpace F d m M W`, which contains the translated truncations, and with the
exhibited kernel family `exhibitedKernelFamilyKernelMap`, which injects into the kernel of the
enlarged map on `S`. The dimensions of `S` and of the family are
`∑_{r < m} Λ_d(W + r) (r + 1)(M + 1)` and `∑_{r < m} Λ_d(W + r) (r + 1 - h_r)(M + 1 - h_r)`, and
their difference is the certified bound by
`ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound`.

## Main statements

* `finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound`: the rank of the enlarged map
  on the intermediate space is at most the certified bound.
* `finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound`: the rank of the exact local
  constraint map is at most the certified bound, at every center and received value.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Rank.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d:
`finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound` and
`finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound`, with the same hypotheses
(`0 < d` and `d < D`) and the same conclusion. The second is proved as an instance of
`finrank_range_exactLocalConstraintAt_le_sub` rather than by the source's direct factorization.

Deferred: the consumers of the bound (the free-order dimension count and rate rounding), and any
treatment of `d = 0`, where the intermediate space is still finite-dimensional but its dimension
formula and the contact threshold both change.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Module

variable {F : Type*} [Field F] {d : ℕ}

/-- The rank of the enlarged local constraint map on the intermediate space is at most
`certifiedEnlargedRankBound d m M W`. The hypothesis `0 < d` is needed for both the dimension
formulas and the kernel family: for `d = 0` the contact threshold is `0` and the exhibited
products are not in the kernel. -/
theorem finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound (hd : 0 < d)
    (m M W : ℕ) :
    finrank F (LinearMap.range (intermediateConstraintMap (R := F) (d := d) m M W)) ≤
      certifiedEnlargedRankBound d m M W := by
  have : Module.Finite F (localIntermediateSpace F d m M W) :=
    localIntermediateSpace_finite hd m M W
  have h := LinearMap.finrank_range_le_sub_of_injective_ker _
    (exhibitedKernelFamilyKernelMap (R := F) hd m M W)
    (exhibitedKernelFamilyKernelMap_injective hd m M W)
  rwa [finrank_localIntermediateSpace hd, finrank_exhibitedKernelFamilySource hd,
    ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound] at h

/-- The rank of the exact local constraint map at any center and received value is at most
`certifiedEnlargedRankBound d m M W`. The hypothesis `d < D` is the one of the exact
interpolation space, and `0 < d` is needed as in
`finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound`. -/
theorem finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound {D A m M W : ℕ}
    (hd : 0 < d) (hdD : d < D) (center received : F) :
    finrank F (LinearMap.range
        (exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received)) ≤
      certifiedEnlargedRankBound d m M W := by
  have : Module.Finite F (localIntermediateSpace F d m M W) :=
    localIntermediateSpace_finite hd m M W
  have h := finrank_range_exactLocalConstraintAt_le_sub (A := A) hdD m center received
    (localIntermediateSpace F d m M W)
    (fun _ hQ => translatedLocalTruncation_mem_localIntermediateSpace hdD center received hQ)
    (exhibitedKernelFamilyKernelMap hd m M W) (exhibitedKernelFamilyKernelMap_injective hd m M W)
  rwa [finrank_localIntermediateSpace hd, finrank_exhibitedKernelFamilySource hd,
    ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound] at h

end ReedSolomon.HiddenDerivative
