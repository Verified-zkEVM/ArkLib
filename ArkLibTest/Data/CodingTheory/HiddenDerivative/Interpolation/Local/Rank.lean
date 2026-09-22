/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Rank

/-!
# Local rank bound acceptance tests

The image of the translated truncation is itself a finite-dimensional space containing every
translated truncation, so it can serve as `S`; with no exhibited kernel this recovers the
trivial bound by the dimension of the exact space. A numerical bound follows from any `S` and
kernel injection whose dimensions differ by that number; the certified bound
`finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound` is obtained this way.
-/

open Module PolynomialDifferential ReedSolomon.HiddenDerivative

/-- With `S` the image of the translated truncation and no exhibited kernel, the rank is at most
the dimension of the exact interpolation space. -/
example {F : Type*} [Field F] {D A d m M W : ℕ} (hdD : d < D) (center received : F) :
    finrank F (LinearMap.range
        (exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received)) ≤
      finrank F (exactInterpolationSpace F D A d m M W hdD) := by
  let S := LinearMap.range ((translatedLocalTruncation (d := d) m center received).domRestrict
    (exactInterpolationSpace F D A d m M W hdD))
  refine (finrank_range_exactLocalConstraintAt_le_sub hdD m center received S
    (fun Q hQ => ⟨⟨Q, hQ⟩, rfl⟩) (0 : (⊥ : Submodule F F) →ₗ[F] _)
    (fun x y _ => Subsingleton.elim x y)).trans ?_
  simpa using LinearMap.finrank_range_le _

/-- An intermediate space `S` and a kernel injection whose dimensions differ by
`bound` give the uniform bound `bound` at every received point that `S` covers. -/
example {F K : Type*} [Field F] [AddCommGroup K] [Module F K] {D A d m M W bound : ℕ}
    (hdD : d < D) (S : Submodule F (LocalPolynomial F d)) [FiniteDimensional F S]
    (g : K →ₗ[F] LinearMap.ker ((enlargedLocalConstraintMap (R := F) m).domRestrict S))
    (hg : Function.Injective g) (hbound : finrank F S - finrank F K = bound)
    (hS : ∀ center received : F, ∀ Q ∈ exactInterpolationSpace F D A d m M W hdD,
      translatedLocalTruncation m center received Q ∈ S)
    (center received : F) :
    finrank F (LinearMap.range
        (exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received)) ≤ bound :=
  hbound ▸ finrank_range_exactLocalConstraintAt_le_sub hdD m center received S
    (hS center received) g hg
