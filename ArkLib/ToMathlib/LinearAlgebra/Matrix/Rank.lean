/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix rank of coordinate matrices and under coefficient maps

This file adds two facts about `Matrix.rank` for matrices with finitely many columns and an
arbitrary, possibly infinite, row type.

The first identifies the rank of a coordinate matrix with the rank of a linear map. If `b` is a
finite basis of `M` and `f : M →ₗ[R] (m → R)`, the matrix whose column `j` is `f (b j)` has rank
`finrank R (LinearMap.range f)`. Mathlib's `Matrix.rank_eq_finrank_range_toLin` states the same
for matrices with finitely many rows, where `Matrix.toLin` is available.

The second bounds the rank after applying a ring homomorphism `f : K →+* S` to every entry, where
`K` is a field and `S` has the strong rank condition: `(A.map f).rank ≤ A.rank`. Over a field
extension equality holds, but the inequality is what the callers need and its proof is short.

## Main statements

* `Matrix.rank_of_basis`: the rank of the coordinate matrix of `f` in the basis `b`.
* `Matrix.rank_map_le`: the rank does not increase under a coefficient map from a field.

## References

`Matrix.rank_map_le` generalizes `Matrix.rank_map_algebraMap_le` of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Translation.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, which was stated for
`algebraMap F E` between two fields. `Matrix.rank_of_basis` is the generic form of the source's
`rank_weightedSupportLocalCoordinateMatrix` in `Interpolation/Symbolic/LocalRank.lean` at the
same revision.
-/

@[expose] public section

namespace Matrix

open Module Submodule

variable {m n : Type*} [Fintype n]

/-- The matrix whose column `j` is `f (b j)` has rank `finrank R (LinearMap.range f)`. The row
type `m` may be infinite. The range of `f` is spanned by the images of the basis vectors, which
are the columns. -/
theorem rank_of_basis {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (b : Basis n R M) (f : M →ₗ[R] (m → R)) :
    (Matrix.of fun i j => f (b j) i).rank = finrank R (LinearMap.range f) := by
  rw [rank_eq_finrank_span_cols, LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span,
    ← Set.range_comp]
  rfl

/-- Applying a ring homomorphism from a field to every entry does not increase the rank. The
target `S` needs the strong rank condition, so that a span of `k` vectors has `finrank` at most
`k`. The row type `m` may be infinite. -/
theorem rank_map_le {K S : Type*} [Field K] [CommRing S] [StrongRankCondition S] (f : K →+* S)
    (A : Matrix m n K) : (A.map f).rank ≤ A.rank := by
  classical
  set p := span K (Set.range A.col)
  have : Module.Finite K p := Module.Finite.span_of_finite K (Set.finite_range A.col)
  let b := Module.finBasis K p
  let v : Fin (finrank K p) → m → S := fun q i => f ((b q : m → K) i)
  have : Module.Finite S (span S (Set.range v)) :=
    Module.Finite.span_of_finite S (Set.finite_range v)
  rw [rank_eq_finrank_span_cols, rank_eq_finrank_span_cols]
  calc finrank S (span S (Set.range (A.map f).col))
      ≤ finrank S (span S (Set.range v)) := by
        refine Submodule.finrank_mono (span_le.mpr ?_)
        rintro _ ⟨j, rfl⟩
        have hj : A.col j ∈ p := subset_span (Set.mem_range_self j)
        have hsum := b.sum_repr ⟨A.col j, hj⟩
        have hcol : (A.map f).col j = ∑ q, f (b.repr ⟨A.col j, hj⟩ q) • v q := by
          ext i
          have hi := congrFun (congrArg Subtype.val hsum) i
          simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul] at hi
          simp only [col_apply, map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v,
            ← map_mul, ← map_sum, hi]
        rw [hcol]
        exact sum_mem fun q _ => smul_mem _ _ (subset_span (Set.mem_range_self q))
    _ ≤ Fintype.card (Fin (finrank K p)) := finrank_range_le_card v
    _ = finrank K p := Fintype.card_fin _

end Matrix
