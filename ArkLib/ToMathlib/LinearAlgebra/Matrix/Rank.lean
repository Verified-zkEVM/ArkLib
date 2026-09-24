/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix rank of coordinate matrices and under coefficient maps

This file adds three facts about `Matrix.rank` for matrices with finitely many columns and an
arbitrary, possibly infinite, row type.

The first identifies the rank of a coordinate matrix with the rank of a linear map. If `b` is a
finite basis of `M` and `f : M →ₗ[R] (m → R)`, the matrix whose column `j` is `f (b j)` has
rank `finrank R (LinearMap.range f)`. Mathlib's `Matrix.rank_eq_finrank_range_toLin` states the
same for matrices with finitely many rows, where `Matrix.toLin` is available.

The second bounds the rank after applying a ring homomorphism `f : K →+* S` to every entry, where
`K` is a field and `S` has the strong rank condition: `(A.map f).rank ≤ A.rank`. Over a field
extension equality holds, but the inequality is what the callers need and its proof is short.
The third bounds the rank of a matrix with product row indices by the sum of the ranks of its
row blocks.

## Main statements

* `Matrix.rank_of_basis`: the rank of the coordinate matrix of `f` in the basis `b`.
* `Matrix.rank_map_le`: the rank does not increase under a coefficient map from a field.
* `Matrix.rank_prod_rows_le_sum`: the rank is at most the sum of the ranks of its row blocks.

## References

* [DKT26]
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

/-- A matrix with product row indices has rank at most the sum of the ranks of its row blocks.
The block at `i` has entries `A (i, row) column`. -/
theorem rank_prod_rows_le_sum {K ι ρ κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (A : Matrix (ι × ρ) κ K) :
    A.rank ≤ ∑ i, Matrix.rank (fun row column => A (i, row) column) := by
  let Φ := A.mulVecLin
  let block : ι → Matrix ρ κ K := fun i row column => A (i, row) column
  let φ := fun i => (block i).mulVecLin
  let includeRange : Φ.range →ₗ[K] ∀ i, (φ i).range := {
    toFun y i := ⟨(fun row => y.1 (i, row)), by
      rcases y.2 with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      ext row
      change (block i).mulVecLin v row = y.1 (i, row)
      have hblock : (block i).mulVecLin v row = A.mulVecLin v (i, row) := by
        change (block i *ᵥ v) row = (A *ᵥ v) (i, row)
        simp [block, Matrix.mulVec]
      exact hblock.trans (congrFun hv (i, row))⟩
    map_add' x y := by
      ext i row
      rfl
    map_smul' a x := by
      ext i row
      rfl
  }
  have hinjective : Function.Injective includeRange := by
    intro x y hxy
    apply Subtype.ext
    funext row
    have hi := congrArg Subtype.val (congrFun hxy row.1)
    exact congrFun hi row.2
  change Module.finrank K A.mulVecLin.range ≤ _
  calc
    Module.finrank K Φ.range ≤ Module.finrank K (∀ i, (φ i).range) :=
      LinearMap.finrank_le_finrank_of_injective hinjective
    _ = ∑ i, Module.finrank K (φ i).range := Module.finrank_pi_fintype K
    _ = ∑ i, Matrix.rank (block i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show φ i = (block i).mulVecLin by rfl]
      rfl

end Matrix
