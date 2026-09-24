/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank bounds for product-indexed rows

For a matrix whose rows are indexed by a product, the rank is at most the sum of the ranks of its
row blocks. The second row index may be infinite; only the block index and the column index need to
be finite.

## Main statements

* `Matrix.rowBlock` and `Matrix.rank_prod_rows_le_sum`: row blocks and their rank bound.

## References
-/

@[expose] public section

namespace Matrix

/-- The block of rows with first coordinate `i`. -/
def rowBlock {K : Type*} {ι ρ κ : Type*} (A : Matrix (ι × ρ) κ K) (i : ι) :
    Matrix ρ κ K :=
  fun row column => A (i, row) column

/-- A matrix with product-indexed rows has rank at most the sum of its row-block ranks. -/
theorem rank_prod_rows_le_sum {K : Type*} [Field K] {ι ρ κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι × ρ) κ K) : A.rank ≤ ∑ i, (rowBlock A i).rank := by
  let Φ := A.mulVecLin
  let block : ι → Matrix ρ κ K := rowBlock A
  let φ := fun i => (block i).mulVecLin
  let includeRange : Φ.range →ₗ[K] (∀ i, (φ i).range) := {
    toFun y i := ⟨(fun row => y.1 (i, row)), by
      rcases y.2 with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      ext row
      simpa [Φ, φ, block, rowBlock, Matrix.mulVecLin_apply, Matrix.mulVec] using
        congrFun hv (i, row)⟩
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
    _ = ∑ i, (rowBlock A i).rank := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show φ i = (rowBlock A i).mulVecLin by rfl]
      rfl

end Matrix
