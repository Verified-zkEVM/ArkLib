/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank bounds for matrices with product row indices

A matrix with row index `ι × α` defines a linear map into functions on that product.
Currying the output expresses this map as a product of the maps for each fixed first coordinate.
The rank of the full matrix is therefore at most the sum of the ranks of its row blocks.

## Main statements

* `Matrix.rank_prod_rows_le_sum`: the rank of a matrix with product row indices is at most the
  sum of the ranks of its row blocks.

## References
-/

@[expose] public section

namespace Matrix

/-- The rank of a matrix with row indices `ι × α` is at most the sum of the ranks of its row
blocks, where block `i` consists of rows `(i, a)`. -/
theorem rank_prod_rows_le_sum {ι α κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (M : Matrix (ι × α) κ K) :
    M.rank ≤ ∑ i, (M.submatrix (fun a : α => (i, a)) id).rank := by
  let blocks : ∀ i : ι, (κ → K) →ₗ[K] (α → K) := fun i =>
    (M.submatrix (fun a : α => (i, a)) id).mulVecLin
  let curry : (ι × α → K) ≃ₗ[K] (ι → α → K) :=
    { toFun := fun f i a => f (i, a)
      invFun := fun f p => f p.1 p.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl }
  have hblocks : LinearMap.pi blocks = curry.toLinearMap.comp M.mulVecLin := by
    ext v i a
    simp [blocks, curry, Matrix.mulVec, dotProduct]
  rw [Matrix.rank]
  calc
    Module.finrank K (LinearMap.range M.mulVecLin) =
        Module.finrank K (LinearMap.range (LinearMap.pi blocks)) := by
      rw [hblocks, LinearMap.range_comp, LinearEquiv.finrank_map_eq]
    _ ≤ ∑ i, Module.finrank K (LinearMap.range (blocks i)) :=
      LinearMap.finrank_range_pi_le_sum blocks
    _ = ∑ i, (M.submatrix (fun a : α => (i, a)) id).rank := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

end Matrix
