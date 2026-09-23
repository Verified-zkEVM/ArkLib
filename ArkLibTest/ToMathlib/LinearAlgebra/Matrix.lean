/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBlocks

/-!
# Matrix acceptance tests

The rank bound for product-indexed rows applies to a concrete matrix with two nonzero row blocks.
-/

namespace MatrixRowBlocksTest

/-- The two row blocks form the identity matrix. -/
private def twoBlockMatrix : Matrix (Fin 2 × Fin 1) (Fin 2) ℚ :=
  fun row col => if row.1 = col then 1 else 0

private def twoBlockRows : Fin 2 ≃ Fin 2 × Fin 1 where
  toFun i := (i, 0)
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := by cases p with | mk i j => fin_cases j; rfl

private theorem twoBlockMatrix_rank : twoBlockMatrix.rank = 2 := by
  rw [← Matrix.rank_submatrix twoBlockMatrix twoBlockRows (Equiv.refl (Fin 2))]
  have hmatrix : twoBlockMatrix.submatrix twoBlockRows (Equiv.refl (Fin 2)) =
      (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoBlockMatrix, twoBlockRows]
  rw [hmatrix]
  simp

private theorem twoBlock_block_rank (i : Fin 2) :
    (twoBlockMatrix.submatrix (fun a : Fin 1 => (i, a)) id).rank = 1 := by
  let B := twoBlockMatrix.submatrix (fun a : Fin 1 => (i, a)) id
  have hupper : B.rank ≤ 1 := by
    simpa [B] using (Matrix.rank_le_card_height B)
  have hminor : (B.submatrix (fun _ : Fin 1 => (0 : Fin 1))
      (fun _ : Fin 1 => i)) = (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    ext r c
    fin_cases r
    fin_cases c
    simp [B, twoBlockMatrix]
  have hlower : 1 ≤ B.rank := by
    have h := Matrix.rank_submatrix_le B (fun _ : Fin 1 => (0 : Fin 1))
      (fun _ : Fin 1 => i)
    rw [hminor, Matrix.rank_one] at h
    simpa using h
  exact Nat.le_antisymm hupper hlower

/-- The full matrix and its two nonzero blocks have ranks two, one and one. -/
example : twoBlockMatrix.rank = 2 ∧
    (∀ i : Fin 2, (twoBlockMatrix.submatrix (fun a : Fin 1 => (i, a)) id).rank = 1) ∧
    twoBlockMatrix.rank ≤
      ∑ i : Fin 2, (twoBlockMatrix.submatrix (fun a : Fin 1 => (i, a)) id).rank := by
  refine ⟨twoBlockMatrix_rank, fun i => twoBlock_block_rank i, ?_⟩
  rw [twoBlockMatrix_rank]
  have hsum : ∑ i : Fin 2,
      (twoBlockMatrix.submatrix (fun a : Fin 1 => (i, a)) id).rank = 2 := by
    simp [twoBlock_block_rank]
  omega

end MatrixRowBlocksTest
