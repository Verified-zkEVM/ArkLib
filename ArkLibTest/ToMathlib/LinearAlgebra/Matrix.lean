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

/-- The rank of the two-block matrix is bounded by the sum of its block ranks. -/
example : twoBlockMatrix.rank ≤
    ∑ i : Fin 2, (twoBlockMatrix.submatrix (fun a : Fin 1 => (i, a)) id).rank := by
  exact Matrix.rank_prod_rows_le_sum twoBlockMatrix

end MatrixRowBlocksTest
