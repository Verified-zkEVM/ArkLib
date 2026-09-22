/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.SupportedRows

/-!
# Supported-row restriction acceptance tests

The rows `0` and `2` of `!![1; 0; 2]` carry all its nonzero entries, so restricting to them keeps
the kernel and the rank. Restricting `!![1]` to no rows drops a nonzero entry and enlarges the
kernel, so the covering hypothesis is needed.
-/

open scoped Matrix

namespace SupportedRowsTest

/-- A `3 × 1` matrix whose middle row is zero. -/
def M₀ : Matrix (Fin 3) (Fin 1) ℚ := !![1; 0; 2]

/-- The rows `0` and `2`. -/
def r₀ : Fin 2 → Fin 3 := ![0, 2]

/-- Every row of `M₀` with a nonzero entry is `0` or `2`. -/
theorem hr₀ : ∀ i j, M₀ i j ≠ 0 → i ∈ Set.range r₀ := by
  intro i j h
  fin_cases i
  · exact ⟨0, rfl⟩
  · simp [M₀] at h
  · exact ⟨1, rfl⟩

/-- Dropping the zero row keeps the kernel. -/
example (v : Fin 1 → ℚ) : M₀.submatrix r₀ id *ᵥ v = 0 ↔ M₀ *ᵥ v = 0 :=
  Matrix.submatrix_mulVec_eq_zero_iff_of_ne_zero_mem_range _ _ hr₀ v

/-- Dropping the zero row keeps the rank. -/
example : (M₀.submatrix r₀ id).rank = M₀.rank :=
  Matrix.rank_submatrix_eq_of_ne_zero_mem_range _ _ hr₀

/-- The covering hypothesis is needed: restricting `!![1]` to no rows puts `![1]` in the kernel. -/
example : ¬ ∀ v : Fin 1 → ℚ,
    ((!![1] : Matrix (Fin 1) (Fin 1) ℚ).submatrix (Fin.elim0 : Fin 0 → Fin 1) id *ᵥ v = 0 ↔
      (!![1] : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ v = 0) := by
  intro h
  have := congrFun ((h ![1]).mp (funext fun i => Fin.elim0 i)) 0
  simp [Matrix.mulVec, dotProduct] at this

end SupportedRowsTest
