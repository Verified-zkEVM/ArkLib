/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.InvertibleCombination
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank
import ArkLib.ToMathlib.LinearAlgebra.Matrix.SupportedRows
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic

/-!
# Acceptance tests for matrix recovery, rank, and row restriction
-/

open Module

/-- An invertible pair of linear combinations recovers a vector in the kernel of a projection. -/
example : ((0, 1) : ℚ × ℚ) ∈ LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
  let A : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, -1]
  have hA : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_fin_two_of]
    norm_num [A]
  have hx : ∀ i : Fin 2, ∑ j, A i j • ((0, 1) : ℚ × ℚ) ∈
      LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
    intro i
    fin_cases i <;> simp [A, Fin.sum_univ_two]
  exact Submodule.mem_of_forall_sum_smul_mem A hA hx 1

/-- Values at the distinct nodes `0` and `1` recover the second coefficient. -/
example : ((0, 2) : ℚ × ℚ) ∈ LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
  let α : Fin 2 → ℚ := fun i ↦ (i : ℚ)
  let x : Fin 2 → ℚ × ℚ := ![(0, 1), (0, 2)]
  have hα : Function.Injective α := by
    intro i j hij
    apply Fin.ext
    change (i : ℚ) = (j : ℚ) at hij
    exact_mod_cast hij
  have hx : ∀ i : Fin 2, ∑ j : Fin 2, α i ^ (j : ℕ) • x j ∈
      LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
    intro i
    fin_cases i <;> norm_num [α, x, Fin.sum_univ_two, LinearMap.mem_ker]
  exact Submodule.mem_of_forall_sum_pow_smul_mem hα hx 1

/-- The identity on `Fin 2 → ℚ` has coordinate matrix of rank `2`. -/
example : (Matrix.of fun i j => (LinearMap.id : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ))
    (Pi.basisFun ℚ (Fin 2) j) i).rank = 2 := by
  rw [Matrix.rank_of_basis, LinearMap.range_id, finrank_top, Module.finrank_fin_fun]

open scoped Matrix

/-- Mapping a nonzero diagonal matrix from `ℚ` to `ℝ` does not increase its rank. -/
example :
    ((!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ)).rank ≤
      (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℚ).rank :=
  Matrix.rank_map_le (Rat.castHom ℝ) _

namespace SupportedRowsTest

/-- Every nonzero row is a multiple of `(1, 1)`, with a zero row between them. -/
def M₀ : Matrix (Fin 3) (Fin 2) ℚ := !![1, 1; 0, 0; 2, 2]

/-- The selected rows cover every nonzero entry. -/
def r₀ : Fin 2 → Fin 3 := ![0, 2]

theorem hr₀ : ∀ i j, M₀ i j ≠ 0 → i ∈ Set.range r₀ := by
  intro i j h
  fin_cases i
  · exact ⟨0, rfl⟩
  · fin_cases j <;> simp [M₀] at h
  · exact ⟨1, rfl⟩

/-- Restricting to the selected rows preserves a nonzero vector in the kernel. -/
example : ![1, -1] ≠ (0 : Fin 2 → ℚ) ∧ M₀ *ᵥ ![1, -1] = 0 ∧
    M₀.submatrix r₀ id *ᵥ ![1, -1] = 0 ∧
      (M₀.submatrix r₀ id *ᵥ ![1, -1] = 0 ↔ M₀ *ᵥ ![1, -1] = 0) := by
  refine ⟨by norm_num, ?_, ?_,
    Matrix.submatrix_mulVec_eq_zero_iff_of_ne_zero_mem_range M₀ r₀ hr₀ ![1, -1]⟩
  · ext i
    fin_cases i <;> norm_num [M₀, Matrix.mulVec, Fin.sum_univ_two]
  · ext i
    fin_cases i <;> norm_num [M₀, r₀, Matrix.submatrix, Matrix.mulVec, Fin.sum_univ_two]

/-- Restricting to the selected rows preserves the rank. -/
example : (M₀.submatrix r₀ id).rank = M₀.rank :=
  Matrix.rank_submatrix_eq_of_ne_zero_mem_range M₀ r₀ hr₀

end SupportedRowsTest

namespace ProductRowRankTest

/-- A matrix with two independent rows, split into two one-row blocks and three columns. -/
private def productRowsMatrix : Matrix (Fin 2 × Fin 1) (Fin 3) ℚ :=
  fun row column => if row.1.val = column.val then 1 else 0

/-- Two one-rank row blocks bound the rank of a three-column matrix by two. -/
example : productRowsMatrix.rank = 2 ∧
    (∑ i : Fin 2, Matrix.rank (fun row column => productRowsMatrix (i, row) column)) = 2 ∧
    Fintype.card (Fin 3) >
      ∑ i : Fin 2, Matrix.rank (fun row column => productRowsMatrix (i, row) column) ∧
    productRowsMatrix.rank ≤
      ∑ i : Fin 2, Matrix.rank (fun row column => productRowsMatrix (i, row) column) := by
  have hblock : ∀ i : Fin 2,
      Matrix.rank (fun row column => productRowsMatrix (i, row) column) = 1 := by
    intro i
    let block : Matrix (Fin 1) (Fin 3) ℚ :=
      fun row column => productRowsMatrix (i, row) column
    have hupper : block.rank ≤ 1 := by
      simpa using (Matrix.rank_le_card_height block)
    let r : Fin 1 → Fin 1 := fun _ => 0
    let c : Fin 1 → Fin 3 := fun _ => ⟨i.val, by omega⟩
    have hminor : block.submatrix r c = 1 := by
      ext row column
      fin_cases row
      fin_cases column
      simp [Matrix.submatrix, block, productRowsMatrix, r, c]
    have hlower : 1 ≤ block.rank := by
      have hminorRank : (block.submatrix r c).rank = 1 := by
        rw [hminor, Matrix.rank_one]
        simp
      calc
        1 = (block.submatrix r c).rank := hminorRank.symm
        _ ≤ block.rank := Matrix.rank_submatrix_le block r c
    exact Nat.le_antisymm hupper hlower
  have hupper : productRowsMatrix.rank ≤ 2 := by
    simpa using (Matrix.rank_le_card_height productRowsMatrix)
  let r : Fin 2 → Fin 2 × Fin 1 := fun i => (i, 0)
  let c : Fin 2 → Fin 3 := fun i => ⟨i.val, by omega⟩
  have hminor : productRowsMatrix.submatrix r c = 1 := by
    ext row column
    rw [Matrix.submatrix_apply]
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.one_apply, productRowsMatrix, r, c]
  have hlower : 2 ≤ productRowsMatrix.rank := by
    have hminorRank : (productRowsMatrix.submatrix r c).rank = 2 := by
      rw [hminor, Matrix.rank_one]
      simp
    calc
      2 = (productRowsMatrix.submatrix r c).rank := hminorRank.symm
      _ ≤ productRowsMatrix.rank := Matrix.rank_submatrix_le productRowsMatrix r c
  have hmatrix : productRowsMatrix.rank = 2 := Nat.le_antisymm hupper hlower
  have hsum :
      (∑ i : Fin 2, Matrix.rank (fun row column => productRowsMatrix (i, row) column)) = 2 := by
    simp [hblock]
  refine ⟨hmatrix, hsum, ?_, Matrix.rank_prod_rows_le_sum productRowsMatrix⟩
  rw [hsum]
  simp

end ProductRowRankTest
