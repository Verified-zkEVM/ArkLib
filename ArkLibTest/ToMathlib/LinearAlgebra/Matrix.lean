/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.Determinant
import ArkLib.ToMathlib.LinearAlgebra.Matrix.InvertibleCombination
import ArkLib.ToMathlib.LinearAlgebra.Matrix.PrimitiveKernel
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank
import ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis
import ArkLib.ToMathlib.LinearAlgebra.Matrix.SupportedRows
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance cases for matrix recovery, rank, and row restriction
-/

open Module
open scoped Matrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

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

/-- Mapping a nonzero diagonal matrix from `ℚ` to `ℝ` does not increase its rank. -/
example :
    ((!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ)).rank ≤
      (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℚ).rank :=
  Matrix.rank_map_le (Rat.castHom ℝ) _

private def M₀ : Matrix (Fin 3) (Fin 2) ℚ := !![1, 1; 0, 0; 2, 2]

private def r₀ : Fin 2 → Fin 3 := ![0, 2]

private theorem hr₀ : ∀ i j, M₀ i j ≠ 0 → i ∈ Set.range r₀ := by
  intro i j h
  fin_cases i
  · exact ⟨0, rfl⟩
  · fin_cases j <;> simp [M₀] at h
  · exact ⟨1, rfl⟩

/-- Restricting the selected rows preserves the kernel and rank. -/
example :
    (M₀.submatrix r₀ id *ᵥ ![1, -1] = 0 ↔ M₀ *ᵥ ![1, -1] = 0) ∧
      (M₀.submatrix r₀ id).rank = M₀.rank := by
  exact ⟨Matrix.submatrix_mulVec_eq_zero_iff_of_ne_zero_mem_range M₀ r₀ hr₀ _,
    Matrix.rank_submatrix_eq_of_ne_zero_mem_range M₀ r₀ hr₀⟩

private def productRowsMatrix : Matrix (Fin 2 × Fin 1) (Fin 2) ℚ :=
  fun row column => if row.1 = column then 1 else 0

/-- Splitting a two-row matrix into singleton blocks bounds its rank by their rank sum. -/
example : productRowsMatrix.rank ≤
    ∑ i : Fin 2, Matrix.rank (fun row column => productRowsMatrix (i, row) column) :=
  Matrix.rank_prod_rows_le_sum productRowsMatrix

/-- A concrete nonzero kernel vector factors through a primitive one. -/
example : ∃ g : ℤ, ∃ u : Fin 2 → ℤ, g ≠ 0 ∧ ![1, 0] = g • u ∧
    u ≠ 0 ∧ (0 : Matrix (Fin 1) (Fin 2) ℤ) *ᵥ u = 0 ∧
      Ideal.span (Set.range u) = ⊤ := by
  exact (0 : Matrix (Fin 1) (Fin 2) ℤ).exists_primitive_kernel_vector_eq_smul
    (v := ![1, 0]) (by norm_num) (by simp)

/-- The unit ideal prevents this concrete vector from vanishing modulo `5`. -/
example : (fun j : Fin 2 => ((![2, 3] j : ℤ) : ZMod 5)) ≠ 0 := by
  have hgcd : Finset.univ.gcd ![(2 : ℤ), 3] = 1 := by decide
  exact Ideal.comp_ne_zero_of_span_range_eq_top
    (Ideal.span_range_eq_top_iff_univ_gcd_eq_one.mpr hgcd) (Int.castRingHom (ZMod 5))

private def rowBasisMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

/-- The identity matrix has a basis selected from its actual rows. -/
example : ∃ rows : Fin rowBasisMatrix.rank → Fin 2,
    LinearIndependent ℚ (fun i ↦ rowBasisMatrix.row (rows i)) ∧
      Submodule.span ℚ (Set.range fun i ↦ rowBasisMatrix.row (rows i)) =
        Submodule.span ℚ (Set.range rowBasisMatrix.row) :=
  rowBasisMatrix.exists_rows_linearIndependent_span_eq

private def rowBasisIntegerMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Selected rows of a concrete integer matrix preserve its right kernel. -/
example : ∃ rows : Fin (rowBasisIntegerMatrix.map (Int.castRingHom ℚ)).rank → Fin 2,
    ∀ v : Fin 2 → ℤ,
      rowBasisIntegerMatrix.submatrix rows id *ᵥ v = 0 ↔ rowBasisIntegerMatrix *ᵥ v = 0 :=
  rowBasisIntegerMatrix.exists_rows_submatrix_mulVec_eq_zero_iff
    (Int.castRingHom ℚ) Int.cast_injective

private def determinantMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 1]

/-- Divisibility of one whole column gives divisibility of the determinant. -/
example : 2 ∣ determinantMatrix.det := by
  have hcol : ∀ j ∈ ({0} : Finset (Fin 2)), ∀ i, (2 : ℤ) ∣ determinantMatrix i j := by
    intro j hj i
    have hj' : j = 0 := Finset.mem_singleton.mp hj
    subst j
    fin_cases i <;> norm_num [determinantMatrix]
  have hdiv := Matrix.pow_dvd_det_of_forall_mem_col_dvd determinantMatrix 2 {0} hcol
  simpa using hdiv
