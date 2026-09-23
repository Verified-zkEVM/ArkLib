/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Symbolic
import Mathlib.Algebra.Field.ZMod

/-!
# First-order interpolation acceptance tests

These examples check a nonzero interpolant satisfying the local constraints, a numerical rank
bound, and the coefficient-height and support properties of assembled source columns.
-/

open PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative
open scoped BigOperators Matrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def constantSourceColumnsTwo : Fin 1 → SourceColumn 2 :=
  fun _ => ⟨0, 0, fun _ => 0⟩

private def constantSourceColumnsOne : Fin 1 → SourceColumn 1 :=
  fun _ => ⟨0, 0, fun _ => 0⟩

/-- The coefficient-height theorem applies to two derivative variables. -/
example :
    ∀ u, ((SourceColumn.interpolant constantSourceColumnsTwo
      (fun _ ↦ (1 : (ZMod 5)[X]))).coeff u).natDegree ≤ 0 := by
  exact SourceColumn.coeff_interpolant_natDegree_le constantSourceColumnsTwo
    (by intro i j _; exact Subsingleton.elim _ _) (fun _ ↦ (1 : (ZMod 5)[X]))
    (by intro j; norm_num)

/-- A constant source column assembles to a polynomial in the finite first-order support. -/
example :
    SourceColumn.interpolant constantSourceColumnsOne
      (fun _ ↦ (1 : (ZMod 5)[X])) ∈ firstOrderSpace (ZMod 5)[X] 1 1 1 0 0 := by
  apply interpolant_mem_firstOrderSpace
  · intro j
    rw [mem_firstOrderExponents_iff_coordinates]
    simp [constantSourceColumnsOne, SourceColumn.exponent]

/-- A nonzero multiple-root interpolant satisfies the one-point local constraint. -/
example :
    ∃ v : Fin (Fintype.card ↑(firstOrderExponents 1 2 1 0 0)) → (ZMod 5)[X],
      v ≠ 0 ∧
      SourceColumn.interpolant
        (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 0) (μ := 0)) v ≠ 0 ∧
      (firstOrderCurveGradedConstraintMatrix 1 2 1 0 0 1
        (fun _ ↦ (0 : ZMod 5)) (fun _ ↦ (0 : (ZMod 5)[X])) *ᵥ v) = 0 ∧
      ∀ _i : Fin 1, SatisfiesLocalConstraints 1 (Polynomial.C (0 : ZMod 5))
        (0 : (ZMod 5)[X])
        (SourceColumn.interpolant
          (firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 0) (μ := 0)) v) := by
  classical
  let columns := firstOrderColumns (D := 1) (A := 2) (m := 1) (M := 0) (μ := 0)
  let sourceX : SourceColumn 1 := ⟨1, 0, fun _ => 0⟩
  have hsourceX : sourceX.exponent ∈ firstOrderExponents 1 2 1 0 0 := by
    rw [mem_firstOrderExponents_iff_coordinates]
    simp [sourceX, SourceColumn.exponent]
  let indexX : Fin (Fintype.card ↑(firstOrderExponents 1 2 1 0 0)) :=
    Fintype.equivFin ↑(firstOrderExponents 1 2 1 0 0) ⟨sourceX.exponent, hsourceX⟩
  let v : Fin (Fintype.card ↑(firstOrderExponents 1 2 1 0 0)) → (ZMod 5)[X] :=
    fun j => if j = indexX then 1 else 0
  have hcolumn : columns indexX = sourceX := by
    apply SourceColumn.exponent_injective
    rw [firstOrderColumns_exponent]
    simp [indexX]
  have hv : v ≠ 0 := by
    intro hv
    have hvalue := congrFun hv indexX
    simp [v] at hvalue
  have hinterpolant : SourceColumn.interpolant columns v = sourceX.polynomial := by
    rw [SourceColumn.interpolant_eq_sum_smul]
    simp [v, hcolumn]
  have hnonzero : SourceColumn.interpolant columns v ≠ 0 := by
    intro hzero
    have hcolumns : Function.Injective columns := by
      simpa [columns] using
        (firstOrderColumns_injective (D := 1) (A := 2) (m := 1) (M := 0) (μ := 0))
    exact hv ((SourceColumn.interpolant_eq_zero_iff hcolumns).mp hzero)
  have hsatisfies : ∀ _i : Fin 1, SatisfiesLocalConstraints 1
      (Polynomial.C (0 : ZMod 5)) (0 : (ZMod 5)[X])
      (SourceColumn.interpolant columns v) := by
    intro _i
    rw [SatisfiesLocalConstraints, hinterpolant]
    apply MvPolynomial.ext
    intro e
    rw [SourceColumn.polynomial_eq_sourceMonomial]
    by_cases hlow : localContactOrder 1 e < 1
    · have hT : e (localT 1) ≠ 1 := by
        change e none ≠ 1
        rw [localContactOrder_one] at hlow
        simp only [localT, localE] at hlow
        omega
      simpa [sourceX] using
        (coeff_localConstraintAt_zero_sourceMonomial_eq_zero_of_T_degree_ne
          (R := (ZMod 5)[X]) 1 1 0 (fun _ : Fin 1 ↦ 0) e hT)
    · simp [localConstraintAt, hlow]
  have hkernel :
      (firstOrderCurveGradedConstraintMatrix 1 2 1 0 0 1
        (fun _ ↦ (0 : ZMod 5)) (fun _ ↦ (0 : (ZMod 5)[X])) *ᵥ v) = 0 :=
    (firstOrderCurveGradedConstraintMatrix_kernel_iff 1 2 1 0 0 1 (by decide)
      (fun _ ↦ (0 : ZMod 5)) (fun _ ↦ (0 : (ZMod 5)[X])) v).2 hsatisfies
  exact ⟨v, hv, hnonzero, hkernel, hsatisfies⟩

/-- The small origin rank profile is bounded by its numerical profile. -/
example : firstOrderOriginGradedRank (F := ZMod 5) 1 1 1 0 0 ≤ 1 := by
  simpa [firstOrderGradedRankBound, firstOrderGradedSourceCount] using
    firstOrderOriginGradedRank_le_bound (F := ZMod 5) 1 1 1 0 0
