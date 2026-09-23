/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Interpolant
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Space
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank

/-!
# First-order interpolation acceptance cases

Concrete dimension, support, membership, and interpolant instances.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial Matrix

example : Module.finrank ℚ (firstOrderSpace ℚ 2 3 1 0 1) = 4 := by
  rw [finrank_firstOrderSpace_eq_firstOrderDimensionCount ℚ (by norm_num)]
  decide

example : firstOrderColumnSlotCount 2 3 1 0 1 1 = 7 := by
  rw [firstOrderColumnSlotCount_eq_heightSlotCount (D := 2) (A := 3) (m := 1) (M := 0)
    (μ := 1) (h := 1) (by omega)]
  decide

private def firstOrderBoundaryColumns : Fin 2 → SourceColumn 1 := fun j =>
  if j = 0 then ⟨0, 0, fun _ => 0⟩ else ⟨0, 1, fun _ => 0⟩

example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 ↦ Polynomial.C (0 : ℚ))
      (fun _ ↦ receivedLine 0 0) firstOrderBoundaryColumns).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 := by
  have heligible : ∀ j,
      (firstOrderBoundaryColumns j).exponent ∈ firstOrderExponents 0 1 1 0 1 := by
    intro j
    rw [mem_firstOrderExponents_iff_coordinates]
    fin_cases j <;> simp [firstOrderBoundaryColumns, SourceColumn.exponent]
  exact (rank_firstOrderLocalConstraintMatrix_le (D := 0) (A := 1) (m := 1) (M := 0)
    (μ := 1) (centers := fun _ ↦ (0 : ℚ)) (f := fun _ ↦ 0) (g := fun _ ↦ 0)
    firstOrderBoundaryColumns heligible).trans (by decide)

example : (firstOrderExponentSet 0 3 2 1 4).Finite :=
  firstOrderExponentSet_finite 0 3 2 1 4

example : Finsupp.single none 1 + Finsupp.single (some 0) 1 ∈
    firstOrderExponents 2 2 2 0 1 := by
  rw [mem_firstOrderExponents_iff_coordinates]
  simp

example : monomial (Finsupp.single (some 1) 1) (1 : ℚ) ∈ firstOrderSpace ℚ 2 2 1 1 1 := by
  rw [monomial_mem_firstOrderSpace, ← mem_firstOrderExponents,
    mem_firstOrderExponents_iff_coordinates]
  simp

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ firstOrderSpace ℚ 2 3 1 0 1 ∧
      ∀ _ : Fin 3, SatisfiesLocalConstraints 1 0 0 Q := by
  apply exists_nonzero_firstOrder_interpolant_of_dimensionCount (by norm_num)
    (fun _ : Fin 3 => (0 : ℚ)) (fun _ => 0)
  decide

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ firstOrderSpace ℚ 2 3 1 0 1 ∧
      (Polynomial.X - Polynomial.C (0 : ℚ)) ^ 1 ∣
        differentialSpecialization Q (0 : Polynomial ℚ) := by
  have hdim : Fintype.card (Fin 3) * certifiedEnlargedRankBound 1 1 0 0 <
      (firstOrderExponents 2 3 1 0 1).card := by
    rw [card_firstOrderExponents (by norm_num)]
    decide
  obtain ⟨Q, hQ0, hQspace, hdiv⟩ :=
    exists_nonzero_firstOrder_interpolant_X_sub_C_pow_dvd
      (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1)
      (fun _ : Fin 3 => (0 : ℚ)) (fun _ => 0) hdim
  exact ⟨Q, hQ0, hQspace, hdiv 0 0 (by simp)⟩
