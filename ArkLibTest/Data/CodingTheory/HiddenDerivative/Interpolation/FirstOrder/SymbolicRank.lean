/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank

/-!
# First-order local constraint rank acceptance tests

The tests check the rank bound for a concrete non-line received polynomial at `D = 0`.
-/

open PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative

private def boundaryColumns : Fin 2 → SourceColumn 1 := fun j =>
  if j = 0 then ⟨0, 0, fun _ => 0⟩ else ⟨0, 1, fun _ => 0⟩

/-- The constant row has entry `1` in the constant column at `D = 0`. -/
example :
    localConstraintMatrix 1 (fun _ : Fin 1 ↦ Polynomial.C (0 : ℚ))
      (fun _ ↦ receivedLine 0 0) boundaryColumns
      (0, ⟨0, by simp [localContactOrder]⟩) 0 = 1 := by
  simp [localConstraintMatrix_apply, boundaryColumns, SourceColumn.polynomial,
    SourceColumn.exponent, unscaledLocalSubstitution]

/-- The two eligible columns at `D = 0` have a certified rank bound of `1`. -/
example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 ↦ Polynomial.C (0 : ℚ))
      (fun _ ↦ (X ^ 2 : ℚ[X])) boundaryColumns).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 := by
  have heligible : ∀ j, (boundaryColumns j).exponent ∈ firstOrderExponents 0 1 1 0 1 := by
    intro j
    rw [mem_firstOrderExponents_iff_coordinates]
    fin_cases j <;> simp [boundaryColumns, SourceColumn.exponent]
  exact (rank_firstOrderLocalConstraintMatrix_le (D := 0) (A := 1) (m := 1) (M := 0)
    (μ := 1) (centers := fun _ ↦ (0 : ℚ))
    (received := fun _ ↦ (X ^ 2 : ℚ[X])) boundaryColumns heligible).trans (by decide)
