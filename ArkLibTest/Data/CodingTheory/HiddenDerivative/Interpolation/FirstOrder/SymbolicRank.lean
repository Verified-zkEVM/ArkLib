/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank

/-!
# First-order symbolic rank acceptance tests

The tests check the rank bound at `D = 0` and state the rank bound under `1 < D`.
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
      (fun _ ↦ receivedLine 0 0) boundaryColumns).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 := by
  have heligible : ∀ j, (boundaryColumns j).exponent ∈ firstOrderExponents 0 1 1 0 1 := by
    intro j
    rw [mem_firstOrderExponents_iff_coordinates]
    fin_cases j <;> simp [boundaryColumns, SourceColumn.exponent]
  exact (rank_firstOrderLocalConstraintMatrix_le (D := 0) (A := 1) (m := 1) (M := 0)
    (μ := 1) (centers := fun _ ↦ (0 : ℚ)) (f := fun _ ↦ 0) (g := fun _ ↦ 0)
    boundaryColumns heligible).trans (by decide)

/-- The form with the hypothesis `1 < D` follows from the rank bound, which applies to every D. -/
example {F : Type*} [Field F] {D A m M μ n N : ℕ} (_hD : 1 < D)
    (centers f g : Fin n → F) (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ) :
    ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i))
      (fun i ↦ receivedLine (f i) (g i)) columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤ n * certifiedEnlargedRankBound 1 m M 0 := by
  simpa using rank_firstOrderLocalConstraintMatrix_le centers f g columns heligible
