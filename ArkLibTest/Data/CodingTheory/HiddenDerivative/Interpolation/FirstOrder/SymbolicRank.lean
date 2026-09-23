/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.SymbolicRank

/-!
# First-order symbolic rank acceptance tests

The tests check a small received-line matrix at `D = 0`, the source-shaped rank bound with
`1 < D`, and coefficient change for the local constraint map over `ℤ → ℚ`.
-/

open PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative

private def constantColumn : Fin 1 → SourceColumn 1 := fun _ =>
  ⟨0, 0, fun _ => 0⟩

/-- Even at the boundary `D = 0`, the constant received-line matrix has the certified rank bound. -/
example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 ↦ Polynomial.C (0 : ℚ))
      (fun _ ↦ receivedLine 0 0) constantColumn).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ certifiedEnlargedRankBound 1 1 0 0 := by
  have heligible : ∀ j, (constantColumn j).exponent ∈ firstOrderExponents 0 1 1 0 0 := by
    intro j
    simp [FirstOrderEligibleExponent, constantColumn, SourceColumn.exponent, firstJetExponent,
      totalJetDegree]
  apply (rank_firstOrderLocalConstraintMatrix_le (D := 0) (A := 1) (m := 1) (M := 0)
    (μ := 0) (centers := fun _ ↦ (0 : ℚ)) (f := fun _ ↦ 0) (g := fun _ ↦ 0)
    constantColumn heligible).trans
  simp

/-- The form with the hypothesis `1 < D` follows from the rank bound, which applies to every D. -/
example {F : Type*} [Field F] {D A m M μ n N : ℕ} (_hD : 1 < D)
    (centers f g : Fin n → F) (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ) :
    ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i))
      (fun i ↦ receivedLine (f i) (g i)) columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤ n * certifiedEnlargedRankBound 1 m M 0 := by
  simpa using rank_firstOrderLocalConstraintMatrix_le centers f g columns heligible
