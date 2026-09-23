/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.PartitionRank

/-!
# Symbolic interpolation acceptance tests

The derivative-order coordinate budget bounds a concrete low-contact coordinate matrix and its
one-point symbolic specialization.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial Matrix

namespace SymbolicPartitionRankTest

/-- The constant monomial over a field has derivative-order weight zero. -/
private noncomputable def constantPolynomial : DifferentialPolynomial ℚ 0 :=
  MvPolynomial.monomial (0 : JetVariable 0 →₀ ℕ) 1

/-- One constant polynomial at multiplicity one has local coordinate rank at most one. -/
example : Matrix.rank (fun row _ => localConstraintCoordinatesAt 1 (0 : ℚ) 0
    constantPolynomial row :
      Matrix (LowContactIndex 0 1) (Fin 1) ℚ) ≤ 1 := by
  have h := localConstraintCoordinates_rank_le_of_derivative_weight
    (m := 1) (W := 0) (center := (0 : ℚ)) (received := (0 : ℚ))
    (polynomials := fun _ : Fin 1 => constantPolynomial) (by
      intro j u hu
      have hu0 : u = 0 := by
        simpa [constantPolynomial] using MvPolynomial.support_monomial_subset hu
      subst u
      simp [fullDerivativeJetWeight])
  simpa [localDerivativeCoordinateBudget, contactThreshold,
    weightedHigherJetCount_of_le_one] using h

/-- The one-point supported symbolic matrix for the column `Y₀` has rank at most its local
coordinate budget. -/
example : ((supportedLocalConstraintMatrix 1
    (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
    (fun _ : Fin 1 => (0 : ℚ[X]))
    (fun _ : Fin 1 => (⟨0, 1, ![]⟩ : SourceColumn 0))).map
      (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 1 := by
  let columns : Fin 1 → SourceColumn 0 := fun _ => ⟨0, 1, ![]⟩
  have hweight : ∀ j, fullDerivativeJetWeight (columns j).exponent ≤ 0 := by
    intro j
    simp [columns, SourceColumn.exponent, fullDerivativeJetWeight,
      Finsupp.weight_single, jetDerivativeWeight]
  have h := rank_map_supportedLocalConstraintMatrix_le_of_derivative_weight
    (m := 1) (W := 0)
    (centers := fun _ : Fin 1 => (0 : ℚ))
    (received := fun _ : Fin 1 => (0 : ℚ[X])) columns hweight
  simpa [localDerivativeCoordinateBudget, contactThreshold,
    weightedHigherJetCount_of_le_one] using h

end SymbolicPartitionRankTest
