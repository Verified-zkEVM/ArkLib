/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RecursiveCounting
import Mathlib.Algebra.Field.ZMod
/-!
# Canaries for recursive separant counting

These examples distinguish the two sides of the separant partition.  For `Y₀² = 0`, the zero
polynomial is singular at the first stage and is transported to the `2Y₀ = 0` equation.  For
`Y₀ = 0`, the same polynomial is regular because the separant is the nonzero constant one.
Thus the examples reject swapping the regular and singular predicates or reversing the
descendant transport.
-/

namespace ReedSolomon.HiddenDerivative.RecursiveCountingCanary

open PolynomialDifferential

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def quadraticEquation : DifferentialPolynomial (ZMod 5) 0 :=
  MvPolynomial.X (some (0 : Fin 1)) ^ 2

private def zeroQuadraticSolution : BoundedSolution quadraticEquation 1 :=
  ⟨⟨0, by simp⟩, by simp [quadraticEquation, differentialSpecialization]⟩

/-- The zero solution of `Y₀² = 0` takes the singular branch and survives transport to the
first separant equation. -/
example :
    (regularSolutions quadraticEquation 0 1 {zeroQuadraticSolution}).card = 0 ∧
      (singularDescendants quadraticEquation 0 1 {zeroQuadraticSolution}).card = 1 := by
  classical
  have hspecialization :
      differentialSpecialization (separant quadraticEquation 0)
        zeroQuadraticSolution.polynomial = 0 := by
    simp [quadraticEquation, zeroQuadraticSolution, differentialSpecialization, separant,
      BoundedSolution.polynomial]
  constructor
  · simp [regularSolutions, hspecialization]
  · rw [card_singularDescendants]
    simp only [singularSolutions, Finset.filter_singleton]
    simp [hspecialization]

private def linearEquation : DifferentialPolynomial (ZMod 5) 0 :=
  MvPolynomial.X (some (0 : Fin 1))

private def zeroLinearSolution : BoundedSolution linearEquation 1 :=
  ⟨⟨0, by simp⟩, by simp [linearEquation, differentialSpecialization]⟩

/-- The zero solution of `Y₀ = 0` takes the regular branch, so no singular descendant remains.
This is the final contributing stage before the separant chain becomes terminal. -/
example :
    (regularSolutions linearEquation 0 1 {zeroLinearSolution}).card = 1 ∧
      (singularDescendants linearEquation 0 1 {zeroLinearSolution}).card = 0 := by
  classical
  have hspecialization :
      differentialSpecialization (separant linearEquation 0)
        zeroLinearSolution.polynomial ≠ 0 := by
    simp [linearEquation, differentialSpecialization, separant, BoundedSolution.polynomial]
  constructor
  · simp only [regularSolutions, Finset.filter_singleton]
    simp [hspecialization]
  · rw [card_singularDescendants]
    simp [singularSolutions, hspecialization]

end

end ReedSolomon.HiddenDerivative.RecursiveCountingCanary
