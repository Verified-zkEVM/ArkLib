/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.SingularRecursion
import Mathlib.Algebra.Field.ZMod
/-!
# Canaries for singular differential-equation recursion

These examples exercise strict separant descent, regular-branch coverage, and the empty terminal
branch for a nonzero equation in `X`.
-/

namespace ReedSolomon
namespace HiddenDerivative
namespace SingularRecursionCanary

open PolynomialDifferential

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def quadraticJetEquation : DifferentialPolynomial (ZMod 5) 0 :=
  MvPolynomial.X (some (0 : Fin 1)) ^ 2

/-- One separant step strictly lowers the only active jet degree. -/
example : jetDegreeMeasure (separant quadraticJetEquation 0) <
    jetDegreeMeasure quadraticJetEquation := by
  apply jetDegreeMeasure_separant_lt
  · simp [DependsOnJet, jetDegree, quadraticJetEquation]
  · norm_num [jetDegree, quadraticJetEquation, ZMod.ringChar_zmod_n]

private def zeroQuadraticSolution : BoundedSolution quadraticJetEquation 1 :=
  ⟨⟨0, by simp⟩, by simp [quadraticJetEquation, differentialSpecialization]⟩

/-- The zero solution is initially singular because it also solves the first separant. -/
example : Nonempty (SingularBoundedSolution quadraticJetEquation 0 1) := by
  refine ⟨zeroQuadraticSolution, ?_⟩
  simp [quadraticJetEquation, separant, differentialSpecialization, zeroQuadraticSolution,
    BoundedSolution.polynomial]

/-- Recursion through that singular branch still reaches a regular leaf. -/
example : Nonempty
    (RegularRecursionLeaf quadraticJetEquation 1 zeroQuadraticSolution.polynomial) := by
  apply exists_regularRecursionLeaf quadraticJetEquation
  · simp [quadraticJetEquation]
  · constructor
    · norm_num [ZMod.ringChar_zmod_n]
    · intro j
      fin_cases j
      norm_num [jetDegree, quadraticJetEquation, ZMod.ringChar_zmod_n]

private def regularEquation : DifferentialPolynomial (ZMod 5) 0 :=
  MvPolynomial.X (some (0 : Fin 1))

private def zeroRegularSolution : BoundedSolution regularEquation 1 :=
  ⟨⟨0, by simp⟩, by simp [regularEquation]⟩

/-- The zero solution of `Y₀ = 0` reaches a regular recursion leaf. -/
example : Nonempty (RegularRecursionLeaf regularEquation 1 zeroRegularSolution.polynomial) := by
  apply exists_regularRecursionLeaf regularEquation
  · simp [regularEquation]
  · constructor
    · norm_num [ZMod.ringChar_zmod_n]
    · intro j
      fin_cases j
      norm_num [jetDegree, regularEquation, ZMod.ringChar_zmod_n]

private def terminalEquation : DifferentialPolynomial (ZMod 5) 0 :=
  MvPolynomial.X none

/-- A nonzero equation depending only on `X` has no bounded differential solution. -/
example : IsEmpty (BoundedSolution terminalEquation 1) := by
  apply isEmpty_boundedSolution_of_highestActiveJet_eq_none terminalEquation
  · simp [terminalEquation]
  · rw [highestActiveJet_eq_none_iff]
    intro j
    fin_cases j
    rw [DependsOnJet, jetDegree, terminalEquation, MvPolynomial.degreeOf_X]
    simp

end

end SingularRecursionCanary
end HiddenDerivative
end ReedSolomon
