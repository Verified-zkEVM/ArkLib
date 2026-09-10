/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.Iteration
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.DegreeBounds.SpecializationDegree
/-!
# Counting regular branches using unique Hasse jets

The iterated lifting theorem supplies the injectivity hypothesis in the finite witness count.
For a highest active jet and an ambient polynomial degree below the characteristic, distinct
solutions have distinct jets at every regular witness. The degree of the specialized separant
bounds the exceptional witness points. These two facts yield a regular-branch counting theorem
with only explicit degree, characteristic, and nonvanishing hypotheses.

Singular solutions require the separate separant recursion before this theorem applies.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F] {d D : ℕ}

/-- At a regular witness, the ambient jet determines a bounded solution uniquely when the
polynomial degree is below the characteristic. -/
theorem polynomialJet_injOn_regularWitness
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hs : IsHighestActiveJet Q s) (hD : D < ringChar F) (point : F) :
    Set.InjOn (fun solution : BoundedSolution Q D ↦
      polynomialJet (d := d) point solution.polynomial)
      {solution | IsRegularWitness s solution point} := by
  intro P hP P' _hP' hjet
  apply BoundedSolution.eq_of_polynomialJet_eq_of_isHighestActiveJet Q s hs point P P'
  · exact ⟨by
      rw [← eval_differentialSpecialization, P.equation]
      simp, hP⟩
  · exact hD
  · simpa only [restrictJet_polynomialJet] using congrArg (restrictJet s) hjet

/-- Regular-branch witness counting with jet injectivity discharged by iterated lifting.
`H` may be any bound for the equation's differential weighted degree. -/
theorem regularBranch_counting_pow_le [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (H Δ : ℕ)
    (hs : IsHighestActiveJet Q s) (hD : D < ringChar F)
    (hWeight : differentialWeightedDegree D Q ≤ H)
    (hDegree : jetDegree Q s ≤ Δ)
    (roots : Finset (BoundedSolution Q D))
    (hRegular : ∀ solution ∈ roots,
      differentialSpecialization (separant Q s) solution.polynomial ≠ 0) :
    (Nat.card F - H) * roots.card ≤ Nat.card F * Δ * Nat.card F ^ d := by
  apply boundedSolution_counting_pow_le Q s D H Δ roots hRegular
  · intro solution _hsolution
    exact (solution.natDegree_separant_le Q s).trans hWeight
  · intro point
    exact (polynomialJet_injOn_regularWitness Q s hs hD point).mono
      (fun _ hmem ↦ hmem.2)
  · exact hDegree

end

end ReedSolomon.HiddenDerivative
