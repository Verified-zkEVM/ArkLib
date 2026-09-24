/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Flattening
import Mathlib.Data.Rat.Defs

/-!
# Acceptance tests for first-order squarefree challenge flattening

Concrete first-order equations check nonvanishing and the challenge, derivative-variable, and
jet-degree bounds after flattening.
-/

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential

noncomputable section

private abbrev challengeEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  MvPolynomial.C (Polynomial.X : Polynomial ℚ) * X (some 1)

private theorem challengeEquation_height : CoeffNatDegreeLE challengeEquation 1 := by
  change CoeffNatDegreeLE
    (MvPolynomial.C (Polynomial.X : Polynomial ℚ) * X (some 1)) 1
  exact (coeffNatDegreeLE_C (p := (Polynomial.X : Polynomial ℚ)) (by simp)).mul
    (coeffNatDegreeLE_X (some 1))

example : flattenFirstOrderChallenge challengeEquation ≠ 0 := by
  rw [flattenFirstOrderChallenge_ne_zero_iff]
  simp [challengeEquation]

example : degreeOf none (flattenFirstOrderChallenge challengeEquation) ≤ 1 :=
  flattenFirstOrderChallenge_challengeDegree_le challengeEquation challengeEquation_height

example :
    degreeOf (some (some (1 : Fin 2))) (flattenFirstOrderChallenge challengeEquation) ≤ 1 := by
  calc
    _ ≤ degreeOf (some (1 : Fin 2)) challengeEquation :=
      flattenFirstOrderChallenge_yOneDegree_le challengeEquation
    _ ≤ 1 := by
      rw [challengeEquation]
      exact (degreeOf_mul_le (some 1) (MvPolynomial.C Polynomial.X)
        (X (some 1))).trans (by simp)

example :
    (flattenFirstOrderChallenge challengeEquation).weightedTotalDegree
        (liftedSourceWeight (fun v : JetVariable 1 ↦ v.elim 0 fun _ ↦ 1)) ≤ 1 := by
  apply (flattenFirstOrderChallenge_jetWeight_le challengeEquation).trans
  change challengeEquation.weightedTotalDegree jetDegreeWeight ≤ 1
  rw [challengeEquation]
  calc
    _ ≤ (MvPolynomial.C Polynomial.X).weightedTotalDegree jetDegreeWeight +
        (X (some 1) : DifferentialPolynomial (Polynomial ℚ) 1).weightedTotalDegree
          jetDegreeWeight := weightedTotalDegree_mul_le _ _ _
    _ = 1 := by
      rw [weightedTotalDegree_C, zero_add]
      rw [show (X (some 1) : DifferentialPolynomial (Polynomial ℚ) 1) =
          monomial (Finsupp.single (some 1) 1) 1 by rfl,
        weightedTotalDegree_monomial _ _ _ (by simp)]
      simp [Finsupp.weight_single, jetDegreeWeight]

end

end ReedSolomon.FirstOrder.Squarefree
