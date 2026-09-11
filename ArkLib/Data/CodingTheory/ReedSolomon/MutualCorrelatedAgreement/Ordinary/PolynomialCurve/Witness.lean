/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Graph
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorWitnessEmbedding
/-!
# Actual solutions in sparse Frobenius power charts

Order-zero recurrence pivots are one.  Hence a regular pulled solution satisfies the source,
sparse, and arbitrary power-curve agreement equations in every characteristic.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

variable {E : Type*} [Field E] {ℓ : ℕ}

/-- A regular pulled solution satisfies every actual source and power-curve cut. -/
theorem symbolicFrobeniusPowerWitness_equations
    (Q : DifferentialPolynomial E[X] 0) (center z : E) (P : E[X])
    (p e K τ : ℕ) [ExpChar E p] (hτ : TaylorExponentSufficient 0 K τ)
    (hdegree : (expand E (p ^ e) P).degree < K)
    (hsol : differentialSpecialization (challengeSpecialization Q z)
      (expand E (p ^ e) P) = 0)
    (hsep : jetEvaluation (separant (challengeSpecialization Q z) (Fin.last 0))
      center (polynomialJet center (expand E (p ^ e) P)) ≠ 0) :
    aeval (symbolicWitnessPoint center z (expand E (p ^ e) P))
      (symbolicSourceInitialEquation center Q) = 0 ∧
    aeval (symbolicWitnessPoint center z (expand E (p ^ e) P))
      (symbolicSourceSeparant center Q) ≠ 0 ∧
    (∀ l : Fin K, ¬p ^ e ∣ l.val →
      aeval (symbolicWitnessPoint center z (expand E (p ^ e) P))
        (symbolicSourceNumerator center Q K l (τ := τ)) = 0) ∧
    ∀ alpha : E, ∀ values : Fin (ℓ + 1) → E,
      aeval (symbolicWitnessPoint center z (expand E (p ^ e) P))
        (symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e) alpha values) = 0 ↔
      P.eval (alpha ^ (p ^ e)) = ∑ t, z ^ (p ^ e * t.val) * values t := by
  have hbin : ∀ i, 0 < i → i < K → (i.choose 0 : E) ≠ 0 := by simp
  have hS : aeval (polynomialJet center (expand E (p ^ e) P))
      (initialJetSeparant center (challengeSpecialization Q z)) ≠ 0 := by
    rwa [aeval_initialJetSeparant]
  have hflatten (R : MvPolynomial (Fin 1) E[X]) :
      (optionEquivRight E (Fin 1)).symm R = flattenChallenge R := rfl
  unfold symbolicWitnessPoint symbolicSourceInitialEquation symbolicSourceSeparant
    symbolicSourceNumerator symbolicSourceFrobeniusPowerAgreement
  change aeval (fun i ↦ i.elim z (polynomialJet center (expand E (p ^ e) P)))
      (flattenChallenge (initialJetEquationOver (Polynomial.C center) Q)) = 0 ∧ _
  simp only [hflatten, aeval_flattenChallenge, map_initialJetEquationOver_eq,
    map_initialJetSeparantOver_eq, map_commonTaylorNumeratorOver_eq,
    map_taylorAgreementEquationOver_eq, Polynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨initialJetEquation_solution _ _ _ hsol, hS, ?_, ?_⟩
  · intro l hl
    change aeval (polynomialJet center (expand E (p ^ e) P))
      (commonTaylorNumerator center (challengeSpecialization Q z) K l (τ := τ)) = 0
    rw [commonTaylorNumerator_solution_of_exponent center _ _ hsol hsep K τ hτ hbin,
      coeff_taylor_expand_primePow_eq_zero p e P center l.val hl, mul_zero]
  · intro alpha values
    change aeval (polynomialJet center (expand E (p ^ e) P))
        (taylorAgreementEquation center (challengeSpecialization Q z) K alpha
          ((frobeniusPowerCoordinate (p ^ e) values).eval z) (τ := τ)) = 0 ↔ _
    rw [taylorAgreementEquation_solution_of_exponent center _ _ hsol hsep K τ hτ
      hdegree hbin, mul_eq_zero]
    simp only [pow_ne_zero τ hS, false_or, sub_eq_zero, expand_eval,
      frobeniusPowerCoordinate_eval]

/-- Order-zero reconstruction recovers the actual regular pulled polynomial. -/
theorem symbolicFrobeniusPowerWitness_reconstruction
    (Q : DifferentialPolynomial E[X] 0) (center z : E) (P : E[X])
    (p e K : ℕ) [ExpChar E p]
    (hdegree : (expand E (p ^ e) P).degree < K)
    (hsol : differentialSpecialization (challengeSpecialization Q z)
      (expand E (p ^ e) P) = 0)
    (hsep : aeval (symbolicWitnessPoint center z (expand E (p ^ e) P))
      (symbolicSourceSeparant center Q) ≠ 0) :
    rationalTaylorPolynomial center (challengeSpecialization Q z) K
      (polynomialJet center (expand E (p ^ e) P)) = expand E (p ^ e) P :=
  symbolicWitnessPoint_reconstruction Q center z _ K hdegree hsol hsep (by simp)

end ReedSolomon
