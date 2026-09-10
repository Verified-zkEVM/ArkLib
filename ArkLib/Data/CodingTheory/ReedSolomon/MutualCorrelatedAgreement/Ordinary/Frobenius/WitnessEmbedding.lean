/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.Recognition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorWitnessEmbedding
/-!
# Actual solutions in sparse Frobenius charts

Order-zero recurrence pivots are all one. Thus every regular pulled polynomial solution
satisfies the actual sparse and agreement equations in every characteristic.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

variable {E : Type*} [Field E]

/-- The exact order-zero denominator schedule for a pulled degree bound. -/
theorem frobeniusTaylorExponentSufficient (D s : ℕ) :
    TaylorExponentSufficient 0 (D * s + 1) (2 * D * s - 1) := by
  intro l
  simp only [Nat.mul_assoc]
  omega

/-- Actual regular pulled solutions satisfy the source, sparse, and agreement cuts.
The agreement equation is expressed in the original challenge `w^(p^e)`. -/
theorem symbolicFrobeniusWitness_equations
    (Q : DifferentialPolynomial E[X] 0) (center w : E) (P : E[X])
    (p e K τ : ℕ) [ExpChar E p] (hτ : TaylorExponentSufficient 0 K τ)
    (hdegree : (expand E (p ^ e) P).degree < K)
    (hsol : differentialSpecialization (challengeSpecialization Q w)
      (expand E (p ^ e) P) = 0)
    (hsep : jetEvaluation (separant (challengeSpecialization Q w) (Fin.last 0))
      center (polynomialJet center (expand E (p ^ e) P)) ≠ 0) :
    aeval (symbolicWitnessPoint center w (expand E (p ^ e) P))
      (symbolicSourceInitialEquation center Q) = 0 ∧
    aeval (symbolicWitnessPoint center w (expand E (p ^ e) P))
      (symbolicSourceSeparant center Q) ≠ 0 ∧
    (∀ l : Fin K, ¬p ^ e ∣ l.val →
      aeval (symbolicWitnessPoint center w (expand E (p ^ e) P))
        (symbolicSourceNumerator center Q K l (τ := τ)) = 0) ∧
    ∀ alpha u v : E,
      aeval (symbolicWitnessPoint center w (expand E (p ^ e) P))
        (symbolicSourceFrobeniusAgreement center Q K τ (p ^ e) alpha u v) = 0 ↔
      P.eval (alpha ^ (p ^ e)) = u + w ^ (p ^ e) * v := by
  have hbin : ∀ i, 0 < i → i < K → (i.choose 0 : E) ≠ 0 := by simp
  have hS : aeval (polynomialJet center (expand E (p ^ e) P))
      (initialJetSeparant center (challengeSpecialization Q w)) ≠ 0 := by
    rwa [aeval_initialJetSeparant]
  have hflatten (R : MvPolynomial (Fin 1) E[X]) :
      (optionEquivRight E (Fin 1)).symm R = flattenChallenge R := rfl
  unfold symbolicWitnessPoint symbolicSourceInitialEquation symbolicSourceSeparant
    symbolicSourceNumerator symbolicSourceFrobeniusAgreement
  change aeval (fun i ↦ i.elim w (polynomialJet center (expand E (p ^ e) P)))
      (flattenChallenge (initialJetEquationOver (Polynomial.C center) Q)) = 0 ∧ _
  simp only [hflatten, aeval_flattenChallenge, map_initialJetEquationOver_eq,
    map_initialJetSeparantOver_eq, map_commonTaylorNumeratorOver_eq,
    map_taylorAgreementEquationOver_eq, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨initialJetEquation_solution _ _ _ hsol, hS, ?_, ?_⟩
  · intro l hl
    change aeval (polynomialJet center (expand E (p ^ e) P))
      (commonTaylorNumerator center (challengeSpecialization Q w) K l (τ := τ)) = 0
    rw [commonTaylorNumerator_solution_of_exponent center _ _ hsol hsep K τ hτ hbin,
      coeff_taylor_expand_primePow_eq_zero p e P center l.val hl, mul_zero]
  · intro alpha u v
    change aeval (polynomialJet center (expand E (p ^ e) P))
        (taylorAgreementEquation center (challengeSpecialization Q w) K alpha
          (u + w ^ (p ^ e) * v) (τ := τ)) = 0 ↔ _
    rw [taylorAgreementEquation_solution_of_exponent center _ _ hsol hsep K τ hτ
      hdegree hbin, mul_eq_zero]
    simp only [pow_ne_zero τ hS, false_or, sub_eq_zero, expand_eval]

/-- Order-zero reconstruction recovers an actual regular pulled solution without any
characteristic cutoff on its degree. -/
theorem symbolicFrobeniusWitness_reconstruction
    (Q : DifferentialPolynomial E[X] 0) (center w : E) (P : E[X])
    (p e K : ℕ) [ExpChar E p]
    (hdegree : (expand E (p ^ e) P).degree < K)
    (hsol : differentialSpecialization (challengeSpecialization Q w)
      (expand E (p ^ e) P) = 0)
    (hsep : aeval (symbolicWitnessPoint center w (expand E (p ^ e) P))
      (symbolicSourceSeparant center Q) ≠ 0) :
    rationalTaylorPolynomial center (challengeSpecialization Q w) K
      (polynomialJet center (expand E (p ^ e) P)) = expand E (p ^ e) P :=
  symbolicWitnessPoint_reconstruction Q center w _ K hdegree hsol hsep (by simp)

end ReedSolomon
