/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorCuts
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorDegree
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.SolutionGeometry


/-!
# Finite symbolic solution witnesses at a common center

The equation may depend on the challenge. Each indexed witness solves its own specialization;
only the expansion center is shared. The resulting points retain the challenge coordinate.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace MvPolynomial

variable {E σ : Type*} [Field E]

/-- Joint evaluation specializes the retained challenge and then evaluates the jet. -/
theorem aeval_flattenChallenge (z : E) (jet : σ → E)
    (p : MvPolynomial σ (Polynomial E)) :
    aeval (fun i ↦ i.elim z jet) (flattenChallenge p) =
      aeval jet (MvPolynomial.map (Polynomial.aeval z).toRingHom p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [flattenChallenge_C, ← Polynomial.aeval_algHom_apply]
      simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, flattenChallenge_X, aeval_X, map_X,
      Option.elim_some]

end MvPolynomial

namespace ReedSolomon.HiddenDerivative

open MvPolynomial
open scoped BigOperators

variable {E ι : Type*} [Field E] {r : ℕ}

/-- A symbolic equation at one challenge, with no assumption of challenge independence. -/
def challengeSpecialization (Q : DifferentialPolynomial (Polynomial E) r) (z : E) :
    DifferentialPolynomial E r := MvPolynomial.map (Polynomial.aeval z).toRingHom Q

/-- The actual challenge and initial jet of an indexed polynomial witness. -/
def symbolicWitnessPoint (center z : E) (P : Polynomial E) : Option (Fin (r + 1)) → E :=
  fun i ↦ i.elim z (polynomialJet center P)

/-- Finitely many nonzero separant polynomials, even for different equations, have one
common regular center. -/
theorem exists_common_symbolicWitness_center [Infinite E]
    (Q : DifferentialPolynomial (Polynomial E) r) (S : Finset ι)
    (z : ι → E) (P : ι → Polynomial E)
    (hsep : ∀ i ∈ S, differentialSpecialization
      (separant (challengeSpecialization Q (z i)) (Fin.last r)) (P i) ≠ 0) :
    ∃ center : E, ∀ i ∈ S,
      jetEvaluation (separant (challengeSpecialization Q (z i)) (Fin.last r))
        center (polynomialJet center (P i)) ≠ 0 := by
  classical
  let R := ∏ i ∈ S, differentialSpecialization
    (separant (challengeSpecialization Q (z i)) (Fin.last r)) (P i)
  have hR : R ≠ 0 := Finset.prod_ne_zero_iff.mpr hsep
  have hex : ∃ center : E, R.eval center ≠ 0 := by
    by_contra! h
    apply hR
    apply Polynomial.funext
    simpa using h
  obtain ⟨center, hc⟩ := hex
  refine ⟨center, ?_⟩
  have hc' : ∀ i ∈ S, (differentialSpecialization
      (separant (challengeSpecialization Q (z i)) (Fin.last r)) (P i)).eval center ≠ 0 := by
    simpa only [R, Polynomial.eval_prod, Finset.prod_ne_zero_iff] using hc
  intro i hi
  rw [← eval_differentialSpecialization]
  exact hc' i hi

/-- At a regular center every actual solution satisfies the joint chart equations. High
cuts use only the additional degree bound; agreement cuts retain the affine challenge value. -/
theorem symbolicWitnessPoint_equations
    (Q : DifferentialPolynomial (Polynomial E) r) (center z : E) (P : Polynomial E)
    (K : ℕ) (hdegree : P.degree < K)
    (hsol : differentialSpecialization (challengeSpecialization Q z) P = 0)
    (hsep : jetEvaluation (separant (challengeSpecialization Q z) (Fin.last r))
      center (polynomialJet center P) ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    aeval (symbolicWitnessPoint center z P)
      (flattenChallenge (initialJetEquationOver (Polynomial.C center) Q)) = 0 ∧
    aeval (symbolicWitnessPoint center z P)
      (flattenChallenge (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 ∧
    (∀ k : ℕ, P.degree < k → ∀ l : Fin K, k ≤ l.val →
      aeval (symbolicWitnessPoint center z P)
        (flattenChallenge (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l)) =
          0) ∧
    (∀ x f g : E,
      aeval (symbolicWitnessPoint center z P)
        (flattenChallenge (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
          (Polynomial.C x) (Polynomial.C f + Polynomial.X * Polynomial.C g))) = 0 ↔
        P.eval x = f + z * g) := by
  unfold symbolicWitnessPoint
  simp only [aeval_flattenChallenge,
    map_initialJetEquationOver_eq, map_initialJetSeparantOver_eq,
    map_commonTaylorNumeratorOver_eq, map_taylorAgreementEquationOver_eq,
    map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self,
    RingHom.id_apply]
  change aeval (polynomialJet center P)
      (initialJetEquation center (challengeSpecialization Q z)) = 0 ∧ _
  refine ⟨initialJetEquation_solution _ _ _ hsol, ?_, ?_, ?_⟩
  · rwa [aeval_initialJetSeparant]
  · intro k hk l hl
    change aeval (polynomialJet center P)
      (commonTaylorNumerator center (challengeSpecialization Q z) K l) = 0
    rw [commonTaylorNumerator_solution center _ P hsol hsep K hbin]
    have hc : (Polynomial.taylor center P).coeff l.val = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      simpa only [Polynomial.degree_taylor] using hk.trans_le (Nat.cast_le.mpr hl)
    rw [hc, mul_zero]
  · intro x f g
    exact polynomialJet_agreement_cut_iff center _ K P hdegree hsol hsep hbin x (f + z * g)

/-- A finite indexed family of symbolic witnesses embeds at one common regular center.
Indices need not be unique challenges or unique polynomials. -/
theorem exists_symbolicWitness_embedding [Infinite E]
    (Q : DifferentialPolynomial (Polynomial E) r) (S : Finset ι)
    (z : ι → E) (P : ι → Polynomial E) (K : ℕ)
    (hdegree : ∀ i ∈ S, (P i).degree < K)
    (hsol : ∀ i ∈ S, differentialSpecialization (challengeSpecialization Q (z i)) (P i) = 0)
    (hsep : ∀ i ∈ S, differentialSpecialization
      (separant (challengeSpecialization Q (z i)) (Fin.last r)) (P i) ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ center : E, ∀ i ∈ S,
      aeval (symbolicWitnessPoint center (z i) (P i))
        (flattenChallenge (initialJetEquationOver (Polynomial.C center) Q)) = 0 ∧
      aeval (symbolicWitnessPoint center (z i) (P i))
        (flattenChallenge (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 ∧
      (∀ k : ℕ, (P i).degree < k → ∀ l : Fin K, k ≤ l.val →
        aeval (symbolicWitnessPoint center (z i) (P i))
          (flattenChallenge (commonTaylorNumeratorOver (F := E)
            (Polynomial.C center) Q K l)) = 0) ∧
      (∀ x f g : E,
        aeval (symbolicWitnessPoint center (z i) (P i))
          (flattenChallenge (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
            (Polynomial.C x) (Polynomial.C f + Polynomial.X * Polynomial.C g))) = 0 ↔
          (P i).eval x = f + z i * g) := by
  obtain ⟨center, hc⟩ := exists_common_symbolicWitness_center Q S z P hsep
  exact ⟨center, fun i hi ↦ symbolicWitnessPoint_equations Q center (z i) (P i) K
    (hdegree i hi) (hsol i hi) (hc i hi) hbin⟩

/-- At any regular joint witness point, reconstruction recovers the actual polynomial.
In particular the nonvanishing conclusion of `exists_symbolicWitness_embedding` supplies
the regularity premise at its chosen common center. -/
theorem symbolicWitnessPoint_reconstruction
    (Q : DifferentialPolynomial (Polynomial E) r) (center z : E) (P : Polynomial E)
    (K : ℕ) (hdegree : P.degree < K)
    (hsol : differentialSpecialization (challengeSpecialization Q z) P = 0)
    (hsep : aeval (symbolicWitnessPoint center z P)
      (flattenChallenge (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    rationalTaylorPolynomial center (challengeSpecialization Q z) K
      (polynomialJet center P) = P := by
  have hs : jetEvaluation (separant (challengeSpecialization Q z) (Fin.last r))
      center (polynomialJet center P) ≠ 0 := by
    unfold symbolicWitnessPoint at hsep
    simpa only [aeval_flattenChallenge,
      map_initialJetSeparantOver_eq, Polynomial.aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, aeval_initialJetSeparant, challengeSpecialization] using hsep
  apply Polynomial.taylor_injective center
  ext i
  rw [rationalTaylorPolynomial, coeff_taylor_centeredCoefficientPrefix]
  by_cases hi : i < K
  · rw [if_pos hi]
    exact congrFun (rationalTaylorMap_eq_solution center _ P hsol hs K hbin) ⟨i, hi⟩
  · rw [if_neg hi]
    symm
    apply Polynomial.coeff_eq_zero_of_degree_lt
    simpa only [Polynomial.degree_taylor] using
      hdegree.trans_le (Nat.cast_le.mpr (Nat.le_of_not_gt hi))

/-- Selecting one witness per distinct challenge gives distinct joint source points,
independently of any differential equation. -/
theorem symbolicWitnessPoint_injOn (center : E) (S : Set ι)
    (z : ι → E) (P : ι → Polynomial E) (hz : Set.InjOn z S) :
    Set.InjOn (fun i ↦ symbolicWitnessPoint (r := r) center (z i) (P i)) S := by
  intro i hi j hj hij
  exact hz hi hj (congrFun hij none)

end ReedSolomon.HiddenDerivative
