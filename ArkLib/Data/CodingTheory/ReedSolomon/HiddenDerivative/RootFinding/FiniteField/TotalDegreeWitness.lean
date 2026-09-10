/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RecursiveCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RegularCounting


/-!
# First nonzero separant witnesses

A witness follows the deterministic highest-jet derivative chain, requiring the candidate to
solve every preceding equation. This extra invariant makes jets injective across different
stages, not just within one regular branch. No normalization or root-count assumption is used.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], first-nonzero separant witnesses in the differential root-counting
  proof.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} [Field F] {d D : ℕ}

/-- A regular witness at the first chain stage with nonzero specialized separant.
The singular constructor retains the equation at every preceding stage. -/
inductive ChainWitness : DifferentialPolynomial F d → F[X] → F → Prop where
  | regular {Q P a s} (highest : highestActiveJet Q = some s)
      (solves : differentialSpecialization Q P = 0)
      (nonzero : jetEvaluation (separant Q s) a (polynomialJet a P) ≠ 0) :
      ChainWitness Q P a
  | singular {Q P a s} (highest : highestActiveJet Q = some s)
      (solves : differentialSpecialization Q P = 0)
      (next : ChainWitness (separant Q s) P a) : ChainWitness Q P a

/-- Every witness candidate solves the original equation. -/
theorem ChainWitness.solves {Q : DifferentialPolynomial F d} {P : F[X]} {a : F}
    (h : ChainWitness Q P a) : differentialSpecialization Q P = 0 := by
  cases h <;> assumption

/-- The witness jet is a zero of the original equation. -/
theorem ChainWitness.evaluation_eq_zero {Q : DifferentialPolynomial F d} {P : F[X]} {a : F}
    (h : ChainWitness Q P a) : jetEvaluation Q a (polynomialJet a P) = 0 := by
  rw [← eval_differentialSpecialization, h.solves]
  simp

/-- First-nonzero witnesses sharing the ambient jet come from the same polynomial, even when
 their derivative-chain stages initially appear different. -/
theorem ChainWitness.polynomial_eq {Q : DifferentialPolynomial F d} {P P' : F[X]} {a : F}
    (h : ChainWitness Q P a) (h' : ChainWitness Q P' a)
    (hP : P.degree ≤ D) (hP' : P'.degree ≤ D) (hD : D < ringChar F)
    (hjet : polynomialJet (d := d) a P = polynomialJet a P') : P = P' := by
  induction h with
  | @regular Q P a s hs hsol hreg =>
      cases h' with
      | regular hs' hsol' hreg' =>
          exact eq_of_regular_solutions_of_degree_le_of_polynomialJet_eq_of_isHighestActiveJet
            Q s (isHighestActiveJet_of_highestActiveJet_eq_some hs) a P P' D
            ⟨by rw [← eval_differentialSpecialization, hsol]; simp, hreg⟩ hP hP' hD hsol hsol'
            (by simpa only [restrictJet_polynomialJet] using congrArg (restrictJet s) hjet)
      | singular hs' hsol' next =>
          have heq := Option.some.inj (hs.symm.trans hs')
          subst heq
          exact (hreg (hjet ▸ next.evaluation_eq_zero)).elim
  | @singular Q P a s hs hsol next ih =>
      cases h' with
      | regular hs' hsol' hreg' =>
          have heq := Option.some.inj (hs.symm.trans hs')
          subst heq
          exact (hreg' (hjet ▸ next.evaluation_eq_zero)).elim
      | singular hs' hsol' next' =>
          have heq := Option.some.inj (hs.symm.trans hs')
          subst heq
          exact ih next' hP hjet

/-- A nonzero specialized chain derivative covers every center outside its roots, and its
 degree obeys the original equation's generic separant budget. -/
theorem exists_chainWitness_polynomial (Q : DifferentialPolynomial F d)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q) (P : BoundedSolution Q D) :
    ∃ R : F[X], R ≠ 0 ∧
      R.natDegree ≤ differentialWeightedDegree D Q - (D - d) ∧
      ∀ a, R.eval a ≠ 0 → ChainWitness Q P.polynomial a := by
  let H := differentialWeightedDegree D Q - (D - d)
  let motive := fun current : DifferentialPolynomial F d ↦
    Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q → current ≠ 0 →
      IsBelowCharacteristic D current → differentialSpecialization current P.polynomial = 0 →
        ∃ R : F[X], R ≠ 0 ∧ R.natDegree ≤ H ∧
          ∀ a, R.eval a ≠ 0 → ChainWitness current P.polynomial a
  have recurse : ∀ current, motive current := by
    intro current
    apply (singularStep_wellFounded (F := F) (d := d)).induction current
    intro equation ih hreach hne hc hsol
    cases hs : highestActiveJet equation with
    | none =>
        exact (hne (eq_zero_of_boundedSolution_of_highestActiveJet_eq_none equation hs
          ⟨P.1, hsol⟩)).elim
    | some s =>
        by_cases hz : differentialSpecialization (separant equation s) P.polynomial = 0
        · have hstep := singularStep_separant equation s hs (hc.2 s)
          have hcontract := singularStep_preserves_contract hc hstep
          obtain ⟨R, hR, hdeg, hcover⟩ := ih (separant equation s) hstep
            (Relation.ReflTransGen.head hstep hreach) hcontract.1 hcontract.2 hz
          exact ⟨R, hR, hdeg, fun a ha => ChainWitness.singular hs hsol (hcover a ha)⟩
        · refine ⟨differentialSpecialization (separant equation s) P.polynomial, hz, ?_, ?_⟩
          · have hw := differentialWeightedDegree_le_of_reflTransGen_singularStep (D := D) hreach
            have hj : s.val ≤ d := Nat.le_of_lt_succ s.isLt
            have hb := natDegree_differentialSpecialization_separant_le_sub equation s P.polynomial
              (Polynomial.natDegree_le_of_degree_le P.degree_le)
            dsimp [H]
            omega
          · intro a ha
            exact ChainWitness.regular hs hsol (by rwa [← eval_differentialSpecialization])
  exact recurse Q Relation.ReflTransGen.refl hQ hchar P.equation

/-- Specialize only the distinguished X coordinate, leaving all jet variables formal. -/
def jetFiberHom (a : F) : DifferentialPolynomial F d →+* MvPolynomial (Fin (d + 1)) F :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun v => match v with
    | none => MvPolynomial.C a
    | some j => MvPolynomial.X j)

/-- Scalar evaluation after partial specialization is the original jet evaluation. -/
theorem eval_jetFiberHom (Q : DifferentialPolynomial F d) (a : F) (jet : Fin (d + 1) → F) :
    MvPolynomial.eval jet (jetFiberHom a Q) = jetEvaluation Q a jet := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [jetFiberHom, jetEvaluation]
  | add Q R hQ hR => simp [map_add, hQ, hR, jetEvaluation]
  | mul_X Q v hQ =>
      cases v <;> simp [map_mul, jetFiberHom, jetEvaluation] at hQ ⊢ <;> simp [hQ]

/-- Specializing X commutes with differentiation in a jet variable. -/
theorem jetFiberHom_separant (Q : DifferentialPolynomial F d) (a : F) (s : Fin (d + 1)) :
    jetFiberHom a (separant Q s) = MvPolynomial.pderiv s (jetFiberHom a Q) := by
  classical
  unfold separant
  induction Q using MvPolynomial.induction_on with
  | C c => simp [jetFiberHom]
  | add Q R hQ hR => simp only [map_add, hQ, hR]
  | mul_X Q v hQ =>
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul, hQ]
      cases v <;> simp [jetFiberHom, Pi.single_apply]

/-- An identically zero jet fiber has no regular witness anywhere along the derivative chain. -/
theorem ChainWitness.jetFiber_ne_zero {Q : DifferentialPolynomial F d} {P : F[X]} {a : F}
    (h : ChainWitness Q P a) : jetFiberHom a Q ≠ 0 := by
  induction h with
  | regular hs hsol hreg =>
      intro hz
      apply hreg
      rw [← eval_jetFiberHom, jetFiberHom_separant, hz, map_zero, map_zero]
  | singular hs hsol next ih =>
      intro hz
      apply ih
      rw [jetFiberHom_separant, hz, map_zero]

end
end ReedSolomon.HiddenDerivative
