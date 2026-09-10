/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.IsolatedRoot
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.ComputablePool
/-!
# The computed family captures simple isolated roots

The square-capture lemma selects independent agreement/tail rows at the wanted message's jet.
Its nonzero Jacobian determinant supplies simplicity. The elementary polynomial-neighborhood
criterion then proves isolation over arbitrary field extensions. Thus the literal computed
family has exactly the isolated-root coverage needed by the sparse solver's input contract.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems
open PolynomialDifferential CPoly CPoly.CMvPolynomial
universe u v
variable {F : Type u} [Field F] [DecidableEq F] {r : ℕ}

/-- Every qualifying regular message is a simple isolated zero of one emitted square system.
The last conjunct supplies an affine basic-open neighborhood containing no other common zero;
it does not require the rest of the system's zero locus to be finite. -/
theorem squareSystemsFromEquation_simple_isolated (center : F) (Q : CMvPolynomial (r + 2) F)
    (K k n A τ : ℕ) (hK : r < K) (hk : k ≤ K) (hkA : k ≤ A)
    -- τ covers the individual coefficient denominators; choosing τ=2K matches the paper.
    (hτ : TaylorExponentSufficient r K τ)
    (domain : Fin n ↪ F) (received : Fin n → F) (agreementPositions : Fin A ↪ Fin n)
    (P : Polynomial F) (hsolution : differentialSpecialization (semanticEquation Q) P = 0)
    (hseparant : jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
      (polynomialJet center P) ≠ 0)
    -- Each higher Hasse-coefficient recurrence uses this binomial pivot.
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hdegree : P.degree < k)
    (hagreement : ∀ i, P.eval (domain (agreementPositions i)) =
      received (agreementPositions i)) :
    ∃ rows ∈ squareSystemsFromEquation center Q K τ k n hk domain received,
      (∀ i, MvPolynomial.aeval (polynomialJet center P) (fromCMvPolynomial (rows i)) = 0) ∧
      (formalJacobian (polynomialJet center P)
        (fun i => fromCMvPolynomial (rows i))).det ≠ 0 ∧
      MvPolynomial.HasIsolatingPolynomial.{v, u}
        (fun i => fromCMvPolynomial (rows i)) (polynomialJet center P) := by
  obtain ⟨rows, hmem, hroot, hdet⟩ := squareSystemsFromEquation_covers center Q K k n A τ
    hK hk hkA hτ domain received agreementPositions P hsolution hseparant hbinomial
    hdegree hagreement
  refine ⟨rows, hmem, hroot, hdet, ?_⟩
  apply MvPolynomial.hasIsolatingPolynomial_of_jacobian_det_ne_zero
  · intro i
    exact hroot i
  · exact hdet
end ReedSolomon.HiddenDerivative.SquareSystems
