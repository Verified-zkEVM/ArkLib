/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition

/-!
# Polynomial graphs of power-batched Taylor components

A common sample determines a tuple of base-field polynomials. A positive-dimensional prime
component satisfying the joint Taylor cuts lies on its power-batched initial-jet graph. Its
ideal vanishes after graph restriction, and its separant stays nonzero on the graph.

## Main statements

* ReedSolomon.exists_polynomialGraph_of_primeTaylorComponent: recognition of a prime component
  and its graph identities for a tuple of arbitrary length.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

noncomputable section

variable {F E : Type*} [Field F] [Field E] {n k K r ℓ : ℕ}

/-- The polynomial map from the challenge line to the joint challenge and initial-jet
coordinates of a power-batched message tuple. -/
def powerBatchedJetGraphMap (center : E) (P : Fin (ℓ + 1) → E[X]) :
    Option (Fin (r + 1)) → E[X] :=
  fun i ↦ i.elim Polynomial.X (powerBatchedJetGraph (r := r) center P)

/-- A positive-dimensional prime component containing the high Taylor cuts and sample
agreement cuts lies on the graph of one base-field message tuple. Its ideal vanishes on that
graph, and the separant remains nonzero after restriction. -/
theorem exists_polynomialGraph_of_primeTaylorComponent [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k) (φ : F →+* E) (center : E)
    (Q : DifferentialPolynomial E[X] r) (hK : r < K) (τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) [I.IsPrime]
    (hsep : jointInitialJetSeparant center Q ∉ I)
    (hdim : 0 < (affineHilbertPolynomial I).natDegree)
    (hhigh : ∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ I)
    (hcuts : ∀ i ∈ sample,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (φ (domain i)))
        (powerBatchedCoordinate (fun t ↦ φ (w t i))) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = w t i) ∧
      (∀ x ∈ {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0},
        x = fun i ↦ (powerBatchedJetGraphMap (r := r) center
          (fun t ↦ (P t).map φ) i).eval (x none)) ∧
      (∀ x ∈ {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0},
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
          K (fun j ↦ x (some j)) = powerBatchedPolynomial (fun t ↦ (P t).map φ) (x none)) ∧
      (∀ p ∈ I, aeval (powerBatchedJetGraphMap (r := r) center
        (fun t ↦ (P t).map φ)) p = 0) ∧
      aeval (powerBatchedJetGraphMap (r := r) center (fun t ↦ (P t).map φ))
        (jointInitialJetSeparant center Q) ≠ 0 := by
  obtain ⟨P, hP, hsampleP, hrecognize⟩ :=
    exists_polynomialGraph_of_symbolic_sample_of_exponent domain w sample hsample
      φ center Q hK τ hτ
  let graph := powerBatchedJetGraphMap (r := r) center (fun t ↦ (P t).map φ)
  have hpoint (x : Option (Fin (r + 1)) → E)
      (hx : x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0) :
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
          K (fun j ↦ x (some j)) =
          powerBatchedPolynomial (fun t ↦ (P t).map φ) (x none) ∧
        (fun j ↦ x (some j)) =
          (fun j ↦ (powerBatchedJetGraph (r := r) center
            (fun t ↦ (P t).map φ) j).eval (x none)) ∧
        ∀ l : Fin K,
          aeval (fun j ↦ x (some j)) (commonTaylorNumerator center
            (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q) τ l.val) =
          aeval (fun j ↦ x (some j)) (initialJetSeparant center
            (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)) ^ τ *
            (Polynomial.taylor center
              (powerBatchedPolynomial (fun t ↦ (P t).map φ) (x none))).coeff l.val := by
    have hφ : (Polynomial.aeval (x none)).toRingHom =
        Polynomial.evalRingHom (x none) := by
      ext a <;> simp [Polynomial.evalRingHom]
    apply hrecognize (x none) (fun j ↦ x (some j))
    · rw [← hφ, ← aeval_jointInitialJetSeparant]
      exact hx.2
    · intro l hl
      have hz := hx.1 _ (hhigh l hl)
      rw [aeval_jointCommonTaylorNumerator, hφ] at hz
      exact hz
    · intro i hi
      have hz := hx.1 _ (hcuts i hi)
      rw [aeval_jointTaylorAgreementEquation, hφ] at hz
      simpa only [Polynomial.eval_C] using hz
  have hgraph : ∀ x, x ∈ zeroLocus E I ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 →
      x = fun i ↦ (graph i).eval (x none) := by
    intro x hx
    have hjet := (hpoint x hx).2.1
    funext i
    cases i with
    | none =>
      change x none = Polynomial.X.eval (x none)
      simp
    | some j => exact congrFun hjet j
  have hrange : ∀ x, x ∈ zeroLocus E I →
      aeval x (jointInitialJetSeparant center Q) ≠ 0 →
      ∃ z : E, x = fun i ↦ (graph i).eval z := by
    intro x hx hxs
    exact ⟨x none, hgraph x ⟨hx, hxs⟩⟩
  obtain ⟨_, hvanish, hseparant⟩ :=
    MvPolynomial.regular_principalOpen_graph_restriction I
      (jointInitialJetSeparant center Q) hsep hdim graph hrange
  refine ⟨P, hP, hsampleP, hgraph, ?_, hvanish, hseparant⟩
  intro x hx
  exact (hpoint x hx).1

end

end ReedSolomon
