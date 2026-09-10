/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PointRecognition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ComponentRecognition
/-!
# Recognizing polynomial graphs from prime Taylor-chart components

Every positive-dimensional regular prime component supported on `k` common agreement
cuts lies on the graph of the tuple interpolated on those positions. Restricting its ideal
to that graph gives polynomial identities, and the separant does not vanish identically.
The statement works over any algebraically closed extension of the received-word field.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.6 (Theorem 5.14), recognition of polynomial graphs.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K r ℓ : ℕ}

/-- A received-curve agreement cut in the joint challenge and initial-jet coordinates at a
specified common Taylor exponent. -/
def symbolicSourceCurveAgreement_of_exponent (center : E)
    (Q : DifferentialPolynomial E[X] r) (K τ : ℕ) (alpha : E) (w : Fin (ℓ + 1) → E) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
      (Polynomial.C alpha) (powerBatchedCoordinate w) (τ := τ))

/-- Compatibility form at the former coarse common exponent. -/
def symbolicSourceCurveAgreement (center : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (alpha : E) (w : Fin (ℓ + 1) → E) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
      (Polynomial.C alpha) (powerBatchedCoordinate w))

/-- Actual prime components with a common sample yield a base-field polynomial tuple.
Every equation of the component vanishes on the whole tuple graph, while its separant
remains nonzero. The common sample need not be maximal. -/
theorem exists_polynomialGraph_of_symbolic_prime_sample_of_exponent [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (ι : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hhigh : ∀ l : Fin K, k ≤ l.val → symbolicSourceNumerator center Q K l (τ := τ) ∈ I)
    (hcuts : ∀ i ∈ sample,
      symbolicSourceCurveAgreement_of_exponent center Q K τ
        (ι (domain i)) (fun t ↦ ι (w t i)) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = w t i) ∧
      (∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        x = polynomialGraphPoint
          (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι)) (x none)) ∧
      (∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
          K (fun j ↦ x (some j)) = powerBatchedPolynomial (fun t ↦ (P t).map ι) (x none)) ∧
      (∀ p ∈ I, polynomialGraphPullback
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι)) p = 0) ∧
      polynomialGraphPullback
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι))
        (symbolicSourceSeparant center Q) ≠ 0 := by
  obtain ⟨P, hP, hsampleP, hrecognize⟩ :=
    exists_polynomialGraph_of_symbolic_sample_of_exponent domain w sample hsample
      ι center Q hK τ hτ
  have hgraph : ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
      x = polynomialGraphPoint
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι)) (x none) := by
    intro x hx
    have hpoint := hrecognize (x none) (fun j ↦ x (some j))
      (by simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm] using hx.2)
      (fun l hl ↦ by
        have hz := hx.1 _ (hhigh l hl)
        simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm] using hz)
      (fun i hi ↦ by
        have hz := hx.1 _ (hcuts i hi)
        simpa only [symbolicSourceCurveAgreement_of_exponent,
          aeval_optionEquivRight_symm] using hz)
    funext j
    cases j with
    | none => rfl
    | some j => exact congrFun hpoint.2.1 j
  obtain ⟨hvanish, hsep⟩ := polynomialGraphPullback_vanishes_of_principalOpen
    hI hs hd (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι)) hgraph
  refine ⟨P, hP, hsampleP, hgraph, ?_, hvanish, hsep⟩
  intro x hx
  exact (hrecognize (x none) (fun j ↦ x (some j))
    (by simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm] using hx.2)
    (fun l hl ↦ by
      have hz := hx.1 _ (hhigh l hl)
      simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm] using hz)
    (fun i hi ↦ by
      have hz := hx.1 _ (hcuts i hi)
      simpa only [symbolicSourceCurveAgreement_of_exponent,
        aeval_optionEquivRight_symm] using hz)).1


end ReedSolomon
