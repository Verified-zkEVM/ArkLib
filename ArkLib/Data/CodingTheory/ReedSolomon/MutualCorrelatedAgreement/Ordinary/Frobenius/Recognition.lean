/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.TaylorChart
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ComponentRecognition
/-!
# Prime components of sparse ordinary Taylor charts

Sparse numerator cuts and an original-size common sample force a prime component onto
one Frobenius graph. Every component equation then vanishes identically on that graph.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

/-- The received-line equation in the pulled challenge coordinate. -/
def symbolicSourceFrobeniusAgreement (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K τ s : ℕ) (alpha u v : E) :
    MvPolynomial (Option (Fin 1)) E :=
  (optionEquivRight E _).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K (Polynomial.C alpha)
      (Polynomial.C u + Polynomial.X ^ s * Polynomial.C v) (τ := τ))

/-- The initial-value graph of a base-field pair in the pulled challenge. -/
def frobeniusInitialGraph (center : E) (s : ℕ) (F₀ G₀ : E[X]) : Fin 1 → E[X] :=
  fun _ ↦ Polynomial.C (F₀.eval (center ^ s)) +
    Polynomial.X ^ s * Polynomial.C (G₀.eval (center ^ s))

/-- Recognition uses only the actual prime-ideal equations and the original `k` sample.
The resulting graph is defined by a pair over the original received-word field. -/
theorem exists_frobeniusGraph_of_symbolic_prime_sample [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (sample : Finset (Fin n))
    (hsample : sample.card = k) (ι : F →+* E) (p e : ℕ) [ExpChar E p]
    (roots : Fin n → E) (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hsparse : ∀ l : Fin K, ¬p ^ e ∣ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ I)
    (hcuts : ∀ i ∈ sample,
      symbolicSourceFrobeniusAgreement center Q K τ (p ^ e)
        (roots i) (ι (f i)) (ι (g i)) ∈ I) :
    ∃ F₀ G₀ : F[X], F₀.degree < ↑k ∧ G₀.degree < ↑k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      (∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        x = polynomialGraphPoint
          (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι)) (x none)) ∧
      (∀ q ∈ I, polynomialGraphPullback
        (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι)) q = 0) ∧
      polynomialGraphPullback
        (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι))
        (symbolicSourceSeparant center Q) ≠ 0 := by
  obtain ⟨F₀, G₀, hF, hG, hsampleFG, hrecognize⟩ :=
    exists_frobeniusGraphLine_of_symbolic_sample domain f g sample hsample
      ι p e roots hroots center Q hK hKk τ hτ
  have hgraph : ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
      x = polynomialGraphPoint
        (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι)) (x none) := by
    intro x hx
    have hpoint := hrecognize (x none) (fun j ↦ x (some j))
      (by simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm] using hx.2)
      (fun l hl ↦ by
        have hz := hx.1 _ (hsparse l hl)
        simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm] using hz)
      (fun i hi ↦ by
        have hz := hx.1 _ (hcuts i hi)
        simpa only [symbolicSourceFrobeniusAgreement,
          aeval_optionEquivRight_symm] using hz)
    funext j
    cases j with
    | none => rfl
    | some j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [polynomialGraphPoint, frobeniusInitialGraph,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      exact hpoint.2
  obtain ⟨hvanish, hsep⟩ := polynomialGraphPullback_vanishes_of_principalOpen
    hI hs hd (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι)) hgraph
  exact ⟨F₀, G₀, hF, hG, hsampleFG, hgraph, hvanish, hsep⟩

end ReedSolomon
