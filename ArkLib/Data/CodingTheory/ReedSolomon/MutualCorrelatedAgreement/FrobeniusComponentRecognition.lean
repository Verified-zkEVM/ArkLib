/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
/-!
# Frobenius graph recognition on regular Taylor components

A positive-dimensional prime component containing sparse Frobenius Taylor cuts and a common
sample lies on the Frobenius graph of one pair of base-field polynomials. Every polynomial in the
component ideal vanishes after restriction to that graph, and the separant remains nonzero.

## Main statements

* `ReedSolomon.exists_frobeniusGraph_of_symbolic_prime_sample`: recognition of a Frobenius graph
  from sparse Taylor cuts on a positive-dimensional prime component.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

/-- The challenge and order-zero jet coordinates of a pair on a Frobenius graph. -/
def frobeniusInitialGraph {E : Type*} [CommSemiring E] (center : E) (s : ℕ)
    (F₀ G₀ : E[X]) : Option (Fin 1) → E[X] :=
  fun i ↦ i.elim Polynomial.X fun _ ↦
    Polynomial.C (F₀.eval (center ^ s)) +
      Polynomial.X ^ s * Polynomial.C (G₀.eval (center ^ s))

variable {F E ι : Type*} [Field F] [Field E] {k K : ℕ}

/-- Sparse Frobenius Taylor cuts on a positive-dimensional prime component determine one
base-field polynomial pair. The regular principal open is parametrized by its Frobenius graph,
every component equation vanishes on that graph, and the separant remains nonzero. -/
theorem exists_frobeniusGraph_of_symbolic_prime_sample [IsAlgClosed E]
    (domain : ι ↪ F) (f g : ι → F) (sample : Finset ι) (hsample : sample.card = k)
    (iota : F →+* E) (p e : ℕ) [ExpChar E p]
    (roots : ι → E) (hroots : ∀ i ∈ sample, roots i ^ (p ^ e) = iota (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) [I.IsPrime]
    (hs : jointInitialJetSeparant center Q ∉ I)
    (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (hsparse : ∀ l : Fin K, ¬p ^ e ∣ l.val →
      jointCommonTaylorNumerator center Q τ l ∈ I)
    (hcuts : ∀ i ∈ sample,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) * Polynomial.C (iota (g i))) ∈ I) :
    ∃ F₀ G₀ : F[X], F₀.degree < ↑k ∧ G₀.degree < ↑k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      (∀ x ∈ {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0},
        x = fun i ↦ (frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota) i).eval
          (x none)) ∧
      (∀ q ∈ I,
        aeval (frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota)) q = 0) ∧
      aeval (frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota))
        (jointInitialJetSeparant center Q) ≠ 0 := by
  obtain ⟨F₀, G₀, hF, hG, hsampleFG, hrecognize⟩ :=
    exists_frobeniusGraphLine_of_symbolic_sample domain f g sample hsample iota p e roots hroots
      center Q hK hKk τ hτ
  let graph := frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota)
  have hpoint (x : Option (Fin 1) → E)
      (hx : x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0) :
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q) K
          (fun j ↦ x (some j)) =
        expand E (p ^ e) (F₀.map iota + Polynomial.C ((x none) ^ (p ^ e)) * G₀.map iota) ∧
        x (some 0) = (F₀.map iota).eval (center ^ (p ^ e)) +
          (x none) ^ (p ^ e) * (G₀.map iota).eval (center ^ (p ^ e)) := by
    let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
    have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
      ext a <;> simp [φ, Polynomial.evalRingHom]
    apply hrecognize (x none) (fun j ↦ x (some j))
    · have hS : aeval (fun j ↦ x (some j))
          (MvPolynomial.map φ.toRingHom (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
        simpa only [jointInitialJetSeparant, aeval_optionEquivRight_symm] using hx.2
      simpa only [hφ] using hS
    · intro l hl
      have hz := hx.1 _ (hsparse l hl)
      have hnum : aeval (fun j ↦ x (some j))
          (MvPolynomial.map φ.toRingHom
            (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)) = 0 := by
        simpa only [jointCommonTaylorNumerator, aeval_optionEquivRight_symm] using hz
      simpa only [hφ] using hnum
    · intro i hi
      have hz := hx.1 _ (hcuts i hi)
      have hcut : aeval (fun j ↦ x (some j))
          (MvPolynomial.map φ.toRingHom
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (roots i))
              (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) *
                Polynomial.C (iota (g i))) (τ := τ))) = 0 := by
        simpa only [jointTaylorAgreementEquation, aeval_optionEquivRight_symm] using hz
      simpa only [hφ] using hcut
  have hgraph : ∀ x,
      x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0 →
      x = fun i ↦ (graph i).eval (x none) := by
    intro x hx
    have hjet := (hpoint x hx).2
    funext i
    cases i with
    | none => simp [graph, frobeniusInitialGraph]
    | some j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hjet' : x (some 0) = (F₀.map iota).eval (center ^ (p ^ e)) +
          (G₀.map iota).eval (center ^ (p ^ e)) * (x none) ^ (p ^ e) := by
        calc
          _ = (F₀.map iota).eval (center ^ (p ^ e)) +
              (x none) ^ (p ^ e) * (G₀.map iota).eval (center ^ (p ^ e)) := hjet
          _ = _ := by rw [mul_comm]
      simpa [graph, frobeniusInitialGraph] using hjet'
  have hrange : ∀ x, x ∈ zeroLocus E I →
      aeval x (jointInitialJetSeparant center Q) ≠ 0 →
      ∃ z : E, x = fun i ↦ (graph i).eval z := by
    intro x hx hsep
    exact ⟨x none, hgraph x ⟨hx, hsep⟩⟩
  obtain ⟨_, hvanish, hseparant⟩ :=
    MvPolynomial.regular_principalOpen_graph_restriction I
      (jointInitialJetSeparant center Q) hs hd graph hrange
  exact ⟨F₀, G₀, hF, hG, hsampleFG, hgraph, hvanish, hseparant⟩

end

end ReedSolomon
