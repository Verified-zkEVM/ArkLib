/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentRecognition

/-!
# Frobenius graph recognition on regular Taylor components

A positive-dimensional prime component containing sparse Frobenius Taylor cuts and a common
sample lies on the Frobenius graph of one pair of base-field polynomials. Every polynomial in the
component ideal vanishes after restriction to that graph, and the separant remains nonzero.
This is the two-term case of `ReedSolomon.exists_frobeniusPowerGraph_of_symbolic_prime_sample`.

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

/-- A two-term Frobenius power coordinate is the Frobenius pair coordinate. -/
private theorem frobeniusPowerCoordinate_two {R : Type*} [CommSemiring R] (s : ℕ)
    (values : Fin 2 → R) :
    frobeniusPowerCoordinate s values =
      Polynomial.C (values 0) + Polynomial.X ^ s * Polynomial.C (values 1) := by
  rw [frobeniusPowerCoordinate, powerBatchedCoordinate, Fin.sum_univ_two,
    ← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one]
  ring

/-- The Frobenius power graph of a pair is `frobeniusInitialGraph`. -/
private theorem frobeniusPowerGraphMap_two {E : Type*} [CommSemiring E] (center : E) (s : ℕ)
    (P : Fin 2 → E[X]) :
    frobeniusPowerGraphMap center s P = frobeniusInitialGraph center s (P 0) (P 1) := by
  funext i
  cases i with
  | none => rfl
  | some j =>
    simp [frobeniusPowerGraphMap, frobeniusPowerInitialGraph, frobeniusInitialGraph,
      frobeniusPowerCoordinate_two]

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
  obtain ⟨P, hP, hsampleP, hgraph, hvanish, hseparant⟩ :=
    exists_frobeniusPowerGraph_of_symbolic_prime_sample (ℓ := 1) domain ![f, g] sample hsample
      iota p e roots hroots center Q hK hKk τ hτ I hs hd hsparse
      (fun i hi ↦ by simpa [frobeniusPowerCoordinate_two] using hcuts i hi)
  rw [frobeniusPowerGraphMap_two] at hgraph hvanish hseparant
  exact ⟨P 0, P 1, hP 0, hP 1, fun i hi ↦ ⟨by simpa using hsampleP i hi 0,
    by simpa using hsampleP i hi 1⟩, hgraph, hvanish, hseparant⟩

end

end ReedSolomon
