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

* `ReedSolomon.exists_polynomialGraph_of_primeTaylorComponent`: recognition of a prime component
  and its graph identities for a tuple of arbitrary length.
* `ReedSolomon.frobeniusPowerInitialGraph` and `ReedSolomon.frobeniusPowerGraphMap`: the
  initial-value curve and its polynomial graph map.
* `ReedSolomon.exists_frobeniusPowerGraph_of_symbolic_sample`: reconstruction of a sparse
  Frobenius power graph from symbolic Taylor cuts at a common sample.
* `ReedSolomon.exists_frobeniusPowerGraph_of_symbolic_prime_sample`: recognition of a sparse
  Frobenius power graph on a positive-dimensional prime component.

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

variable {F E α : Type*} [Field F] [Field E] {k K ℓ : ℕ}

/-- The single jet coordinate is the scaled polynomial coordinate of the values
`(P t).eval (center ^ s)`. -/
def frobeniusPowerInitialGraph {E : Type*} [CommSemiring E] (center : E) (s : ℕ)
    (P : Fin (ℓ + 1) → E[X]) : Fin 1 → E[X] :=
  fun _ ↦ frobeniusPowerCoordinate s (fun t ↦ (P t).eval (center ^ s))

/-- The graph map whose challenge coordinate is `X` and whose initial-value coordinate is the
Frobenius-pulled curve of the polynomial tuple. -/
def frobeniusPowerGraphMap {E : Type*} [CommSemiring E] (center : E) (s : ℕ)
    (P : Fin (ℓ + 1) → E[X]) : Option (Fin 1) → E[X] :=
  fun i ↦ i.elim Polynomial.X (frobeniusPowerInitialGraph center s P)

/-- A common sample of agreement cuts and sparse Taylor cuts determines the Frobenius-pulled
polynomial graph at every regular symbolic chart point. The reconstructed tuple has degree below
the sample size. -/
theorem exists_frobeniusPowerGraph_of_symbolic_sample
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F)
    (sample : Finset α) (hsample : sample.card = k)
    (ι : F →+* E) (p e : ℕ) [ExpChar E p]
    (roots : α → E) (hroots : ∀ i ∈ sample, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = values t i) ∧
      ∀ (z : E) (jet : Fin 1 → E),
        aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
          (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 →
        (∀ l : Fin K, ¬p ^ e ∣ l.val →
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q τ l.val)) = 0) →
        (∀ i ∈ sample,
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (roots i))
              (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))
              (τ := τ))) = 0) →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K jet =
            Polynomial.expand E (p ^ e)
              (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) ∧
          jet 0 = (frobeniusPowerInitialGraph center (p ^ e)
            (fun t ↦ (P t).map ι) 0).eval z := by
  obtain ⟨P, hPdegree, hPsample, hrecognize⟩ :=
    exists_frobeniusPowerGraph_polynomials_of_sample domain values sample hsample
  refine ⟨P, hPdegree, hPsample, ?_⟩
  intro z jet hS hsparse hcuts
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by ext a <;> simp [φ]
  have hdegreeK :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).degree < K := by
    simpa only [hcenter, hφ] using
      degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
        φ (Polynomial.C center) Q K K τ hτ jet hS (fun l hl ↦ by omega)
  have hdegree :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).degree < p ^ e * k := hdegreeK.trans_le (by exact_mod_cast hKk)
  have hsparseQ := sparse_rationalTaylorPolynomial_of_symbolic_cuts
    φ (Polynomial.C center) Q K (p ^ e) τ hτ jet hS hsparse
  simp only [hcenter, hφ] at hsparseQ
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).eval (roots i) =
          ∑ t, z ^ (p ^ e * t.val) * ι (values t i) := by
    intro i hi
    have h := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent
      φ (Polynomial.C center) Q K τ hτ jet hS (Polynomial.C (roots i))
        (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))).mp (hcuts i hi)
    simpa only [hφ, hcenter, φ, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id, Polynomial.eval_C, frobeniusPowerCoordinate_eval] using h
  obtain ⟨hpoly, heval⟩ :=
    hrecognize ι p e roots center z _ hroots hdegree hsparseQ hagree
  refine ⟨hpoly, ?_⟩
  have hjet := congrFun
    (polynomialJet_rationalTaylorPolynomial center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) hK jet) 0
  have hzero :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).eval center = jet 0 := by
    simpa [polynomialJet] using hjet
  calc
    jet 0 =
        (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
          K jet).eval center := hzero.symm
    _ = (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))).eval
        (center ^ (p ^ e)) := heval
    _ = (frobeniusPowerInitialGraph center (p ^ e)
        (fun t ↦ (P t).map ι) 0).eval z := by
      simp only [frobeniusPowerInitialGraph, frobeniusPowerCoordinate_eval,
        powerBatchedPolynomial_eval, pow_mul]

/-- A positive-dimensional prime component with sparse Taylor and sample agreement cuts is
parametrized by a Frobenius power graph. Every component equation vanishes after restriction to
the graph, and the separant remains nonzero. -/
theorem exists_frobeniusPowerGraph_of_symbolic_prime_sample [IsAlgClosed E]
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F)
    (sample : Finset α) (hsample : sample.card = k)
    (ι : F →+* E) (p e : ℕ) [ExpChar E p]
    (roots : α → E) (hroots : ∀ i ∈ sample, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) [I.IsPrime]
    (hsep : jointInitialJetSeparant center Q ∉ I)
    (hdim : 0 < (affineHilbertPolynomial I).natDegree)
    (hsparse : ∀ l : Fin K, ¬p ^ e ∣ l.val → jointCommonTaylorNumerator center Q τ l ∈ I)
    (hcuts : ∀ i ∈ sample,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = values t i) ∧
      (∀ x ∈ {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0},
        x = fun i ↦
          (frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι) i).eval
            (x none)) ∧
      (∀ q ∈ I, aeval (frobeniusPowerGraphMap center (p ^ e)
        (fun t ↦ (P t).map ι)) q = 0) ∧
      aeval (frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι))
        (jointInitialJetSeparant center Q) ≠ 0 := by
  obtain ⟨P, hPdegree, hPsample, hrecognize⟩ :=
    exists_frobeniusPowerGraph_of_symbolic_sample domain values sample hsample
      ι p e roots hroots center Q hK hKk τ hτ
  let graph : Option (Fin 1) → E[X] :=
    frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι)
  have hgraph : ∀ x,
      x ∈ {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} →
      x = fun i ↦ (graph i).eval (x none) := by
    intro x hx
    have hφ : (Polynomial.aeval (x none)).toRingHom =
        Polynomial.evalRingHom (x none) := by
      ext a <;> simp [Polynomial.evalRingHom]
    have hpoint := hrecognize (x none) (fun j ↦ x (some j))
      (by simpa only [jointInitialJetSeparant, aeval_optionEquivRight_symm, hφ] using hx.2)
      (fun l hl ↦ by
        have hz := hx.1 _ (hsparse l hl)
        simpa only [jointCommonTaylorNumerator, aeval_optionEquivRight_symm, hφ] using hz)
      (fun i hi ↦ by
        have hz := hx.1 _ (hcuts i hi)
        simpa only [jointTaylorAgreementEquation, aeval_optionEquivRight_symm, hφ] using hz)
    funext i
    cases i with
    | none =>
      change x none = Polynomial.X.eval (x none)
      simp
    | some j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change x (some 0) =
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι) 0).eval (x none)
      exact hpoint.2
  have hrange : ∀ x : Option (Fin 1) → E, x ∈ zeroLocus E I →
      aeval x (jointInitialJetSeparant center Q) ≠ 0 →
      ∃ z : E, x = fun i ↦ (graph i).eval z := by
    intro x hx hxs
    exact ⟨x none, hgraph x ⟨hx, hxs⟩⟩
  obtain ⟨_, hvanish, hseparant⟩ :=
    MvPolynomial.regular_principalOpen_graph_restriction I
      (jointInitialJetSeparant center Q) hsep hdim graph hrange
  exact ⟨P, hPdegree, hPsample, (by simpa [graph] using hgraph),
    (by simpa [graph] using hvanish), (by simpa [graph] using hseparant)⟩

end

end ReedSolomon
