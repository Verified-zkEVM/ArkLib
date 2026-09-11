/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Point
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.FrobeniusCuts
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ComponentRecognition
/-!
# Prime-component recognition for Frobenius-pulled polynomial curves

This generalizes the ordinary line chart from `u + X ^ s * v` to the sparse power curve
`∑ t, X ^ (s * t.val) * w t`.  Sparse Taylor contraction occurs before interpolation, so every
recovered constituent retains the original degree bound `k`, not the expanded bound `s * k`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert
open scoped BigOperators

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

/-- A received power-curve coordinate in the Frobenius-pulled challenge. -/
def frobeniusPowerCoordinate (s : ℕ) (values : Fin (ℓ + 1) → E) : E[X] :=
  ∑ t, Polynomial.monomial (s * t.val) (values t)

theorem frobeniusPowerCoordinate_eval (s : ℕ) (values : Fin (ℓ + 1) → E) (z : E) :
    (frobeniusPowerCoordinate s values).eval z =
      ∑ t, z ^ (s * t.val) * values t := by
  rw [frobeniusPowerCoordinate, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Polynomial.eval_monomial]
  rw [mul_comm]

theorem frobeniusPowerCoordinate_natDegree_le
    (s : ℕ) (values : Fin (ℓ + 1) → E) :
    (frobeniusPowerCoordinate s values).natDegree ≤ s * ℓ := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro t _
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.mul_le_mul_left s (Fin.is_le t))

/-- The received-curve agreement cut in the pulled challenge coordinate. -/
def symbolicSourceFrobeniusPowerAgreement (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K τ s : ℕ) (alpha : E)
    (values : Fin (ℓ + 1) → E) : MvPolynomial (Option (Fin 1)) E :=
  (optionEquivRight E _).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
      (Polynomial.C alpha) (frobeniusPowerCoordinate s values) (τ := τ))

/-- The initial-value graph of an original-degree polynomial tuple in the pulled challenge. -/
def frobeniusPowerInitialGraph (center : E) (s : ℕ)
    (P : Fin (ℓ + 1) → E[X]) : Fin 1 → E[X] :=
  fun _ ↦ frobeniusPowerCoordinate s (fun t ↦ (P t).eval (center ^ s))

/-- Actual sparse Taylor cuts and one common original-size sample recognize a pulled power curve.
The reconstructed tuple is over the original received-word field and has degree `< k`. -/
theorem exists_frobeniusPowerGraph_of_symbolic_sample
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (ι : F →+* E) (p e : ℕ) [ExpChar E p]
    (roots : Fin n → E) (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = values t i) ∧
      ∀ (z : E) (jet : Fin 1 → E),
        aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
          (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 →
        (∀ l : Fin K, ¬p ^ e ∣ l.val →
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))) = 0) →
        (∀ i ∈ sample,
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (roots i))
              (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))) (τ := τ))) = 0) →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K jet =
            expand E (p ^ e)
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
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) K hK jet) 0
  have hzero :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).eval center = jet 0 := by
    simpa [polynomialJet] using hjet
  rw [← hzero, heval]
  simp only [frobeniusPowerInitialGraph, frobeniusPowerCoordinate_eval,
    powerBatchedPolynomial_eval, pow_mul]

/-- A positive-dimensional regular prime component satisfying the sparse curve cuts lies on one
original-degree Frobenius power graph.  Every component equation vanishes on that graph. -/
theorem exists_frobeniusPowerGraph_of_symbolic_prime_sample [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (ι : F →+* E) (p e : ℕ) [ExpChar E p]
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
      symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e)
        (roots i) (fun t ↦ ι (values t i)) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = values t i) ∧
      (∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        x = polynomialGraphPoint
          (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι)) (x none)) ∧
      (∀ q ∈ I, polynomialGraphPullback
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι)) q = 0) ∧
      polynomialGraphPullback
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι))
        (symbolicSourceSeparant center Q) ≠ 0 := by
  obtain ⟨P, hPdegree, hPsample, hrecognize⟩ :=
    exists_frobeniusPowerGraph_of_symbolic_sample domain values sample hsample
      ι p e roots hroots center Q hK hKk τ hτ
  have hgraph : ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
      x = polynomialGraphPoint
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι)) (x none) := by
    intro x hx
    have hpoint := hrecognize (x none) (fun j ↦ x (some j))
      (by simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm] using hx.2)
      (fun l hl ↦ by
        have hz := hx.1 _ (hsparse l hl)
        simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm] using hz)
      (fun i hi ↦ by
        have hz := hx.1 _ (hcuts i hi)
        simpa only [symbolicSourceFrobeniusPowerAgreement,
          aeval_optionEquivRight_symm] using hz)
    funext j
    cases j with
    | none => rfl
    | some j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change x (some 0) =
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι) 0).eval (x none)
      exact hpoint.2
  obtain ⟨hvanish, hsep⟩ := polynomialGraphPullback_vanishes_of_principalOpen
    hI hs hd (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι)) hgraph
  exact ⟨P, hPdegree, hPsample, hgraph, hvanish, hsep⟩

end ReedSolomon
