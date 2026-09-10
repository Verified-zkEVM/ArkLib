/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.PointRecognition
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.FrobeniusCuts
/-!
# Recognizing sparse ordinary Taylor charts

Actual cleared numerator equations impose sparse reconstruction. Agreement cuts at the
pulled domain positions then identify a base-field pair from the original sample size.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

/-- A sparse regular order-zero Taylor chart is recognized by the original `k` sample
positions. Its input root lies on a polynomial graph in the pulled challenge. -/
theorem exists_frobeniusGraphLine_of_symbolic_sample
    (domain : Fin n ↪ F) (f g : Fin n → F) (sample : Finset (Fin n))
    (hsample : sample.card = k) (ι : F →+* E) (p e : ℕ) [ExpChar E p]
    (roots : Fin n → E) (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) :
    ∃ F₀ G₀ : F[X], F₀.degree < ↑k ∧ G₀.degree < ↑k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      ∀ (w : E) (jet : Fin 1 → E),
        MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom w)
          (initialJetSeparantOver (C center) Q)) ≠ 0 →
        (∀ l : Fin K, ¬p ^ e ∣ l.val →
          MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom w)
            (commonTaylorNumeratorOver (F := E) (C center) Q K l (τ := τ))) = 0) →
        (∀ i ∈ sample,
          MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom w)
            (taylorAgreementEquationOver (F := E) (C center) Q K (C (roots i))
              (C (ι (f i)) + X ^ (p ^ e) * C (ι (g i))) (τ := τ))) = 0) →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q) K jet =
            expand E (p ^ e) (F₀.map ι + C (w ^ (p ^ e)) * G₀.map ι) ∧
          jet 0 = (F₀.map ι).eval (center ^ (p ^ e)) +
            w ^ (p ^ e) * (G₀.map ι).eval (center ^ (p ^ e)) := by
  obtain ⟨F₀, G₀, hF, hG, hsampleFG, hrecognize⟩ :=
    exists_frobeniusGraphLine_polynomials_of_sample domain f g sample hsample
  refine ⟨F₀, G₀, hF, hG, hsampleFG, ?_⟩
  intro w jet hS hsparse hcuts
  let φ : E[X] →ₐ[E] E := Polynomial.aeval w
  have hcenter : φ (C center) = center := by simp [φ]
  have hφ : φ.toRingHom = Polynomial.evalRingHom w := by ext a <;> simp [φ]
  have hdegreeK :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q)
        K jet).degree < ↑K := by
    simpa only [hcenter, hφ] using
      degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
        φ (C center) Q K K τ hτ jet hS (fun l hl ↦ by omega)
  have hdegree :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q)
        K jet).degree < ↑(p ^ e * k) := hdegreeK.trans_le (by exact_mod_cast hKk)
  have hsparseP := sparse_rationalTaylorPolynomial_of_symbolic_cuts
    φ (C center) Q K (p ^ e) τ hτ jet hS hsparse
  simp only [hcenter, hφ] at hsparseP
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q)
        K jet).eval (roots i) = ι (f i) + w ^ (p ^ e) * ι (g i) := by
    intro i hi
    have h := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent
      φ (C center) Q K τ hτ jet hS (C (roots i))
        (C (ι (f i)) + X ^ (p ^ e) * C (ι (g i)))).mp (hcuts i hi)
    simp [φ, Polynomial.aeval_def, hcenter] at h
    exact h.trans (congrArg (ι (f i) + ·) (mul_comm _ _))
  obtain ⟨hpoly, heval⟩ := hrecognize ι p e roots center w _ hroots hdegree hsparseP hagree
  refine ⟨hpoly, ?_⟩
  have hjet := congrFun
    (polynomialJet_rationalTaylorPolynomial center
      (MvPolynomial.map (Polynomial.evalRingHom w) Q) K hK jet) 0
  have hzero :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q)
        K jet).eval center = jet 0 := by
    simpa [polynomialJet] using hjet
  exact hzero.symm.trans heval

end ReedSolomon
