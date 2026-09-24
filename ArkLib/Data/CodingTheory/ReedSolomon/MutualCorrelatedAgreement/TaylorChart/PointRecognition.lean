/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra

/-!
# Graph-line recognition on symbolic Taylor charts

A sample of agreement equations and high Taylor cuts determines one pair of polynomials over the
received words' base field. At every regular symbolic chart point satisfying those equations, the
reconstructed polynomial is the affine combination of that same pair, and its jet and cleared
Taylor coefficients satisfy the corresponding identities.

## Main statements

* `ReedSolomon.exists_graphLine_pair_of_symbolic_sample_of_exponent`: one sample determines a
  base-field pair for every sufficient common exponent.
* `ReedSolomon.exists_graphLine_pair_of_symbolic_sample`: one sample determines a base-field pair
  that reconstructs every regular symbolic Taylor chart point at the default exponent.
* `ReedSolomon.exists_frobeniusGraphLine_of_symbolic_sample`: one sample recognizes the
  Frobenius pullback of a regular order-zero symbolic Taylor chart.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

/-- One sample determines a base-field pair uniformly for all regular symbolic chart points at a
sufficient common exponent. The conclusions identify the reconstructed polynomial, its initial
jet, and each cleared Taylor coefficient. -/
theorem exists_graphLine_pair_of_symbolic_sample_of_exponent
    {F E : Type*} [Field F] [Field E] {n k K r : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      ∀ (z : E) (jet : Fin (r + 1) → E),
        aeval jet (map (Polynomial.evalRingHom z)
          (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 →
        (∀ l : Fin K, k ≤ l.val →
        aeval jet (map (Polynomial.evalRingHom z)
            (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)) = 0) →
        (∀ i ∈ sample,
          aeval jet (map (Polynomial.evalRingHom z)
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (iota (domain i)))
              (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))
                ) (τ := τ))) = 0) →
        rationalTaylorPolynomial center (map (Polynomial.evalRingHom z) Q) K jet =
            P₀.map iota + Polynomial.C z * P₁.map iota ∧
          jet = (fun j ↦ polynomialJet (d := r) center (P₀.map iota) j +
            z * polynomialJet (d := r) center (P₁.map iota) j) ∧
          ∀ l : Fin K,
            aeval jet (map (Polynomial.evalRingHom z)
              (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)) =
              aeval jet (map (Polynomial.evalRingHom z)
                (initialJetSeparant (Polynomial.C center) Q)) ^ τ *
                (Polynomial.taylor center
                  (P₀.map iota + Polynomial.C z * P₁.map iota)).coeff l.val := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample domain f g sample hsample
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, ?_⟩
  intro z jet hS hhigh hcuts
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ, Polynomial.evalRingHom]
  have hdegree :
      (rationalTaylorPolynomial center (map (Polynomial.evalRingHom z) Q) K jet).degree < k := by
    simpa only [hcenter, hφ] using
      degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
        φ (Polynomial.C center) Q K k τ hτ jet hS hhigh
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center (map (Polynomial.evalRingHom z) Q) K jet).eval
          (domain.trans ⟨iota, iota.injective⟩ i) = iota (f i) + z * iota (g i) := by
    intro i hi
    have heval := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent φ
      (Polynomial.C center) Q K τ hτ jet hS (Polynomial.C (iota (domain i)))
      (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))).mp
        (hcuts i hi)
    have heval' :
        (rationalTaylorPolynomial center (map (Polynomial.evalRingHom z) Q) K jet).eval
            (domain.trans ⟨iota, iota.injective⟩ i) = iota (f i) + iota (g i) * z := by
      simpa [hcenter, hφ, φ] using heval
    exact heval'.trans (by ring)
  have hpoly := hrecognize iota z _ hdegree hagree
  refine ⟨hpoly, ?_, ?_⟩
  · rw [← polynomialJet_add_C_mul center z, ← hpoly,
      polynomialJet_rationalTaylorPolynomial center _ hK]
  · intro l
    have hcoeff := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ
      (Polynomial.C center) Q K τ hτ jet hS l
    simpa only [hφ, hcenter, hpoly] using hcoeff

/-- One sample determines a base-field pair uniformly for all regular symbolic chart points at
the default exponent. The conclusions identify the reconstructed polynomial, its initial jet,
and each cleared Taylor coefficient. -/
theorem exists_graphLine_pair_of_symbolic_sample
    {F E : Type*} [Field F] [Field E] {n k K r : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      ∀ (z : E) (jet : Fin (r + 1) → E),
        aeval jet (map (Polynomial.evalRingHom z)
          (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 →
        (∀ l : Fin K, k ≤ l.val →
          aeval jet (map (Polynomial.evalRingHom z)
            (commonTaylorNumeratorOver E (Polynomial.C center) Q (2 * K) l.val)) = 0) →
        (∀ i ∈ sample,
          aeval jet (map (Polynomial.evalRingHom z)
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (iota (domain i)))
              (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))
              (τ := 2 * K))) = 0) →
        rationalTaylorPolynomial center (map (Polynomial.evalRingHom z) Q) K jet =
            P₀.map iota + Polynomial.C z * P₁.map iota ∧
          jet = (fun j ↦ polynomialJet (d := r) center (P₀.map iota) j +
            z * polynomialJet (d := r) center (P₁.map iota) j) ∧
          ∀ l : Fin K,
            aeval jet (map (Polynomial.evalRingHom z)
              (commonTaylorNumeratorOver E (Polynomial.C center) Q (2 * K) l.val)) =
              aeval jet (map (Polynomial.evalRingHom z)
                (initialJetSeparant (Polynomial.C center) Q)) ^ (2 * K) *
                (Polynomial.taylor center
                  (P₀.map iota + Polynomial.C z * P₁.map iota)).coeff l.val := by
  simpa only using exists_graphLine_pair_of_symbolic_sample_of_exponent
    domain f g sample hsample iota center Q hK (2 * K) (taylorExponentSufficient_two_mul r K)

/-- A sample determines a base-field pair whose Frobenius pullback reconstructs every regular
order-zero symbolic Taylor chart satisfying the sparse and agreement cuts. Roots are needed only
at sample positions. -/
theorem exists_frobeniusGraphLine_of_symbolic_sample
    {F E ι : Type*} [Field F] [Field E] {k K : ℕ}
    (domain : ι ↪ F) (f g : ι → F) (sample : Finset ι)
    (hsample : sample.card = k) (iota : F →+* E) (p e : ℕ) [ExpChar E p]
    (roots : ι → E) (hroots : ∀ i ∈ sample, roots i ^ (p ^ e) = iota (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      ∀ (w : E) (jet : Fin 1 → E),
        MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom w)
          (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 →
        (∀ l : Fin K, ¬p ^ e ∣ l.val →
          MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom w)
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q τ l.val)) = 0) →
        (∀ i ∈ sample,
          MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom w)
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (roots i))
              (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) *
                Polynomial.C (iota (g i))) (τ := τ))) = 0) →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q) K jet =
            expand E (p ^ e)
              (F₀.map iota + Polynomial.C (w ^ (p ^ e)) * G₀.map iota) ∧
          jet 0 = (F₀.map iota).eval (center ^ (p ^ e)) +
            w ^ (p ^ e) * (G₀.map iota).eval (center ^ (p ^ e)) := by
  obtain ⟨F₀, G₀, hF, hG, hsampleFG, hrecognize⟩ :=
    exists_frobeniusGraphLine_polynomials_of_sample domain f g sample hsample
  refine ⟨F₀, G₀, hF, hG, hsampleFG, ?_⟩
  intro w jet hS hsparse hcuts
  let φ : E[X] →ₐ[E] E := Polynomial.aeval w
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hφ : φ.toRingHom = Polynomial.evalRingHom w := by ext a <;> simp [φ]
  have hdegreeK :
    (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q)
        K jet).degree < ↑K := by
    simpa only [hcenter, hφ] using
      degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
        φ (Polynomial.C center) Q K K τ hτ jet hS (fun l hl ↦ by omega)
  have hdegree :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q)
        K jet).degree < ↑(p ^ e * k) := hdegreeK.trans_le (by exact_mod_cast hKk)
  have hsparseP := sparse_rationalTaylorPolynomial_of_symbolic_cuts
    φ (Polynomial.C center) Q K (p ^ e) τ hτ jet hS hsparse
  simp only [hcenter, hφ] at hsparseP
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q)
        K jet).eval (roots i) = iota (f i) + w ^ (p ^ e) * iota (g i) := by
    intro i hi
    have h := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent
      φ (Polynomial.C center) Q K τ hτ jet hS (Polynomial.C (roots i))
        (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) *
          Polynomial.C (iota (g i)))).mp (hcuts i hi)
    simp [φ, Polynomial.aeval_def, hcenter] at h
    exact h.trans (congrArg (iota (f i) + ·) (mul_comm _ _))
  obtain ⟨hpoly, heval⟩ := hrecognize iota p e roots center w _ hroots hdegree hsparseP hagree
  refine ⟨hpoly, ?_⟩
  have hjet := congrFun
    (polynomialJet_rationalTaylorPolynomial center
      (MvPolynomial.map (Polynomial.evalRingHom w) Q) hK jet) 0
  have hzero :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q)
        K jet).eval center = jet 0 := by
    simpa [polynomialJet] using hjet
  exact hzero.symm.trans heval

end

end ReedSolomon
