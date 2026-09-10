/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorCuts
/-!
# Graph recognition at actual symbolic Taylor points

A common sample of `k` agreement cuts determines a pair over the received words' base field.
Every regular symbolic chart point satisfying these cuts and the high-coefficient cuts
reconstructs the affine combination of that same pair. Its retained initial jet and all
cleared Taylor coefficients therefore satisfy the corresponding affine graph identities.
Neither a differential-solution premise nor an assumed graph-recognition law is required.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon

noncomputable section

open Polynomial MvPolynomial HiddenDerivative

/-- Taking the initial Hasse jet preserves an affine polynomial combination. -/
theorem polynomialJet_affine_combination {E : Type*} [Field E] {r : ℕ}
    (center z : E) (P Q : E[X]) :
    polynomialJet (d := r) center (P + Polynomial.C z * Q) =
      fun j ↦ polynomialJet (d := r) center P j + z * polynomialJet (d := r) center Q j := by
  rw [← Polynomial.smul_eq_C_mul]
  funext j
  simp [polynomialJet]

/-- One sample determines a base-field pair uniformly for all regular symbolic chart points.
The conclusions identify the reconstructed polynomial, its initial jet, and every one of its
`K` cleared Taylor coefficients. The symbolic equation may be over an arbitrary field extension
containing the chosen Taylor center. -/
theorem exists_graphLine_pair_of_symbolic_sample
    {F E : Type*} [Field F] [Field E] {n k K r : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      ∀ (z : E) (jet : Fin (r + 1) → E),
        aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
          (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 →
        (∀ l : Fin K, k ≤ l.val →
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l)) = 0) →
        (∀ i ∈ sample,
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (iota (domain i)))
              (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))))) = 0) →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K jet =
            P₀.map iota + Polynomial.C z * P₁.map iota ∧
          jet = (fun j ↦ polynomialJet (d := r) center (P₀.map iota) j +
            z * polynomialJet (d := r) center (P₁.map iota) j) ∧
          ∀ l : Fin K,
            aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
              (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l)) =
              aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
                (initialJetSeparantOver (Polynomial.C center) Q)) ^ (2 * K) *
                (Polynomial.taylor center
                  (P₀.map iota + Polynomial.C z * P₁.map iota)).coeff l.val := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample domain f g sample hsample
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, ?_⟩
  intro z jet hS hhigh hcuts
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ]
  have hdegree :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).degree < k := by
    simpa only [hcenter, hφ] using degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts φ
      (Polynomial.C center) Q K k jet hS hhigh
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).eval (mappedDomain domain iota i) = iota (f i) + z * iota (g i) := by
    intro i hi
    have heval := (aeval_map_taylorAgreementEquationOver_eq_zero_iff φ
      (Polynomial.C center) Q K jet hS (Polynomial.C (iota (domain i)))
      (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))).mp
        (hcuts i hi)
    have heval' :
        (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
          K jet).eval (mappedDomain domain iota i) = iota (f i) + iota (g i) * z := by
      simpa [hφ, φ, mappedDomain] using heval
    exact heval'.trans (by ring)
  have hpoly := hrecognize iota z _ hdegree hagree
  refine ⟨hpoly, ?_, ?_⟩
  · rw [← polynomialJet_affine_combination, ← hpoly,
      polynomialJet_rationalTaylorPolynomial center _ K hK]
  · intro l
    have hcoeff := aeval_map_commonTaylorNumeratorOver_reconstruction φ
      (Polynomial.C center) Q K jet hS l
    simpa only [hcenter, hφ, hpoly] using hcoeff

end

end ReedSolomon
