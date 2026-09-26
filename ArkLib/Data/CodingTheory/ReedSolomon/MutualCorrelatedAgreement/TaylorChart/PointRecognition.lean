/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition

/-!
# Graph-line recognition on symbolic Taylor charts

A sample of agreement equations and high Taylor cuts determines one pair of polynomials over the
received words' base field. At every regular symbolic chart point satisfying those equations, the
reconstructed polynomial is the affine combination of that same pair, and its jet and cleared
Taylor coefficients satisfy the corresponding identities.

## Main statements

* `ReedSolomon.exists_graphLine_pair_of_symbolic_sample_of_exponent`: one sample determines a
  base-field pair for every sufficient common exponent.

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
  obtain ⟨P, hP, hsampleP, hrecognize⟩ :=
    exists_polynomialGraph_of_symbolic_sample_of_exponent (ℓ := 1)
      domain ![f, g] sample hsample iota center Q hK τ hτ
  refine ⟨P 0, P 1, hP 0, hP 1, ?_, ?_⟩
  · intro i hi
    exact ⟨by simpa using hsampleP i hi 0, by simpa using hsampleP i hi 1⟩
  · intro z jet hS hhigh hcuts
    let φ : E[X] →ₐ[E] E := Polynomial.aeval z
    have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
      ext a <;> simp [φ, Polynomial.evalRingHom]
    have hS' : aeval jet (initialJetSeparant center (map (Polynomial.evalRingHom z) Q))
        ≠ 0 := by
      rw [← hφ, map_initialJetSeparant] at hS
      simpa [φ] using hS
    have hhigh' : ∀ l : Fin K, k ≤ l.val →
        aeval jet (commonTaylorNumerator center
          (map (Polynomial.evalRingHom z) Q) τ l.val) = 0 := by
      intro l hl
      have hh := hhigh l hl
      rw [← hφ, map_commonTaylorNumeratorOver_eq] at hh
      simpa [φ] using hh
    have hcuts' : ∀ i ∈ sample,
        aeval jet (taylorAgreementEquation center
          (map (Polynomial.evalRingHom z) Q) K τ (iota (domain i))
          ((powerBatchedCoordinate (fun t ↦ iota (![f, g] t i))).eval z)) = 0 := by
      intro i hi
      have hc := hcuts i hi
      rw [← hφ, map_taylorAgreementEquationOver_eq] at hc
      simpa [φ, powerBatchedCoordinate, Fin.sum_univ_two] using hc
    obtain ⟨hpoly, hjet, hcoeff⟩ := hrecognize z jet hS' hhigh' hcuts'
    refine ⟨?_, ?_, ?_⟩
    · simpa [powerBatchedPolynomial, Fin.sum_univ_two, Polynomial.smul_eq_C_mul]
        using hpoly
    · simpa [powerBatchedJetGraph, powerBatchedCoordinate_eval, Fin.sum_univ_two]
        using hjet
    · intro l
      have hc := hcoeff l
      have hNmap : map (Polynomial.evalRingHom z)
          (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val) =
          commonTaylorNumerator center (map (Polynomial.evalRingHom z) Q) τ l.val := by
        rw [← hφ, map_commonTaylorNumeratorOver_eq]
        simp [φ]
      have hSmap : map (Polynomial.evalRingHom z)
          (initialJetSeparant (Polynomial.C center) Q) =
          initialJetSeparant center (map (Polynomial.evalRingHom z) Q) := by
        rw [← hφ, map_initialJetSeparant]
        simp [φ]
      rw [hNmap, hSmap]
      simpa [powerBatchedPolynomial, Fin.sum_univ_two,
        Polynomial.smul_eq_C_mul] using hc


end

end ReedSolomon
