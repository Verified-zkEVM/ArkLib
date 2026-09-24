/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.Polynomial.Differential.TaylorChart
/-!
# Symbolic point recognition for power-batched polynomial graphs

A sample of agreement cuts determines a tuple of base-field polynomials. At every regular
specialization of a symbolic Taylor chart satisfying the high cuts and sample equations, the
reconstructed polynomial is the power-batched polynomial from that tuple. The result also
identifies its initial jet and cleared Taylor coefficients.

## Main statements

* `commonCurveAgreementSet_map` and `exists_exceptional_powerBatched_extension`: scalar extension
  preserves common agreement positions and transfers the exceptional-challenge bound for any
  finite coordinate type.
* `powerBatchedJetGraph` and `polynomialJet_powerBatched`: initial jets commute with power
  batching.
* `exists_polynomialGraph_of_symbolic_sample_of_exponent`: symbolic Taylor cuts recognize the
  polynomial graph determined by the sample.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial PolynomialDifferential

noncomputable section

variable {F E α : Type*} [Field F] [Field E] {k K r ℓ : ℕ}

open Classical in
/-- Scalar extension preserves exactly the common agreement positions of a polynomial tuple. -/
theorem commonCurveAgreementSet_map [Fintype α] (domain : α ↪ F)
    (w : Fin (ℓ + 1) → α → F) (P : Fin (ℓ + 1) → F[X]) (iota : F →+* E) :
    commonCurveAgreementSet (domain.trans ⟨iota, iota.injective⟩) (fun t i ↦ iota (w t i))
      (fun t ↦ (P t).map iota) = commonCurveAgreementSet domain w P := by
  classical
  ext i
  simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, iota.injective.eq_iff]

open Classical in
/-- A retained polynomial tuple costs at most `ℓ(|α|-L)` exceptional challenges over an
extension. Outside them, the full agreement set equals the base-field common agreement set. -/
theorem exists_exceptional_powerBatched_extension [Fintype α] (domain : α ↪ F)
    (w : Fin (ℓ + 1) → α → F) (P : Fin (ℓ + 1) → F[X]) (iota : F →+* E)
    (L : ℕ) (hcommon : L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset E, exceptional.card ≤ ℓ * (Fintype.card α - L) ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z)
          (powerBatchedPolynomial (fun t ↦ (P t).map iota) z) =
        commonCurveAgreementSet domain w P := by
  have hmap := commonCurveAgreementSet_map domain w P iota
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_powerBatched_agreement
    (domain.trans ⟨iota, iota.injective⟩) (fun t i ↦ iota (w t i))
    (fun t ↦ (P t).map iota) L (by rw [hmap]; exact hcommon)
  refine ⟨exceptional, ?_, fun z hz ↦ (hgood z hz).trans hmap⟩
  simpa using hcard

/-- The polynomial initial-jet graph associated with a tuple of messages. -/
def powerBatchedJetGraph (center : E) (P : Fin (ℓ + 1) → E[X]) :
    Fin (r + 1) → E[X] :=
  fun j ↦ powerBatchedCoordinate (fun t ↦ polynomialJet (d := r) center (P t) j)

/-- Initial Hasse jets commute with the entire power combination. -/
theorem polynomialJet_powerBatched (center z : E) (P : Fin (ℓ + 1) → E[X]) :
    polynomialJet (d := r) center (powerBatchedPolynomial P z) =
      fun j ↦ (powerBatchedJetGraph (r := r) center P j).eval z := by
  funext j
  rw [powerBatchedJetGraph, powerBatchedCoordinate_eval]
  simp only [polynomialJet, powerBatchedPolynomial, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- A common sample recognizes every regular specialized Taylor-chart point as belonging to one
base-field polynomial graph. The conclusion identifies the reconstructed polynomial, its initial
jet, and each cleared Taylor coefficient. -/
theorem exists_polynomialGraph_of_symbolic_sample_of_exponent
    (domain : α ↪ F) (w : Fin (ℓ + 1) → α → F)
    (sample : Finset α) (hsample : sample.card = k)
    (ι : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = w t i) ∧
      ∀ (z : E) (jet : Fin (r + 1) → E),
        MvPolynomial.aeval jet (initialJetSeparant center
          (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0 →
        (∀ l : Fin K, k ≤ l.val →
          MvPolynomial.aeval jet (commonTaylorNumerator center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) τ l.val) = 0) →
        (∀ i ∈ sample,
          MvPolynomial.aeval jet (taylorAgreementEquation center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) K τ (ι (domain i))
            (Polynomial.eval z (powerBatchedCoordinate (fun t ↦ ι (w t i))))) = 0) →
        rationalTaylorPolynomial center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) K jet =
            powerBatchedPolynomial (fun t ↦ (P t).map ι) z ∧
        jet = (fun j ↦
          Polynomial.eval z
            (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι) j)) ∧
        ∀ l : Fin K,
          MvPolynomial.aeval jet (commonTaylorNumerator center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) τ l.val) =
          MvPolynomial.aeval jet (initialJetSeparant center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ^ τ *
            (Polynomial.taylor center
              (powerBatchedPolynomial (fun t ↦ (P t).map ι) z)).coeff l.val := by
  obtain ⟨P, hP, hs, hrecognize⟩ :=
    exists_polynomialGraph_of_sample domain w sample hsample
  refine ⟨P, hP, hs, ?_⟩
  intro z jet hS hhigh hcuts
  let Qz : DifferentialPolynomial E r := MvPolynomial.map (Polynomial.evalRingHom z) Q
  have hS' : MvPolynomial.aeval jet (initialJetSeparant center Qz) ≠ 0 := by
    simpa [Qz] using hS
  have hhigh' : ∀ l, k ≤ l → l < K →
      MvPolynomial.aeval jet (commonTaylorNumerator center Qz τ l) = 0 := by
    intro l hkl hlK
    simpa [Qz] using hhigh ⟨l, hlK⟩ hkl
  have hdegree : (rationalTaylorPolynomial center Qz K jet).degree < k :=
    degree_rationalTaylorPolynomial_lt center Qz hτ k jet hS' hhigh'
  have hcuts' : ∀ i ∈ sample,
      MvPolynomial.aeval jet (taylorAgreementEquation center Qz K τ (ι (domain i))
        (Polynomial.eval z (powerBatchedCoordinate (fun t ↦ ι (w t i))))) = 0 := by
    intro i hi
    simpa [Qz] using hcuts i hi
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center Qz K jet).eval (ι (domain i)) =
        ∑ t, z ^ t.val * ι (w t i) := by
    intro i hi
    have heval := (taylorAgreementEquation_eq_zero_iff center Qz hτ jet hS'
      (ι (domain i)) (Polynomial.eval z (powerBatchedCoordinate (fun t ↦ ι (w t i))))).mp
        (hcuts' i hi)
    rw [powerBatchedCoordinate_eval] at heval
    exact heval
  have hpoly := hrecognize ι z _ hdegree hagree
  refine ⟨hpoly, ?_, ?_⟩
  · rw [← polynomialJet_powerBatched, ← hpoly,
      polynomialJet_rationalTaylorPolynomial center Qz hK]
  · intro l
    have hcoeff := aeval_commonTaylorNumerator center Qz jet (hτ l) hS'
    simpa [Qz, ← hpoly, rationalTaylorPolynomial,
      Polynomial.coeff_taylor_centeredCoefficientPrefix, l.isLt] using hcoeff

end

end ReedSolomon
