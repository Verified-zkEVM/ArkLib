/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Agreement
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
/-!
# Polynomial-graph recognition in the symbolic Taylor chart

A sample of `k` agreement cuts determines a base-field polynomial tuple. Every regular
Taylor-chart point satisfying the high-coefficient cuts and that sample reconstructs the
power combination of this same tuple. The result uses actual Taylor numerators and cuts,
not an assumed graph-recognition property.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.6 (Theorem 5.14), recognition of polynomial graphs.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

variable {F E : Type*} [Field F] [Field E] {n k K r ℓ : ℕ}

/-- Scalar extension preserves exactly the common agreement positions of a tuple. -/
theorem commonCurveAgreementSet_map (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P : Fin (ℓ + 1) → F[X]) (ι : F →+* E) :
    commonCurveAgreementSet (mappedDomain domain ι) (fun t i ↦ ι (w t i))
      (fun t ↦ (P t).map ι) = commonCurveAgreementSet domain w P := by
  classical
  ext i
  simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
    mappedDomain, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
    Polynomial.eval_map, Polynomial.eval₂_at_apply, ι.injective.eq_iff]

open Classical in
/-- A retained base-field tuple costs at most `ℓ(n-L)` exceptional challenges over any
extension field. Outside them, the full agreement set equals the base-field common set. -/
theorem exists_exceptional_powerBatched_extension (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P : Fin (ℓ + 1) → F[X]) (ι : F →+* E)
    (L : ℕ) (hcommon : L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset E, exceptional.card ≤ ℓ * (n - L) ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet (mappedDomain domain ι)
          (powerBatchedWord (fun t i ↦ ι (w t i)) z)
          (powerBatchedPolynomial (fun t ↦ (P t).map ι) z) =
        commonCurveAgreementSet domain w P := by
  have hm := commonCurveAgreementSet_map domain w P ι
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_powerBatched_agreement
    (mappedDomain domain ι) (fun t i ↦ ι (w t i)) (fun t ↦ (P t).map ι) L
    (by rw [hm]; exact hcommon)
  exact ⟨exceptional, hcard, fun z hz ↦ (hgood z hz).trans hm⟩

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

/-- A common sample recognizes every regular Taylor-chart point as belonging to one
base-field polynomial graph. This also identifies all cleared Taylor coefficients. -/
theorem exists_polynomialGraph_of_symbolic_sample_of_exponent
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (ι : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = w t i) ∧
      ∀ (z : E) (jet : Fin (r + 1) → E),
        aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
          (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 →
        (∀ l : Fin K, k ≤ l.val →
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))) = 0) →
        (∀ i ∈ sample,
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (ι (domain i)))
              (powerBatchedCoordinate (fun t ↦ ι (w t i))) (τ := τ))) = 0) →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K jet =
            powerBatchedPolynomial (fun t ↦ (P t).map ι) z ∧
        jet = (fun j ↦ (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι) j).eval z) ∧
        ∀ l : Fin K,
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))) =
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (initialJetSeparantOver (Polynomial.C center) Q)) ^ τ *
            (Polynomial.taylor center
              (powerBatchedPolynomial (fun t ↦ (P t).map ι) z)).coeff l.val := by
  obtain ⟨P, hP, hs, hrecognize⟩ := exists_polynomialGraph_of_sample domain w k sample hsample
  refine ⟨P, hP, hs, ?_⟩
  intro z jet hS hhigh hcuts
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by ext a <;> simp [φ]
  have hdegree :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).degree < k := by
    simpa only [hcenter, hφ] using
      degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
        φ (Polynomial.C center) Q K k τ hτ jet hS hhigh
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).eval (ι (domain i)) = ∑ t, z ^ t.val * ι (w t i) := by
    intro i hi
    have heval := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent φ
      (Polynomial.C center) Q K τ hτ jet hS (Polynomial.C (ι (domain i)))
      (powerBatchedCoordinate (fun t ↦ ι (w t i)))).mp (hcuts i hi)
    simpa only [hφ, hcenter, φ, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id, Polynomial.eval_C, powerBatchedCoordinate_eval] using heval
  have hpoly := hrecognize ι z _ hdegree hagree
  refine ⟨hpoly, ?_, ?_⟩
  · rw [← polynomialJet_powerBatched, ← hpoly,
      polynomialJet_rationalTaylorPolynomial center _ K hK]
  · intro l
    have hcoeff := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ
      (Polynomial.C center) Q K τ hτ jet hS l
    simpa only [hcenter, hφ, hpoly] using hcoeff


end ReedSolomon
