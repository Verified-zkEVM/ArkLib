/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.ToMathlib.Polynomial.SparseContraction
/-!
# Point recognition for power-batched polynomial graphs

A sample of agreement positions determines a tuple of base-field polynomials. Sparse Frobenius
pullbacks agreeing with the associated power-batched word on the sample are recognized from their
values at roots of the evaluation points. Symbolic Taylor charts also identify the initial jet and
cleared Taylor coefficients of the reconstructed polynomial.

## Main statements

* `commonCurveAgreementSet_map` and `exists_exceptional_powerBatched_extension`: scalar extension
  preserves common agreement positions and transfers the exceptional-challenge bound for any
  finite coordinate type.
* `exists_exceptional_exactPowerAgreement` and `exists_exceptional_exactPowerAgreement_family`:
  exact power agreement outside a bounded exceptional set for a tuple or a finite family.
* `exists_frobeniusPowerGraph_polynomials_of_sample`: a sample recognizes sparse Frobenius
  pullbacks of power-batched polynomial graphs.
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

variable {F E α : Type*} [Field F] [Field E] {k K r ℓ L : ℕ}

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

open Classical in
/-- A degree-bounded tuple with at least `L` common agreements has exact power agreement outside
at most `ℓ * (|α| - L)` extension-field challenges. -/
theorem exists_exceptional_exactPowerAgreement [Fintype α] (domain : α ↪ F)
    (w : Fin (ℓ + 1) → α → F) (P : Fin (ℓ + 1) → F[X]) (iota : F →+* E)
    (hdegree : ∀ t, (P t).degree < k)
    (hcommon : L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset E, exceptional.card ≤ ℓ * (Fintype.card α - L) ∧
      ∀ z ∉ exceptional, HasExactPowerAgreement domain w iota k z
        (powerBatchedPolynomial (fun t ↦ (P t).map iota) z) := by
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_exceptional_powerBatched_extension domain w P iota L hcommon
  exact ⟨ex, hcard, fun z hz ↦ ⟨P, hdegree, rfl, hgood z hz⟩⟩

open Classical in
/-- One exceptional set gives exact power agreement for every tuple in a finite family, with
size at most `family.card * ℓ * (|α| - L)`. -/
theorem exists_exceptional_exactPowerAgreement_family [Fintype α] (domain : α ↪ F)
    (w : Fin (ℓ + 1) → α → F) (iota : F →+* E)
    (family : Finset (Fin (ℓ + 1) → F[X]))
    (hdegree : ∀ P ∈ family, ∀ t, (P t).degree < k)
    (hcommon : ∀ P ∈ family, L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ family.card * (ℓ * (Fintype.card α - L)) ∧
      ∀ P ∈ family, ∀ z ∉ exceptional,
        HasExactPowerAgreement domain w iota k z
          (powerBatchedPolynomial (fun t ↦ (P t).map iota) z) := by
  classical
  let domainE := domain.trans ⟨iota, iota.injective⟩
  let wordsE := fun t i ↦ iota (w t i)
  let mapTuple (P : Fin (ℓ + 1) → F[X]) : Fin (ℓ + 1) → E[X] :=
    fun t ↦ (P t).map iota
  let familyE := family.image mapTuple
  have hcommonE : ∀ P ∈ familyE,
      L ≤ (commonCurveAgreementSet domainE wordsE P).card := by
    intro P hP
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    rw [commonCurveAgreementSet_map]
    exact hcommon P₀ hP₀
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_exceptional_powerBatched_family domainE wordsE familyE L hcommonE
  refine ⟨ex, hcard.trans (Nat.mul_le_mul_right _ Finset.card_image_le), ?_⟩
  intro P hP z hz
  refine ⟨P, hdegree P hP, rfl, ?_⟩
  have hset := hgood (mapTuple P) (Finset.mem_image.mpr ⟨P, hP, rfl⟩) z hz
  simpa only [domainE, wordsE, familyE, mapTuple] using
    hset.trans (commonCurveAgreementSet_map domain w P iota)

/-- A sample of `k` positions recognizes a sparse Frobenius pullback of the power-batched
polynomial graph. The root and value conditions are needed only on the sample. -/
theorem exists_frobeniusPowerGraph_polynomials_of_sample
    (domain : α ↪ F) (w : Fin (ℓ + 1) → α → F)
    (sample : Finset α) (hsample : sample.card = k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = w t i) ∧
      ∀ {E : Type*} [Field E] (ι : F →+* E) (p e : ℕ) [ExpChar E p]
        (roots : α → E) (center z : E) (Q : E[X]),
        (∀ i ∈ sample, roots i ^ (p ^ e) = ι (domain i)) →
        Q.degree < ↑(p ^ e * k) →
        (∀ j : ℕ, ¬p ^ e ∣ j → (taylor center Q).coeff j = 0) →
        (∀ i ∈ sample,
          Q.eval (roots i) = ∑ t, z ^ (p ^ e * t.val) * ι (w t i)) →
        Q = expand E (p ^ e)
            (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) ∧
          Q.eval center =
            (powerBatchedPolynomial (fun t ↦ (P t).map ι)
              (z ^ (p ^ e))).eval (center ^ (p ^ e)) := by
  obtain ⟨P, hPdegree, hPsample, hrecognize⟩ :=
    exists_polynomialGraph_of_sample domain w sample hsample
  refine ⟨P, hPdegree, hPsample, ?_⟩
  intro E _ ι p e _ roots center z Q hroots hdegree hsparse hagree
  obtain ⟨R, ⟨hRdegree, hRQ⟩, _⟩ :=
    existsUnique_expand_of_sparse_taylor p e k Q center hsparse hdegree
  have hRagree : ∀ i ∈ sample,
      R.eval (domain.trans ⟨ι, ι.injective⟩ i) =
        ∑ t, (z ^ (p ^ e)) ^ t.val * ι (w t i) := by
    intro i hi
    have hiAgree := hagree i hi
    rw [← hRQ, expand_eval, hroots i hi] at hiAgree
    simpa only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, pow_mul]
      using hiAgree
  have hRidentity := hrecognize ι (z ^ (p ^ e)) R hRdegree hRagree
  constructor
  · rw [← hRQ, hRidentity]
  · rw [← hRQ, expand_eval, hRidentity]

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
