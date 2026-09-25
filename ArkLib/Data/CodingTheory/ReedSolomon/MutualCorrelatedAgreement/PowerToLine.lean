/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
/-!
# Exact line agreement from degree-one power batching

At batching degree one, exact power agreement for two words is equivalent to an exact
correlated-pair witness. A uniform exact power guarantee therefore supplies the exact-agreement
interface for affine lines.

## Main statements

* `ReedSolomon.exactCorrelatedPair_of_powerAgreement_one`: degree-one exact power agreement gives
  an exact correlated-pair witness.
* `ReedSolomon.powerAgreement_one_of_exactCorrelatedPair`: an exact correlated-pair witness gives
  degree-one exact power agreement.
* `ReedSolomon.powerBatchedWord_pair_eq`: the degree-one power-batched word is the correlated line.
* `ReedSolomon.lineExactAgreementBound_of_powerAgreement_one`: a uniform degree-one power
  guarantee gives a uniform exact-agreement bound for lines.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

open Polynomial

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n k : ℕ}

omit [DecidableEq F] [DecidableEq E] in
/-- Degree-one power batching of two words is their correlated line. -/
theorem powerBatchedWord_pair_eq (f g : Fin n → F) (ι : F →+* E) (z : E) :
    powerBatchedWord (fun t i ↦ ι (![f, g] t i)) z =
      (fun i ↦ ι (f i) + z * ι (g i)) := by
  funext i
  simp [powerBatchedWord, Fin.sum_univ_two]

/-- An exact correlated-pair witness gives exact degree-one power agreement. -/
theorem powerAgreement_one_of_exactCorrelatedPair
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E) (z : E) (Q : E[X])
    (h : HasExactCorrelatedPair domain f g ι k z Q) :
    HasExactPowerAgreement domain ![f, g] ι k z Q := by
  obtain ⟨pair, hdeg0, hdeg1, hQ, hagree⟩ := h
  let P : Fin 2 → F[X] := ![pair.1, pair.2]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro t
    fin_cases t <;> assumption
  · simpa [P, powerBatchedPolynomial, correlatedPairSpecialization,
      Fin.sum_univ_two, Polynomial.smul_eq_C_mul] using hQ
  · rw [powerBatchedWord_pair_eq f g ι z]
    simpa [P, commonCurveAgreementSet, commonPolynomialAgreementSet,
      Fin.forall_fin_two] using hagree

/-- Exact power agreement for two constituents is exact correlated-pair agreement. -/
theorem exactCorrelatedPair_of_powerAgreement_one
    (domain : Fin n ↪ F) (w : Fin 2 → Fin n → F) (ι : F →+* E) (z : E) (Q : E[X])
    (h : HasExactPowerAgreement domain w ι k z Q) :
    HasExactCorrelatedPair domain (w 0) (w 1) ι k z Q := by
  obtain ⟨P, hdeg, hQ, hagree⟩ := h
  refine ⟨(P 0, P 1), hdeg 0, hdeg 1, ?_, ?_⟩
  · simpa [powerBatchedPolynomial, correlatedPairSpecialization, Fin.sum_univ_two,
      Polynomial.smul_eq_C_mul] using hQ
  · have hw : powerBatchedWord (fun t i ↦ ι (w t i)) z =
        (fun i ↦ ι (w 0 i) + z * ι (w 1 i)) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    rw [hw] at hagree
    simpa [commonCurveAgreementSet, commonPolynomialAgreementSet,
      Fin.forall_fin_two] using hagree

/-- A uniform two-constituent power theorem gives the scalar exact-line interface. -/
theorem lineExactAgreementBound_of_powerAgreement_one
    {F : Type} [Field F] [DecidableEq F]
    {n k A : ℕ} (domain : Fin n ↪ F) (B : ℝ)
    (hpower : ∀ w : Fin 2 → Fin n → F, ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ B ∧ ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord (ℓ := 1) w z) Q).card →
        HasExactPowerAgreement domain w (RingHom.id F) k z Q) :
    LineExactAgreementBound domain k A B := by
  intro f g
  obtain ⟨ex, hcard, hgood⟩ := hpower ![f, g]
  refine ⟨ex, hcard, ?_⟩
  intro z hz Q hdeg hagree
  have hw : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
    funext i
    simp [powerBatchedWord, Fin.sum_univ_two]
  have h := hgood z hz Q hdeg (by rwa [hw])
  obtain ⟨pair, hp0, hp1, hQ, heq⟩ :=
    exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z Q h
  refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
  · simpa [correlatedPairSpecialization] using hQ
  · simpa using heq

end ReedSolomon
