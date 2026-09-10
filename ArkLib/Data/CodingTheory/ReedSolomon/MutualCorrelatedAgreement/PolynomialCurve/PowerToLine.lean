/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Symbolic.RegularEquation
/-!
# Recovering exact line agreement from degree-one power batching

At batching degree one the two weights are `1,z`. Exact power agreement therefore recovers
precisely the pair required by the line theorem, including equality of the entire agreement
sets. This bridge lets a finite curve certificate feed the existing affine-space and
interleaving theorems without repeating their probability arguments.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n k : ℕ}

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
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k A : ℕ} (domain : Fin n ↪ F) (B : ℚ)
    (hpower : ∀ w : Fin 2 → Fin n → F, ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ B ∧ ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord (ℓ := 1) w z) Q).card →
        HasExactPowerAgreement domain w (RingHom.id F) k z Q) :
    LineExactAgreementBound domain k A B := by
  intro f g
  obtain ⟨ex, hcard, hgood⟩ := hpower ![f, g]
  refine ⟨ex, ?_, ?_⟩
  · exact_mod_cast hcard
  · intro z hz Q hdeg hagree
    have hw : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    have h := hgood z hz Q hdeg (by rwa [hw])
    obtain ⟨pair, hp0, hp1, hQ, heq⟩ :=
      exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z Q h
    refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using hQ
    · simpa [mappedDomain] using heq

end ReedSolomon
