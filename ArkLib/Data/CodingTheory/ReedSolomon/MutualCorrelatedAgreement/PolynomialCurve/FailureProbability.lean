/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
/-!
# The probability controlled by an exact power-agreement exceptional set

Failure means that some sufficiently close polynomial has no exact correlated tuple.
The candidate is chosen after the challenge, so this event expresses the simultaneous
agreement guarantee. A uniform exceptional set contains this entire event. Its cardinality
therefore bounds the failure probability under one uniform field challenge.

This is a local coding-theoretic probability. It does not assume independence from another
protocol phase or combine Fiat--Shamir and commitment errors.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped ProbabilityTheory ENNReal

namespace ReedSolomon

variable {F : Type} [Field F] [DecidableEq F] {n ell k A : ℕ}

/-- A challenge with a close polynomial lacking exact correlated-tuple agreement. -/
def PowerAgreementFailure (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F) (k A : ℕ) (z : F) : Prop :=
  ∃ Q : F[X], Q.degree < k ∧
    A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) Q).card ∧
    ¬ HasExactPowerAgreement domain values (RingHom.id F) k z Q

open Classical in
/-- The full failure event is contained in any uniform exact-agreement exceptional set. -/
theorem powerAgreementFailure_card_le [Fintype F]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (exceptional : Finset F)
    (hgood : ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k →
      A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) Q).card →
      HasExactPowerAgreement domain values (RingHom.id F) k z Q) :
    (Finset.univ.filter (PowerAgreementFailure domain values k A)).card ≤ exceptional.card := by
  apply Finset.card_le_card
  intro z hz
  by_contra hzout
  obtain ⟨Q, hdegree, hagree, hfail⟩ := (Finset.mem_filter.mp hz).2
  exact hfail (hgood z hzout Q hdegree hagree)

open Classical in
/-- A proved exceptional count divided by the field size bounds uniform-challenge failure. -/
theorem probability_powerAgreementFailure_le [Fintype F]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (exceptional : Finset F) (B : ℚ) (hcard : (exceptional.card : ℚ) ≤ B)
    (hgood : ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k →
      A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) Q).card →
      HasExactPowerAgreement domain values (RingHom.id F) k z Q) :
    Pr_{let z ←$ᵖ F}[PowerAgreementFailure domain values k A z] ≤
      ENNReal.ofReal ((B : ℝ) / (Fintype.card F : ℝ)) := by
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hbad := powerAgreementFailure_card_le domain values exceptional hgood
  exact (show
    ((Finset.univ.filter (PowerAgreementFailure domain values k A)).card : ℝ) ≤
      (exceptional.card : ℝ) by exact_mod_cast hbad).trans (by exact_mod_cast hcard)

end ReedSolomon
