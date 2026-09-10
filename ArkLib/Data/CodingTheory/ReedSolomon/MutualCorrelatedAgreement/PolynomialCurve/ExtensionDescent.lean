/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullAgreement
/-!
# Descending exact power-batching agreement

Restrict an extension-field exceptional set along the field embedding. Its size cannot
increase. Since the constituent tuple is already over the base field, both the polynomial
identity and equality of the entire agreement sets descend by injectivity.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n ℓ : ℕ}

private theorem agreementSet_map (domain : Fin n ↪ F) (ι : F →+* E)
    (y : Fin n → F) (Q : F[X]) :
    polynomialAgreementSet (mappedDomain domain ι) (fun i ↦ ι (y i)) (Q.map ι) =
      polynomialAgreementSet domain y Q := by
  ext i
  simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  change (Q.map ι).eval (ι (domain i)) = ι (y i) ↔ _
  rw [Polynomial.eval_map_apply]
  exact ι.injective.eq_iff

/-- Exact agreement of a base-field tuple descends from every extension field. -/
theorem HasExactPowerAgreement.descend (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E) (k : ℕ) (z : F) (Q : F[X])
    (h : HasExactPowerAgreement domain w ι k (ι z) (Q.map ι)) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q := by
  obtain ⟨P, hP, heq, hagree⟩ := h
  refine ⟨P, hP, ?_, ?_⟩
  · have hpoly : Q = powerBatchedPolynomial P z :=
      Polynomial.map_injective ι ι.injective (heq.trans (powerBatchedPolynomial_map P ι z).symm)
    simpa only [Polynomial.map_id, RingHom.id_apply] using hpoly
  · rw [powerBatchedWord_map, agreementSet_map] at hagree
    simpa [mappedDomain] using hagree

/-- An exceptional set chosen before all candidate polynomials descends with the same
cardinality bound and the same universal exact-agreement conclusion. -/
theorem exists_exceptional_powerAgreement_descend (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E) (k A : ℕ) (exceptional : Finset E)
    (hgood : ∀ z ∉ exceptional, ∀ Q : E[X], Q.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain ι)
        (powerBatchedWord (fun t i ↦ ι (w t i)) z) Q).card →
      HasExactPowerAgreement domain w ι k z Q) :
    ∃ baseExceptional : Finset F, baseExceptional.card ≤ exceptional.card ∧
      ∀ z ∉ baseExceptional, ∀ Q : F[X], Q.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
        HasExactPowerAgreement domain w (RingHom.id F) k z Q := by
  classical
  let baseExceptional := exceptional.preimage ι ι.injective.injOn
  refine ⟨baseExceptional, ?_, ?_⟩
  · apply Finset.card_le_card_of_injOn ι
    · intro z hz
      exact Finset.mem_preimage.mp hz
    · exact ι.injective.injOn
  · intro z hz Q hdegree hagree
    apply HasExactPowerAgreement.descend domain w ι k z Q
    apply hgood (ι z)
    · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
    · exact Polynomial.degree_map_le.trans_lt hdegree
    · rw [powerBatchedWord_map, agreementSet_map]
      exact hagree

end ReedSolomon
