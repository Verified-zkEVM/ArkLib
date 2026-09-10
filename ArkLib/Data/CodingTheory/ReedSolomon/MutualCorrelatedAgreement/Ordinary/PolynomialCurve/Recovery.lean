/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExceptionalSet
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.GraphCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.UniformPowerAgreement
/-!
# All-characteristic recovery for polynomial curves

This file gives the characteristic-free baseline recovery theorem for the received curve
`z ↦ ∑ t, z ^ t.val • w t`.  It retains every tuple obtained by interpolating the constituents
on a common `k`-sample.  Thus one exceptional set, chosen before the challenge and candidate,
works for every close degree-`< k` polynomial.  The exceptional budget is linear in the curve
degree `ℓ`; sharpening the number of retained tuples is a separate incidence problem.

The conclusion is `HasExactPowerAgreement`, so it includes the polynomial identity and equality
of the complete agreement set.  No restriction on the characteristic or on `ℓ` is used.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F] {n k L ℓ : ℕ}

/-- Package extension-field exact recovery as a base-field uniform certificate.  Restricting the
exceptional set along the field embedding cannot increase its cardinality, and the full
polynomial identity and agreement-set equality descend by injectivity. -/
theorem uniformExactPowerAgreement_descend
    {E : Type*} [Field E] [DecidableEq E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (k L exceptionalCount : ℕ)
    (h : ∃ exceptional : Finset E, exceptional.card ≤ exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ Q : E[X], Q.degree < k →
        L ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (powerBatchedWord (fun t i ↦ ι (w t i)) z) Q).card →
        HasExactPowerAgreement domain w ι k z Q) :
    UniformExactPowerAgreement domain w k L exceptionalCount := by
  obtain ⟨exceptional, hcard, hgood⟩ := h
  obtain ⟨baseExceptional, hbaseCard, hbaseGood⟩ :=
    exists_exceptional_powerAgreement_descend domain w ι k L exceptional hgood
  exact ⟨baseExceptional, hbaseCard.trans hcard, hbaseGood⟩

/-- Retaining every common-sample interpolant gives unconditional exact recovery over an
arbitrary field.  The exceptional set precedes the challenge and every candidate polynomial.

The bound is a characteristic-free baseline: at most `n.choose k` tuples are retained, and each
tuple contributes at most `ℓ * (n - k)` accidental challenges. -/
theorem uniformExactPowerAgreement_of_all_samples
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (hkL : k ≤ L) :
    UniformExactPowerAgreement domain w k L (n.choose k * (ℓ * (n - k))) := by
  classical
  let family := polynomialTupleFamily domain w k
  have hdegree : ∀ P ∈ family, ∀ t, (P t).degree < k := by
    intro P hP
    exact ((mem_polynomialTupleFamily_iff domain w P k).mp hP).1
  have hcommon : ∀ P ∈ family, k ≤ (commonCurveAgreementSet domain w P).card := by
    intro P hP
    exact ((mem_polynomialTupleFamily_iff domain w P k).mp hP).2
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_family
      (k := k) (L := k) domain w (RingHom.id F) family hdegree hcommon
  refine ⟨exceptional, ?_, ?_⟩
  · exact hcard.trans (Nat.mul_le_mul_right _ (polynomialTupleFamily_card_le domain w k))
  · intro z hz Q hQdegree hAgreement
    have hkAgreement : k ≤
        (polynomialAgreementSet domain (powerBatchedWord w z) Q).card :=
      hkL.trans hAgreement
    obtain ⟨sample, hsampleSubset, hsampleCard⟩ :=
      Finset.exists_subset_card_eq hkAgreement
    obtain ⟨P, hPdegree, hPsample, hPidentity⟩ :=
      exists_polynomialGraph_of_sample domain w k sample hsampleCard
    have hPcommon : k ≤ (commonCurveAgreementSet domain w P).card := by
      rw [← hsampleCard]
      apply Finset.card_le_card
      intro i hi
      simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hPsample i hi
    have hPmem : P ∈ family := by
      exact (mem_polynomialTupleFamily_iff domain w P k).mpr ⟨hPdegree, hPcommon⟩
    have hQsample : ∀ i ∈ sample,
        Q.eval ((RingHom.id F) (domain i)) = ∑ t, z ^ t.val * (RingHom.id F) (w t i) := by
      intro i hi
      have hiAgreement := hsampleSubset hi
      have hiEq := (Finset.mem_filter.mp hiAgreement).2
      simpa only [RingHom.id_apply, powerBatchedWord] using hiEq
    have hQidentity : Q = powerBatchedPolynomial P z := by
      simpa only [Polynomial.map_id, RingHom.id_apply] using
        hPidentity (RingHom.id F) z Q hQdegree hQsample
    simpa only [Polynomial.map_id, RingHom.id_apply, hQidentity] using
      hgood P hPmem z hz

end ReedSolomon
