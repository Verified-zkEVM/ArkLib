/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.GraphCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.UniformPowerAgreement
/-!
# Exact polynomial-curve agreement at full message dimension

At message dimension and agreement threshold equal to the block length, interpolate every
constituent received word on the full evaluation domain. Every qualifying candidate is exactly
the corresponding power combination, and every coordinate is a common agreement. Thus the
exceptional set is empty over every field and in every characteristic.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- At full message dimension, one tuple of interpolants explains every full-agreement
candidate on a polynomial received curve, with equality of complete agreement sets. -/
theorem exists_exactPower_fullDimension (n ℓ : ℕ)
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < n) ∧
      ∀ z (Q : F[X]), Q.degree < n →
        n ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
        HasExactPowerAgreement domain w (RingHom.id F) n z Q := by
  classical
  obtain ⟨P, hP, hsample, hrecognize⟩ :=
    exists_polynomialGraph_of_sample domain w n Finset.univ (by simp)
  refine ⟨P, hP, ?_⟩
  intro z Q hQ hcard
  have hfull : polynomialAgreementSet domain (powerBatchedWord w z) Q = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hupper : (polynomialAgreementSet domain (powerBatchedWord w z) Q).card ≤ n := by
      simpa using (polynomialAgreementSet domain (powerBatchedWord w z) Q).card_le_univ
    simpa using Nat.le_antisymm hupper hcard
  have heval : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Q.eval (domain i) = ∑ t, z ^ t.val * w t i := by
    intro i hi
    have hmem : i ∈ polynomialAgreementSet domain (powerBatchedWord w z) Q := by
      rw [hfull]
      exact hi
    simpa only [powerBatchedWord] using (Finset.mem_filter.mp hmem).2
  refine ⟨P, hP, ?_, ?_⟩
  · simpa only [Polynomial.map_id, RingHom.id_apply] using
      hrecognize (RingHom.id F) z Q hQ (by simpa using heval)
  · have hfullMapped :
        polynomialAgreementSet (mappedDomain domain (RingHom.id F))
          (powerBatchedWord (fun t i ↦ (RingHom.id F) (w t i)) z) Q = Finset.univ := by
      simpa [mappedDomain] using hfull
    rw [hfullMapped]
    symm
    apply Finset.eq_univ_of_forall
    intro i
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsample i (Finset.mem_univ i)

/-- Full-dimension polynomial-curve MCA has an empty exceptional set over every field. -/
theorem uniformExactPowerAgreement_fullDimension (n ℓ : ℕ)
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) :
    UniformExactPowerAgreement domain w n n 0 := by
  obtain ⟨P, hP, hgood⟩ := exists_exactPower_fullDimension n ℓ domain w
  refine ⟨∅, by simp, ?_⟩
  intro z _ Q hQ hcard
  exact hgood z Q hQ hcard

end

end ReedSolomon
