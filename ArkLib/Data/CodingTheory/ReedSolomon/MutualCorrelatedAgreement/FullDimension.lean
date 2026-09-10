/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
/-!
# Exact line agreement at full message dimension

When the message dimension and agreement threshold both equal the block length, interpolation
of the two received words gives one pair that explains every qualifying candidate at every
challenge. This handles the finite endpoint separately from ordinary transfer theorems whose
degree parameter is at most `n - 2`. No characteristic restriction is needed.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- At full message dimension, a single interpolated pair explains all full-agreement
candidates, with equality of complete agreement sets and no exceptional challenges. -/
theorem exists_exactPair_fullDimension (n : ℕ)
    {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ F₀ G₀ : F[X], F₀.degree < n ∧ G₀.degree < n ∧
      ∀ z (P : F[X]), P.degree < n →
        n ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF, hG, hsample, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample (k := n) domain f g Finset.univ (by simp)
  refine ⟨F₀, G₀, hF, hG, ?_⟩
  intro z P hP hcard
  have hfull : polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
      Finset.univ := by
    apply Finset.eq_univ_of_card
    have hupper : (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card ≤ n := by
      simpa using (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card_le_univ
    simpa using Nat.le_antisymm hupper hcard
  have heval : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      P.eval (domain i) = f i + z * g i := by
    intro i hi
    have hmem : i ∈ polynomialAgreementSet domain (fun i ↦ f i + z * g i) P := by
      rw [hfull]
      exact hi
    exact (Finset.mem_filter.mp hmem).2
  constructor
  · simpa [mappedDomain] using hrecognize (RingHom.id F) z P hP (by
      simpa [mappedDomain] using heval)
  · rw [hfull]
    symm
    apply Finset.eq_univ_of_forall
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsample i (Finset.mem_univ i)⟩

/-- Full-dimension line MCA has an empty exceptional set over every field. -/
theorem exists_exceptional_fullDimension_lineMCA (n : ℕ)
    {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ exceptional : Finset F, exceptional.card = 0 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < n →
        n ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < n ∧ G₀.degree < n ∧
          P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF, hG, hpair⟩ := exists_exactPair_fullDimension n domain f g
  exact ⟨∅, rfl, fun z _ P hP hcard ↦ ⟨F₀, G₀, hF, hG, hpair z P hP hcard⟩⟩

end

end ReedSolomon
