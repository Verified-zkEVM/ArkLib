/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Symbolic.RegularEquation
/-!
# Descending correlated agreement from an extension field

An extension-field exceptional set restricts to at most as many base-field challenges.
The constituent pair already lives in the base field, so injectivity of the field map
descends both the polynomial identity and equality of the full agreement sets.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n : ℕ}

/-- Field embeddings preserve the exact polynomial agreement set. -/
theorem polynomialAgreementSet_map (domain : Fin n ↪ F) (iota : F →+* E)
    (y : Fin n → F) (P : F[X]) :
    polynomialAgreementSet (mappedDomain domain iota) (fun i ↦ iota (y i)) (P.map iota) =
      polynomialAgreementSet domain y P := by
  ext i
  simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  change (P.map iota).eval (iota (domain i)) = iota (y i) ↔ _
  rw [Polynomial.eval_map_apply]
  exact iota.injective.eq_iff

/-- A correlated pair with base-field constituents descends along any field embedding. -/
theorem HasExactCorrelatedPair.descend (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (k : ℕ) (z : F) (P : F[X])
    (h : HasExactCorrelatedPair domain f g iota k (iota z) (P.map iota)) :
    HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨pair, hleft, hright, heq, hagree⟩ := h
  refine ⟨pair, hleft, hright, ?_, ?_⟩
  · apply Polynomial.map_injective iota iota.injective
    simpa [correlatedPairSpecialization] using heq
  · have hline : (fun i ↦ iota (f i) + iota z * iota (g i)) =
        (fun i ↦ iota (f i + z * g i)) := by
      funext i
      simp
    rw [hline, polynomialAgreementSet_map] at hagree
    simpa [mappedDomain] using hagree

/-- Pulling back a finite exceptional set preserves its cardinality upper bound and the
universal exact-agreement conclusion. The input exception is chosen before all witnesses. -/
theorem exists_exceptional_correlatedAgreement_descend
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (k A : ℕ) (exceptional : Finset E)
    (hgood : ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P).card →
      HasExactCorrelatedPair domain f g iota k z P) :
    ∃ baseExceptional : Finset F, baseExceptional.card ≤ exceptional.card ∧
      ∀ z ∉ baseExceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  let baseExceptional := exceptional.preimage iota iota.injective.injOn
  refine ⟨baseExceptional, ?_, ?_⟩
  · apply Finset.card_le_card_of_injOn iota
    · intro z hz
      exact Finset.mem_preimage.mp hz
    · exact iota.injective.injOn
  · intro z hz P hdegree hagree
    apply HasExactCorrelatedPair.descend domain f g iota k z P
    apply hgood (iota z)
    · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
    · exact Polynomial.degree_map_le.trans_lt hdegree
    · have hline : (fun i ↦ iota (f i) + iota z * iota (g i)) =
          (fun i ↦ iota (f i + z * g i)) := by funext i; simp
      rw [hline, polynomialAgreementSet_map]
      exact hagree

end ReedSolomon
