/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.Polynomial.Differential.BaseChange

/-!
# Descending equation-restricted correlated agreement

Suppose a symbolic differential equation over a field extension has an exceptional set outside
which every close root has an exact correlated-pair witness. Restricting the exceptional set to
the base field preserves its size bound, and roots of the specialized base equation map to roots
of the extension equation. The exact pair then descends to the base field. The same holds for
exact power agreement with a power-batched word.

## Main statements

* `ReedSolomon.exists_exceptional_equation_correlatedAgreement_descend`: equation-restricted
  exact correlated agreement descends with the same exceptional-set bound.
* `ReedSolomon.exists_exceptional_equation_powerAgreement_descend`: equation-restricted exact
  power agreement descends with the same exceptional-set bound.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon

open PolynomialDifferential

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n r : ℕ}

/-- A uniform exceptional-set transfer for roots of a symbolic differential equation descends
from an extension field with the same exceptional-set budget. -/
theorem exists_exceptional_equation_correlatedAgreement_descend
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial F[X] r) (k A : ℕ) (exceptional : Finset E)
    (hgood : ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι (f i) + z * ι (g i)) P).card →
      differentialSpecialization
        (challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom ι) Q) z) P = 0 →
      HasExactCorrelatedPair domain f g ι k z P) :
    ∃ baseExceptional : Finset F, baseExceptional.card ≤ exceptional.card ∧
      ∀ z ∉ baseExceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  let baseExceptional := exceptional.preimage ι ι.injective.injOn
  refine ⟨baseExceptional, ?_, ?_⟩
  · apply Finset.card_le_card_of_injOn ι
    · intro z hz
      exact Finset.mem_preimage.mp hz
    · exact ι.injective.injOn
  · intro z hz P hdegree hagree hroot
    apply HasExactCorrelatedPair.descend domain f g ι k z P
    apply hgood (ι z)
    · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
    · exact Polynomial.degree_map_le.trans_lt hdegree
    · have hline : (fun i ↦ ι (f i) + ι z * ι (g i)) =
          (fun i ↦ ι (f i + z * g i)) := by
        funext i
        simp
      rw [hline, polynomialAgreementSet_map]
      exact hagree
    · rw [← map_symbolicDifferentialSpecialization, hroot, Polynomial.map_zero]

/-- A uniform exceptional-set transfer to exact power agreement, for roots of a symbolic
differential equation, descends from an extension field with the same exceptional-set budget. -/
theorem exists_exceptional_equation_powerAgreement_descend {α : Type*} [Fintype α] {ℓ : ℕ}
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F) (ι : F →+* E)
    (Q : DifferentialPolynomial F[X] r) (k A : ℕ) (exceptional : Finset E)
    (hgood : ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
        (powerBatchedWord (fun t i ↦ ι (values t i)) z) P).card →
      differentialSpecialization
        (challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom ι) Q) z) P = 0 →
      HasExactPowerAgreement domain values ι k z P) :
    ∃ baseExceptional : Finset F, baseExceptional.card ≤ exceptional.card ∧
      ∀ z ∉ baseExceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  refine ⟨exceptional.preimage ι ι.injective.injOn,
    Finset.card_le_card_of_injOn ι (fun z hz ↦ Finset.mem_preimage.mp hz) ι.injective.injOn, ?_⟩
  intro z hz P hdegree hagree hroot
  apply HasExactPowerAgreement.descend (φ := ι)
  apply hgood (ι z)
  · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
  · exact Polynomial.degree_map_le.trans_lt hdegree
  · rwa [powerBatchedWord_map, polynomialAgreementSet_map]
  · rw [← map_symbolicDifferentialSpecialization, hroot, Polynomial.map_zero]

end ReedSolomon
