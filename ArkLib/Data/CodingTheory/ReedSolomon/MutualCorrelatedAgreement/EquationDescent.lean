/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.Extension
/-!
# Descending equation-restricted correlated agreement

Mapping coefficients commutes with challenge and differential specialization. Consequently,
an exceptional set over an extension descends even when its transfer theorem applies only
to polynomial roots of a symbolic equation.
-/

@[expose] public section

open PolynomialDifferential Polynomial
namespace ReedSolomon.HiddenDerivative

variable {F E : Type*} [Field F] [Field E] {r : ℕ}

theorem challengeSpecialization_map_coefficients (ι : F →+* E)
    (Q : DifferentialPolynomial F[X] r) (z : F) :
    challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom ι) Q) (ι z) =
      MvPolynomial.map ι (challengeSpecialization Q z) := by
  unfold challengeSpecialization
  rw [MvPolynomial.map_map, MvPolynomial.map_map]
  have hc : (Polynomial.aeval (ι z)).toRingHom.comp (Polynomial.mapRingHom ι) =
      ι.comp (Polynomial.aeval z).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  rw [hc]

theorem map_symbolicDifferentialSpecialization (ι : F →+* E)
    (Q : DifferentialPolynomial F[X] r) (z : F) (P : F[X]) :
    (differentialSpecialization (challengeSpecialization Q z) P).map ι =
      differentialSpecialization
        (challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom ι) Q) (ι z))
        (P.map ι) := by
  rw [challengeSpecialization_map_coefficients, map_differentialSpecialization]

/-- Extension of scalar coefficients preserves a uniform challenge-height bound. -/
theorem ChallengeHeightLE.map_coefficients (ι : F →+* E)
    {Q : DifferentialPolynomial F[X] r} {h : ℕ} (hQ : ChallengeHeightLE Q h) :
    ChallengeHeightLE (MvPolynomial.map (Polynomial.mapRingHom ι) Q) h := by
  intro m
  rw [MvPolynomial.coeff_map]
  exact Polynomial.natDegree_map_le.trans (hQ m)

end ReedSolomon.HiddenDerivative

namespace ReedSolomon

open HiddenDerivative

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n r : ℕ}

/-- Descend an equation-restricted transfer, preserving the same finite exceptional budget. -/
theorem exists_exceptional_equation_correlatedAgreement_descend
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial F[X] r) (k A : ℕ) (exceptional : Finset E)
    (hgood : ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain ι)
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
          (fun i ↦ ι (f i + z * g i)) := by funext i; simp
      rw [hline, polynomialAgreementSet_map]
      exact hagree
    · rw [← map_symbolicDifferentialSpecialization, hroot, Polynomial.map_zero]

end ReedSolomon
