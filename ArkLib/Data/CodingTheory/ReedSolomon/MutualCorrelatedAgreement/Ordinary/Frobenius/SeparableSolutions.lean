/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.RegularSolutions
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.RootPresentation
/-!
# Choosing a common regular chart for ordinary witnesses
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

open Classical in
/-- A separable irreducible pulled factor controls every root after adding its actual
resultant exceptions to the regular incidence exceptions. -/
theorem exists_exceptional_frobeniusSeparableSolutions [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hb : 0 < b) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        (h * (1 + τ * (b - 1)) + b * (p ^ e + τ * h) : ℕ) *
          (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
            ((n - k) * b : ℕ) + ((2 * b - 1) * h : ℕ) ∧
      ∀ w ∉ exceptional, ∀ P : E[X],
        (expand E (p ^ e) P).degree < K →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (fun i ↦ ι (f i) + w ^ (p ^ e) * ι (g i)) P).card →
        HasExactCorrelatedPair domain f g ι k (w ^ (p ^ e)) P := by
  classical
  obtain ⟨regularEx, hregularCard, hregular⟩ := exists_exceptional_frobeniusRegularSolutions
    domain f g ι roots Q p e τ h b A hroots hK hKk hτ hτpos hb hkA hAn hheight hjet
  obtain ⟨singularEx, hsingularCard, hsingular⟩ := exists_exceptional_ordinary_separant
    hirr (by simpa only [hdegree] using hb) hder hheight
  refine ⟨regularEx ∪ singularEx, ?_, ?_⟩
  · have hcard : ((regularEx ∪ singularEx).card : ℚ) ≤
        regularEx.card + singularEx.card := by
      exact_mod_cast Finset.card_union_le regularEx singularEx
    have hsingularQ : (singularEx.card : ℚ) ≤ ((2 * b - 1) * h : ℕ) := by
      rw [hdegree] at hsingularCard
      exact_mod_cast hsingularCard
    linarith
  · intro w hw P hdeg hsol hagree
    have hw' := Finset.notMem_union.mp hw
    exact hregular w hw'.1 P hdeg hsol
      (hsingular w hw'.2 (expand E (p ^ e) P) hsol) hagree

end ReedSolomon
