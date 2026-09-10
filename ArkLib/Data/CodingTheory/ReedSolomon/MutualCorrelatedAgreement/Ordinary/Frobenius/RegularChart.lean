/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.RegularBound
/-!
# Choosing a common regular chart for ordinary witnesses
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

private theorem span_singleton_ne_top_of_aeval_eq_zero {σ : Type*}
    (g : MvPolynomial σ E) (x : σ → E) (hx : aeval x g = 0) :
    Ideal.span ({g} : Set (MvPolynomial σ E)) ≠ ⊤ := by
  intro htop
  have hgunit : IsUnit g := Ideal.span_singleton_eq_top.mp htop
  have hevalunit : IsUnit (MvPolynomial.aeval x g) := hgunit.map (MvPolynomial.aeval x)
  rw [hx] at hevalunit
  exact not_isUnit_zero hevalunit

private theorem ordinary_source_initial_ne_zero_of_regular {r : ℕ} (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E)
    (hs : aeval jet (initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0) :
    symbolicSourceInitialEquation center Q ≠ 0 := by
  have hs' : initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) ≠ 0 := by
    intro hzero
    exact hs (by rw [hzero]; simp)
  have hi := initialJetEquation_ne_zero_of_separant_ne_zero center _ hs'
  intro hzero
  have he : initialJetEquationOver (Polynomial.C center) Q = 0 := by
    apply (optionEquivRight E (Fin (r + 1))).symm.injective
    simpa only [symbolicSourceInitialEquation, map_zero] using hzero
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom z)) he
  rw [map_initialJetEquationOver, map_zero,
    show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hm
  exact hi hm

open Classical in
/-- Polynomially regular witnesses admit a common chart, so the finite ordinary bound does
not require a supplied Taylor center or source properness certificate. -/
theorem finite_frobeniusRegularBadWitnesses_card_le_of_separant [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hb : 0 < b) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (challenges : Finset E) (witness : E → E[X])
    (hdegree : ∀ w ∈ challenges, (expand E (p ^ e) (witness w)).degree < K)
    (hsol : ∀ w ∈ challenges, differentialSpecialization (challengeSpecialization Q w)
      (expand E (p ^ e) (witness w)) = 0)
    (hsep : ∀ w ∈ challenges, differentialSpecialization
      (separant (challengeSpecialization Q w) (Fin.last 0))
      (expand E (p ^ e) (witness w)) ≠ 0)
    (hagree : ∀ w ∈ challenges, A ≤
      (polynomialAgreementSet (mappedDomain domain ι)
        (fun i ↦ ι (f i) + w ^ (p ^ e) * ι (g i)) (witness w)).card)
    (hbad : ∀ w ∈ challenges,
      ¬HasExactCorrelatedPair domain f g ι k (w ^ (p ^ e)) (witness w)) :
    (challenges.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e + τ * h) : ℕ) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
      ((n - k) * b : ℕ) := by
  classical
  obtain hempty | ⟨w, hw⟩ := challenges.eq_empty_or_nonempty
  · subst challenges
    positivity
  obtain ⟨center, hc⟩ := exists_common_symbolicWitness_center Q challenges id
    (fun w ↦ expand E (p ^ e) (witness w)) hsep
  have hinit : symbolicSourceInitialEquation center Q ≠ 0 := by
    apply ordinary_source_initial_ne_zero_of_regular center w Q
      (polynomialJet center (expand E (p ^ e) (witness w)))
    rw [aeval_initialJetSeparant]
    exact hc w hw
  have hchart := symbolicFrobeniusWitness_equations Q center w (witness w) p e K τ
    hτ (hdegree w hw) (hsol w hw) (hc w hw)
  have hproper := span_singleton_ne_top_of_aeval_eq_zero
    (symbolicSourceInitialEquation center Q)
    (symbolicWitnessPoint center w (expand E (p ^ e) (witness w))) hchart.1
  exact finite_frobeniusRegularBadWitnesses_card_le domain f g ι roots center Q p e τ h b A
    hroots hK hKk hτ hτpos hb hkA hAn hheight hjet hinit hproper challenges witness
    hdegree hsol hc hagree hbad

end ReedSolomon
