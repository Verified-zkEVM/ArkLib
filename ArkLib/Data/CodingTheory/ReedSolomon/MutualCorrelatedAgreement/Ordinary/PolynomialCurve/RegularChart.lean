/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.RegularBound
/-! # Choosing a common regular chart for polynomial-curve witnesses -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

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
/-- Polynomially regular power-curve witnesses admit a common Taylor chart at a free retention
threshold `L`. -/
theorem finite_frobeniusPowerRegularBadWitnesses_card_le_of_separant_at [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (challenges : Finset E) (witness : E → E[X])
    (hdegree : ∀ z ∈ challenges, (expand E (p ^ e) (witness z)).degree < K)
    (hsol : ∀ z ∈ challenges, differentialSpecialization (challengeSpecialization Q z)
      (expand E (p ^ e) (witness z)) = 0)
    (hsep : ∀ z ∈ challenges, differentialSpecialization
      (separant (challengeSpecialization Q z) (Fin.last 0))
      (expand E (p ^ e) (witness z)) ≠ 0)
    (hagree : ∀ z ∈ challenges, A ≤
      (polynomialAgreementSet (mappedDomain domain ι)
        (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e)))
        (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) (witness z)) :
    (challenges.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) +
      (ℓ * (n - L) * b : ℕ) := by
  classical
  obtain hempty | ⟨z, hz⟩ := challenges.eq_empty_or_nonempty
  · subst challenges
    positivity
  obtain ⟨center, hc⟩ := exists_common_symbolicWitness_center Q challenges id
    (fun z ↦ expand E (p ^ e) (witness z)) hsep
  have hinit : symbolicSourceInitialEquation center Q ≠ 0 := by
    apply ordinary_source_initial_ne_zero_of_regular center z Q
      (polynomialJet center (expand E (p ^ e) (witness z)))
    rw [aeval_initialJetSeparant]
    exact hc z hz
  have hchart := symbolicFrobeniusPowerWitness_equations (ℓ := ℓ)
    Q center z (witness z) p e K τ hτ (hdegree z hz) (hsol z hz) (hc z hz)
  have hproper := span_singleton_ne_top_of_aeval_eq_zero
    (symbolicSourceInitialEquation center Q)
    (symbolicWitnessPoint center z (expand E (p ^ e) (witness z))) hchart.1
  exact finite_frobeniusPowerRegularBadWitnesses_card_le_at
    domain values ι roots center Q p e τ h b A hroots hK hKk hτ hτpos hℓ hb
      hkL hLA hAn hheight hjet hinit hproper challenges witness hdegree hsol hc hagree hbad

open Classical in
/-- Polynomially regular power-curve witnesses admit a common Taylor chart. -/
theorem finite_frobeniusPowerRegularBadWitnesses_card_le_of_separant [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (challenges : Finset E) (witness : E → E[X])
    (hdegree : ∀ z ∈ challenges, (expand E (p ^ e) (witness z)).degree < K)
    (hsol : ∀ z ∈ challenges, differentialSpecialization (challengeSpecialization Q z)
      (expand E (p ^ e) (witness z)) = 0)
    (hsep : ∀ z ∈ challenges, differentialSpecialization
      (separant (challengeSpecialization Q z) (Fin.last 0))
      (expand E (p ^ e) (witness z)) ≠ 0)
    (hagree : ∀ z ∈ challenges, A ≤
      (polynomialAgreementSet (mappedDomain domain ι)
        (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e)))
        (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) (witness z)) :
    (challenges.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
      (ℓ * (n - k) * b : ℕ) := by
  classical
  obtain hempty | ⟨z, hz⟩ := challenges.eq_empty_or_nonempty
  · subst challenges
    positivity
  obtain ⟨center, hc⟩ := exists_common_symbolicWitness_center Q challenges id
    (fun z ↦ expand E (p ^ e) (witness z)) hsep
  have hinit : symbolicSourceInitialEquation center Q ≠ 0 := by
    apply ordinary_source_initial_ne_zero_of_regular center z Q
      (polynomialJet center (expand E (p ^ e) (witness z)))
    rw [aeval_initialJetSeparant]
    exact hc z hz
  have hchart := symbolicFrobeniusPowerWitness_equations (ℓ := ℓ)
    Q center z (witness z) p e K τ hτ (hdegree z hz) (hsol z hz) (hc z hz)
  have hproper := span_singleton_ne_top_of_aeval_eq_zero
    (symbolicSourceInitialEquation center Q)
    (symbolicWitnessPoint center z (expand E (p ^ e) (witness z))) hchart.1
  exact finite_frobeniusPowerRegularBadWitnesses_card_le
    domain values ι roots center Q p e τ h b A hroots hK hKk hτ hτpos hℓ hb hkA hAn
      hheight hjet hinit hproper challenges witness hdegree hsol hc hagree hbad

end ReedSolomon
