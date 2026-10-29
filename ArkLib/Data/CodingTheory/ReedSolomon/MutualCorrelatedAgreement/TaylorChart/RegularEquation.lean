/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ExceptionalChallenges
public import ArkLib.Data.Polynomial.Differential.BaseChange

/-!
# One exceptional set for regular symbolic equations

The bad challenges of a regular symbolic differential equation admit one finite exceptional set
outside which every close solution has an exact correlated-pair representation. Its size is
bounded using the chart-incidence and pair-agreement estimates.

## Main statements

* `ReedSolomon.regularSymbolicBadChallenges` identifies the close regular solutions without exact
  correlated-pair representations.
* `ReedSolomon.regularSymbolicAgreementBound` gives the associated rational cardinality bound.
* `ReedSolomon.finite_regularSymbolicBadChallenges_card_le` bounds every finite family of bad
  challenges.
* `ReedSolomon.regularSymbolicBadChallenges_finite` proves the full bad set is finite.
* `ReedSolomon.exists_exceptional_regularSymbolicCorrelatedAgreement` chooses one exceptional
  set before the challenge and polynomial witnesses.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

variable {F E : Type*} [Field F] [Field E] [DecidableEq E] {n r : ℕ}

/-- Challenges with a close regular solution of the symbolic equation but no exact
base-field correlated-pair representation. -/
def regularSymbolicBadChallenges [DecidableEq F]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (k A : ℕ) : Set E :=
  {z | ∃ P : E[X], P.degree < k ∧
    A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
      (fun i ↦ iota (f i) + z * iota (g i)) P).card ∧
    differentialSpecialization (challengeSpecialization Q z) P = 0 ∧
    differentialSpecialization (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 ∧
    ¬ HasExactCorrelatedPair domain f g iota k z P}

/-- The incidence and accidental-agreement bound for regular symbolic equations. -/
def regularSymbolicAgreementBound (n r K k L A v h : ℕ) : ℚ :=
  ((v + h : ℕ) : ℚ) *
    ((((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℚ) /
      ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1)) +
    ((n - L : ℕ) : ℚ) * ((v : ℚ) *
      ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ)) ^ r))

/-- Every finite set of bad challenges satisfies the regular symbolic agreement bound. -/
theorem finite_regularSymbolicBadChallenges_card_le [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (S : Finset E) (hS : ↑S ⊆ regularSymbolicBadChallenges domain f g iota Q k A) :
    (S.card : ℚ) ≤ regularSymbolicAgreementBound n r K k L A v h := by
  classical
  let witness (z : E) : E[X] := if hz : z ∈ S then Classical.choose (hS hz) else 0
  have hw (z : E) (hz : z ∈ S) := Classical.choose_spec (hS hz)
  have hdeg (z : E) (hz : z ∈ S) : (witness z).degree < k := by
    simpa only [witness, dite_eq_left hz] using (hw z hz).1
  have hsol (z : E) (hz : z ∈ S) :
      differentialSpecialization (challengeSpecialization Q z) (witness z) = 0 := by
    simpa only [witness, dite_eq_left hz] using (hw z hz).2.2.1
  have hsep (z : E) (hz : z ∈ S) : differentialSpecialization
      (separant (challengeSpecialization Q z) (Fin.last r)) (witness z) ≠ 0 := by
    simpa only [witness, dite_eq_left hz] using (hw z hz).2.2.2.1
  obtain ⟨center, hc⟩ := exists_forall_jetEvaluation_ne_zero_of_family S
    (fun z ↦ separant (challengeSpecialization Q z) (Fin.last r)) witness hsep
  let jet (z : E) : Fin (r + 1) → E := polynomialJet center (witness z)
  apply finite_symbolicTaylorChart_badChallenges_card_le domain f g iota center Q K k L A v h
    hK hkK hk hkL hLA hAn hjet hheight S witness jet
  · intro z hz
    let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
    have hQz : Qz = challengeSpecialization Q z := by
      dsimp [Qz, challengeSpecialization]
    have hsolz : differentialSpecialization Qz (witness z) = 0 := by
      rw [hQz]
      exact hsol z hz
    have hseparantz : jetEvaluation (separant Qz (Fin.last r)) center (jet z) ≠ 0 := by
      rw [hQz]
      exact hc z hz
    have hinitial := aeval_initialJetEquation_polynomialJet center Qz (witness z) hsolz
    have hSjet : aeval (jet z) (initialJetSeparant center Qz) ≠ 0 := by
      rw [aeval_initialJetSeparant]
      exact hseparantz
    refine ⟨hdeg z hz, hinitial, hSjet, ?_, ?_⟩
    · intro l hl
      have hcoeff : (Polynomial.taylor center (witness z)).coeff l.val = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        rw [Polynomial.degree_taylor]
        exact (hdeg z hz).trans_le (Nat.cast_le.mpr hl)
      have hcₗ := rationalTaylorCoefficient_eq_solution center Qz (witness z) hsolz
        hseparantz l.val (fun i hi hil ↦ hbin i hi (hil.trans_lt l.isLt))
      have hroot : rationalTaylorCoefficient center Qz (jet z) l.val = 0 := by
        rw [hcₗ, hcoeff]
      exact aeval_commonTaylorNumerator_eq_zero center Qz (jet z) (2 * K) hSjet hroot
    · exact rationalTaylorPolynomial_polynomialJet center Qz (witness z) hsolz hseparantz
        ((hdeg z hz).trans_le (Nat.cast_le.mpr hkK)) hbin
  · intro z hz
    simpa only [witness, dite_eq_left hz] using (hw z hz).2.1
  · intro z hz
    simpa only [witness, dite_eq_left hz, HasExactCorrelatedPair] using (hw z hz).2.2.2.2

/-- The full set of regular symbolic bad challenges is finite. -/
theorem regularSymbolicBadChallenges_finite [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    (regularSymbolicBadChallenges domain f g iota Q k A).Finite := by
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt (regularSymbolicAgreementBound n r K k L A v h)
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hb := finite_regularSymbolicBadChallenges_card_le domain f g iota Q K k L A v h
    hK hkK hk hkL hLA hAn hjet hheight hbin S hS
  rw [hcard] at hb
  exact (not_lt_of_ge hb) hN

/-- One exceptional set works for every close regular solution of the symbolic equation, with
exact equality of full agreement sets and base-field polynomial pairs. -/
theorem exists_exceptional_regularSymbolicCorrelatedAgreement [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularSymbolicAgreementBound n r K k L A v h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 →
        HasExactCorrelatedPair domain f g iota k z P := by
  classical
  have hfinite := regularSymbolicBadChallenges_finite domain f g iota Q K k L A v h
    hK hkK hk hkL hLA hAn hjet hheight hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularSymbolicBadChallenges_card_le domain f g iota Q K k L A v h
      hK hkK hk hkL hLA hAn hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end

end ReedSolomon
