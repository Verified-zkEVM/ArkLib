/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedExceptionalChallenges
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.JetDegree
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients

/-!
# Regular equations on power-batched polynomial curves

Close regular solutions of a symbolic differential equation that fail exact power agreement
belong to one bounded finite set of challenges. The bound combines incidence of regular Taylor
charts with the exceptional challenges for retained polynomial tuples.

## Main statements

* `regularPowerBatchedBadChallenges` describes close regular solutions without exact power
  agreement.
* `regularPowerBatchedAgreementBound` gives the rational bound for these challenges.
* `finite_regularPowerBatchedBadChallenges_card_le` bounds every finite family of bad
  challenges.
* `regularPowerBatchedBadChallenges_finite` proves the full bad set is finite.
* `exists_exceptional_regularPowerBatchedAgreement` chooses a bounded exceptional set before
  the challenge and polynomial witnesses.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

open Classical in
/-- Challenges with a close regular solution but no exact power-batched agreement. -/
def regularPowerBatchedBadChallenges
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (k A : ℕ) : Set E :=
  {z | ∃ P : E[X], P.degree < k ∧
    A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
      (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card ∧
    differentialSpecialization (challengeSpecialization Q z) P = 0 ∧
    differentialSpecialization (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 ∧
    ¬ HasExactPowerAgreement domain w iota k z P}

/-- The regular-chart incidence budget plus the retained tuples' exact-agreement budget. -/
def regularPowerBatchedAgreementBound (n r ℓ K k L A v h : ℕ) : ℚ :=
  ((ℓ + h : ℕ) : ℚ) * ((v + 1 : ℕ) : ℚ) *
      ((((n * (2 + 2 * K * v) : ℕ) : ℚ) /
        ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1)) +
    ((ℓ * (n - L : ℕ) : ℕ) : ℚ) * ((v : ℚ) *
      ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ)) ^ r))

open Classical in
/-- Every finite set of bad challenges satisfies the regular power-batched agreement bound. -/
theorem finite_regularPowerBatchedBadChallenges_card_le [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularPowerBatchedBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularPowerBatchedAgreementBound n r ℓ K k L A v h := by
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
  apply finite_powerBatchedChart_badChallenges_card_le
    domain w iota center Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight S witness jet
  · intro z hz
    let Qz : DifferentialPolynomial E r :=
      MvPolynomial.map (Polynomial.evalRingHom z) Q
    have hQz : Qz = challengeSpecialization Q z := by
      dsimp [Qz, challengeSpecialization]
    have hsolz : differentialSpecialization Qz (witness z) = 0 := by
      rw [hQz]
      exact hsol z hz
    have hseparantz : jetEvaluation (separant Qz (Fin.last r)) center (jet z) ≠ 0 := by
      rw [hQz]
      exact hc z hz
    refine ⟨hdeg z hz, ?_, ?_, ?_⟩
    · exact aeval_initialJetEquation_polynomialJet center Qz (witness z) hsolz
    · rw [aeval_initialJetSeparant]
      exact hseparantz
    · simpa only [jet] using rationalTaylorPolynomial_polynomialJet center Qz (witness z)
        hsolz hseparantz ((hdeg z hz).trans_le (Nat.cast_le.mpr hkK)) hbin
  · intro z hz
    simpa only [witness, dite_eq_left hz] using (hw z hz).2.1
  · intro z hz
    simpa only [witness, dite_eq_left hz, HasExactPowerAgreement] using (hw z hz).2.2.2.2

open Classical in
/-- The full set of regular power-batched bad challenges is finite. -/
theorem regularPowerBatchedBadChallenges_finite [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    (regularPowerBatchedBadChallenges domain w iota Q k A).Finite := by
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt (regularPowerBatchedAgreementBound n r ℓ K k L A v h)
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hb := finite_regularPowerBatchedBadChallenges_card_le
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin S hS
  rw [hcard] at hb
  exact (not_lt_of_ge hb) hN

open Classical in
/-- One bounded exceptional set works for every close regular solution of the symbolic equation;
outside it, each solution has exact power-batched agreement. -/
theorem exists_exceptional_regularPowerBatchedAgreement [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularPowerBatchedAgreementBound n r ℓ K k L A v h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  classical
  have hfinite := regularPowerBatchedBadChallenges_finite
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularPowerBatchedBadChallenges_card_le
      domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hseparant
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hseparant, hbad⟩

end

end ReedSolomon
