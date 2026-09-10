/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ExceptionalChallenges
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorWitnessEmbedding
/-!
# One exceptional set for a regular symbolic equation

Each finite family of bad challenges admits a common regular Taylor center. The resulting
bound is independent of that center and of the chosen witnesses, so it bounds the entire
bad set. The final exceptional set is chosen before all polynomial witnesses.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative

variable {F E : Type*} [Field F] [Field E] [DecidableEq E] {n r : ℕ}

/-- Exact representation includes equality of the entire agreement set, not a subset. -/
def HasExactCorrelatedPair [DecidableEq F] (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (k : ℕ) (z : E) (P : E[X]) : Prop :=
  ∃ pair : F[X] × F[X], pair.1.degree < k ∧ pair.2.degree < k ∧
    P = correlatedPairSpecialization iota z pair ∧
    polynomialAgreementSet (mappedDomain domain iota)
      (fun i ↦ iota (f i) + z * iota (g i)) P =
        commonPolynomialAgreementSet domain f g pair.1 pair.2

/-- Challenges possessing at least one regular close solution with no exact base pair. -/
def regularSymbolicBadChallenges [DecidableEq F]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (k A : ℕ) : Set E :=
  {z | ∃ P : E[X], P.degree < k ∧
    A ≤ (polynomialAgreementSet (mappedDomain domain iota)
      (fun i ↦ iota (f i) + z * iota (g i)) P).card ∧
    differentialSpecialization (challengeSpecialization Q z) P = 0 ∧
    differentialSpecialization (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 ∧
    ¬ HasExactCorrelatedPair domain f g iota k z P}

/-- The source incidence and accidental-agreement budgets for a regular symbolic equation. -/
def regularSymbolicMCABound (n r K k L A v h : ℕ) : ℚ :=
  ((v + h : ℕ) : ℚ) *
    ((((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℚ) /
      ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1)) +
    ((n - L : ℕ) : ℚ) * ((v : ℚ) *
      ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ)) ^ r))

/-- A finite set of bad challenges has a uniform bound, although its regular center
and selected polynomial witnesses may depend on that finite set. -/
theorem finite_regularSymbolicBadChallenges_card_le [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (S : Finset E) (hS : ↑S ⊆ regularSymbolicBadChallenges domain f g iota Q k A) :
    (S.card : ℚ) ≤ regularSymbolicMCABound n r K k L A v h := by
  classical
  let witness (z : E) : E[X] := if hz : z ∈ S then Classical.choose (hS hz) else 0
  have hw (z : E) (hz : z ∈ S) := Classical.choose_spec (hS hz)
  have hdeg (z : E) (hz : z ∈ S) : (witness z).degree < k := by
    simpa only [witness, dif_pos hz] using (hw z hz).1
  have hsol (z : E) (hz : z ∈ S) :
      differentialSpecialization (challengeSpecialization Q z) (witness z) = 0 := by
    simpa only [witness, dif_pos hz] using (hw z hz).2.2.1
  have hsep (z : E) (hz : z ∈ S) : differentialSpecialization
      (separant (challengeSpecialization Q z) (Fin.last r)) (witness z) ≠ 0 := by
    simpa only [witness, dif_pos hz] using (hw z hz).2.2.2.1
  obtain ⟨center, hc⟩ := exists_common_symbolicWitness_center Q S id witness hsep
  apply finite_sourceChart_bad_challenges_card_le domain f g iota center Q K k L A v h
    hK hkK hk hkL hLA hAn hv hjet hheight S witness
    (fun z ↦ polynomialJet center (witness z))
  · intro z hz
    have hs := hc z hz
    have hd : (witness z).degree < K := (hdeg z hz).trans_le (Nat.cast_le.mpr hkK)
    refine ⟨hdeg z hz, initialJetEquation_solution center _ _ (hsol z hz), ?_, ?_, ?_⟩
    · rwa [aeval_initialJetSeparant]
    · intro l hl
      change aeval (polynomialJet center (witness z))
        (commonTaylorNumerator center (challengeSpecialization Q z) K l) = 0
      rw [commonTaylorNumerator_solution center _ _ (hsol z hz) hs K hbin]
      have hcoeff : (Polynomial.taylor center (witness z)).coeff l.val = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        simpa only [Polynomial.degree_taylor] using
          (hdeg z hz).trans_le (Nat.cast_le.mpr hl)
      rw [hcoeff, mul_zero]
    · apply symbolicWitnessPoint_reconstruction Q center z (witness z) K hd (hsol z hz)
      · have he := (symbolicWitnessPoint_equations Q center z (witness z) K hd
          (hsol z hz) hs hbin).2.1
        exact he
      · exact hbin
  · intro z hz
    simpa only [witness, dif_pos hz] using (hw z hz).2.1
  · intro z hz
    simpa only [witness, dif_pos hz, HasExactCorrelatedPair] using (hw z hz).2.2.2.2

/-- The entire bad set is finite; finiteness is a conclusion, not a counting premise. -/
theorem regularSymbolicBadChallenges_finite [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    (regularSymbolicBadChallenges domain f g iota Q k A).Finite := by
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt (regularSymbolicMCABound n r K k L A v h)
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hb := finite_regularSymbolicBadChallenges_card_le domain f g iota Q K k L A v h
    hK hkK hk hkL hLA hAn hv hjet hheight hbin S hS
  rw [hcard] at hb
  exact (not_lt_of_ge hb) hN

/-- One exceptional set works for every regular close solution of the symbolic equation,
with exact equality of full agreement sets and base-field polynomial pairs. -/
theorem exists_exceptional_regularSymbolicLineMCA [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularSymbolicMCABound n r K k L A v h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 →
        HasExactCorrelatedPair domain f g iota k z P := by
  classical
  have hfinite := regularSymbolicBadChallenges_finite domain f g iota Q K k L A v h
    hK hkK hk hkL hLA hAn hv hjet hheight hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularSymbolicBadChallenges_card_le domain f g iota Q K k L A v h
      hK hkK hk hkL hLA hAn hv hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end ReedSolomon
