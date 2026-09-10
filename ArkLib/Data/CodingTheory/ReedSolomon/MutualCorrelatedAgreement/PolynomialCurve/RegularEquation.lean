/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExceptionalChallenges
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorWitnessEmbedding
/-!
# One exceptional set for a regular symbolic polynomial-curve equation

Each finite family of bad challenges admits a common regular Taylor center. The strong
lifted-power chart bound is independent of that center and of the selected witnesses, so it
bounds the entire bad set. The characteristic budget depends on the derivative order and Taylor
cutoff, but not on the batching degree.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative

variable {F E : Type*} [Field F] [Field E] [DecidableEq E] {n r ℓ : ℕ}

/-- Challenges possessing a regular close solution without exact power-tuple agreement. -/
def regularSymbolicCurveBadChallenges
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (k A : ℕ) : Set E :=
  {z | ∃ P : E[X], P.degree < k ∧
    A ≤ (polynomialAgreementSet (mappedDomain domain iota)
      (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card ∧
    differentialSpecialization (challengeSpecialization Q z) P = 0 ∧
    differentialSpecialization (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 ∧
    ¬ HasExactPowerAgreement domain w iota k z P}

/-- The strong lifted-power incidence budget plus the retained tuples' exact accidental budget.
The batching degree occurs only in the two outer linear factors. -/
def regularSymbolicCurveMCABound (n r ℓ K k L A v h : ℕ) : ℚ :=
  ((ℓ + h : ℕ) : ℚ) * ((v + 1 : ℕ) : ℚ) *
      ((((n * (2 + 2 * K * v) : ℕ) : ℚ) /
        ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1)) +
    ((ℓ * (n - L) : ℕ) : ℚ) * ((v : ℚ) *
      ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ)) ^ r))

/-- Every finite set of bad challenges satisfies the strong polynomial-curve budget. The
common Taylor center and the selected witnesses may depend on the finite set. -/
theorem finite_regularSymbolicCurveBadChallenges_card_le [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularSymbolicCurveBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularSymbolicCurveMCABound n r ℓ K k L A v h := by
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
  apply finite_sourceCurve_bad_challenges_card_le domain w iota center Q K k L A v h
    hK hkK hk hkL hLA hAn hD hv hjet hheight S witness
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
      · exact (symbolicWitnessPoint_equations Q center z (witness z) K hd
          (hsol z hz) hs hbin).2.1
      · exact hbin
  · intro z hz
    simpa only [witness, dif_pos hz] using (hw z hz).2.1
  · intro z hz
    simpa only [witness, dif_pos hz] using (hw z hz).2.2.2.2

/-- The full bad-challenge set is finite; finiteness is derived from the uniform finite-subset
bound rather than assumed. -/
theorem regularSymbolicCurveBadChallenges_finite [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    (regularSymbolicCurveBadChallenges domain w iota Q k A).Finite := by
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt (regularSymbolicCurveMCABound n r ℓ K k L A v h)
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hb := finite_regularSymbolicCurveBadChallenges_card_le
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin S hS
  rw [hcard] at hb
  exact (not_lt_of_ge hb) hN

/-- One finite exceptional set works simultaneously for every regular close solution of the
symbolic polynomial-curve equation and yields exact full agreement with a base-field tuple. -/
theorem exists_exceptional_regularSymbolicCurveMCA [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularSymbolicCurveMCABound n r ℓ K k L A v h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last r)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  classical
  have hfinite := regularSymbolicCurveBadChallenges_finite
    domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularSymbolicCurveBadChallenges_card_le
      domain w iota Q K k L A v h hK hkK hk hkL hLA hAn hD hv hjet hheight hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end ReedSolomon
