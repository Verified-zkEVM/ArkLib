/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.RegularChart
/-! # Uniform exceptional set for regular polynomial-curve solutions -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

open Classical in
/-- One finite exceptional set controls every polynomially regular solution at a free retention
threshold `L`. -/
theorem exists_exceptional_frobeniusPowerRegularSolutions_at [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
          (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) +
        (ℓ * (n - L) * b : ℕ) ∧
      ∀ z ∉ exceptional, ∀ P : E[X],
        (expand E (p ^ e) P).degree < K →
        differentialSpecialization (challengeSpecialization Q z) (expand E (p ^ e) P) = 0 →
        differentialSpecialization (separant (challengeSpecialization Q z) (Fin.last 0))
          (expand E (p ^ e) P) ≠ 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) P := by
  classical
  let bad : Set E := {z | ∃ P : E[X],
    (expand E (p ^ e) P).degree < K ∧
    differentialSpecialization (challengeSpecialization Q z) (expand E (p ^ e) P) = 0 ∧
    differentialSpecialization (separant (challengeSpecialization Q z) (Fin.last 0))
      (expand E (p ^ e) P) ≠ 0 ∧
    A ≤ (polynomialAgreementSet (mappedDomain domain ι)
      (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e))) P).card ∧
    ¬HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) P}
  let bound : ℚ :=
    (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) +
    (ℓ * (n - L) * b : ℕ)
  have hfinitebound (S : Finset E) (hS : ↑S ⊆ bad) : (S.card : ℚ) ≤ bound := by
    let witness (z : E) : E[X] := if hz : z ∈ S then Classical.choose (hS hz) else 0
    have hz (z : E) (hz : z ∈ S) := Classical.choose_spec (hS hz)
    apply finite_frobeniusPowerRegularBadWitnesses_card_le_of_separant_at
      domain values ι roots Q p e τ h b A hroots hK hKk hτ hτpos hℓ hb
        hkL hLA hAn hheight hjet S witness
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).1
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).2.1
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).2.2.1
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).2.2.2.1
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).2.2.2.2
  have hfinite : bad.Finite := by
    by_contra hinfinite
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
    have hbnd := hfinitebound S hS
    rw [hcard] at hbnd
    exact (not_lt_of_ge hbnd) hN
  refine ⟨hfinite.toFinset, hfinitebound _ (by simp), ?_⟩
  intro z hz P hdeg hsol hsep hagree
  by_contra hbad
  apply hz
  exact hfinite.mem_toFinset.mpr ⟨P, hdeg, hsol, hsep, hagree, hbad⟩

open Classical in
/-- One finite exceptional set controls every polynomially regular pulled power-curve solution. -/
theorem exists_exceptional_frobeniusPowerRegularSolutions [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hℓ : 0 < ℓ) (hb : 0 < b) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
          (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
        (ℓ * (n - k) * b : ℕ) ∧
      ∀ z ∉ exceptional, ∀ P : E[X],
        (expand E (p ^ e) P).degree < K →
        differentialSpecialization (challengeSpecialization Q z) (expand E (p ^ e) P) = 0 →
        differentialSpecialization (separant (challengeSpecialization Q z) (Fin.last 0))
          (expand E (p ^ e) P) ≠ 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) P := by
  classical
  let bad : Set E := {z | ∃ P : E[X],
    (expand E (p ^ e) P).degree < K ∧
    differentialSpecialization (challengeSpecialization Q z) (expand E (p ^ e) P) = 0 ∧
    differentialSpecialization (separant (challengeSpecialization Q z) (Fin.last 0))
      (expand E (p ^ e) P) ≠ 0 ∧
    A ≤ (polynomialAgreementSet (mappedDomain domain ι)
      (powerBatchedWord (fun t i ↦ ι (values t i)) (z ^ (p ^ e))) P).card ∧
    ¬HasExactPowerAgreement domain values ι k (z ^ (p ^ e)) P}
  let bound : ℚ :=
    (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
    (ℓ * (n - k) * b : ℕ)
  have hfinitebound (S : Finset E) (hS : ↑S ⊆ bad) : (S.card : ℚ) ≤ bound := by
    let witness (z : E) : E[X] := if hz : z ∈ S then Classical.choose (hS hz) else 0
    have hz (z : E) (hz : z ∈ S) := Classical.choose_spec (hS hz)
    apply finite_frobeniusPowerRegularBadWitnesses_card_le_of_separant
      domain values ι roots Q p e τ h b A hroots hK hKk hτ hτpos hℓ hb hkA hAn
        hheight hjet S witness
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).1
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).2.1
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).2.2.1
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).2.2.2.1
    · intro z hzs
      simpa only [witness, dif_pos hzs] using (hz z hzs).2.2.2.2
  have hfinite : bad.Finite := by
    by_contra hinfinite
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
    have hbnd := hfinitebound S hS
    rw [hcard] at hbnd
    exact (not_lt_of_ge hbnd) hN
  refine ⟨hfinite.toFinset, hfinitebound _ (by simp), ?_⟩
  intro z hz P hdeg hsol hsep hagree
  by_contra hbad
  apply hz
  exact hfinite.mem_toFinset.mpr ⟨P, hdeg, hsol, hsep, hagree, hbad⟩

end ReedSolomon
