/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.RegularChart
/-!
# Choosing a common regular chart for ordinary witnesses
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

open Classical in
/-- One finite exceptional set controls all polynomially regular pulled solutions. -/
theorem exists_exceptional_frobeniusRegularSolutions [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hb : 0 < b) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        (h * (1 + τ * (b - 1)) + b * (p ^ e + τ * h) : ℕ) *
          (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) + ((n - k) * b : ℕ) ∧
      ∀ w ∉ exceptional, ∀ P : E[X],
        (expand E (p ^ e) P).degree < K →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        differentialSpecialization (separant (challengeSpecialization Q w) (Fin.last 0))
          (expand E (p ^ e) P) ≠ 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (fun i ↦ ι (f i) + w ^ (p ^ e) * ι (g i)) P).card →
        HasExactCorrelatedPair domain f g ι k (w ^ (p ^ e)) P := by
  classical
  let bad : Set E := {w | ∃ P : E[X],
    (expand E (p ^ e) P).degree < K ∧
    differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 ∧
    differentialSpecialization (separant (challengeSpecialization Q w) (Fin.last 0))
      (expand E (p ^ e) P) ≠ 0 ∧
    A ≤ (polynomialAgreementSet (mappedDomain domain ι)
      (fun i ↦ ι (f i) + w ^ (p ^ e) * ι (g i)) P).card ∧
    ¬HasExactCorrelatedPair domain f g ι k (w ^ (p ^ e)) P}
  let bound : ℚ :=
    (h * (1 + τ * (b - 1)) + b * (p ^ e + τ * h) : ℕ) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) + ((n - k) * b : ℕ)
  have hfinitebound (S : Finset E) (hS : ↑S ⊆ bad) : (S.card : ℚ) ≤ bound := by
    let witness (w : E) : E[X] := if hw : w ∈ S then Classical.choose (hS hw) else 0
    have hw (w : E) (hw : w ∈ S) := Classical.choose_spec (hS hw)
    apply finite_frobeniusRegularBadWitnesses_card_le_of_separant domain f g ι roots Q
      p e τ h b A hroots hK hKk hτ hτpos hb hkA hAn hheight hjet S witness
    · intro w hws
      simpa only [witness, dif_pos hws] using (hw w hws).1
    · intro w hws
      simpa only [witness, dif_pos hws] using (hw w hws).2.1
    · intro w hws
      simpa only [witness, dif_pos hws] using (hw w hws).2.2.1
    · intro w hws
      simpa only [witness, dif_pos hws] using (hw w hws).2.2.2.1
    · intro w hws
      simpa only [witness, dif_pos hws] using (hw w hws).2.2.2.2
  have hfinite : bad.Finite := by
    by_contra hinfinite
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
    have hbnd := hfinitebound S hS
    rw [hcard] at hbnd
    exact (not_lt_of_ge hbnd) hN
  refine ⟨hfinite.toFinset, hfinitebound _ (by simp), ?_⟩
  intro w hw P hdeg hsol hsep hagree
  by_contra hbad
  apply hw
  exact hfinite.mem_toFinset.mpr ⟨P, hdeg, hsol, hsep, hagree, hbad⟩

end ReedSolomon
