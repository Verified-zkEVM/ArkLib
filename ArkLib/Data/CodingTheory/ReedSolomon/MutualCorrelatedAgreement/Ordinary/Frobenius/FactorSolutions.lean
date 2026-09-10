/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.SeparableSolutions
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.AggregationBounds
/-!
# The original-coordinate charge of one Frobenius factor

This interface chooses the coordinate roots internally and takes the image of the pulled
exceptional set in the original challenge coordinate. Its bound spends the original root
degree `p^e*b`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

variable {F E : Type*} [Field F] [Field E] {n : ℕ}

open Classical in
/-- One separable pulled factor has the advertised original-coordinate ordinary charge. -/
theorem exists_exceptional_frobeniusFactorSolutions [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hb : 0 < b) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D (p ^ e * b) h ∧
      ∀ w : E, w ^ (p ^ e) ∉ exceptional → ∀ P : E[X],
        P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (fun i ↦ ι (f i) + w ^ (p ^ e) * ι (g i)) P).card →
        HasExactCorrelatedPair domain f g ι (D + 1) (w ^ (p ^ e)) P := by
  classical
  let roots : Fin n → E := fun i ↦ (iterateFrobeniusEquiv E p e).symm (ι (domain i))
  have hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i) := by
    intro i
    exact (iterateFrobeniusEquiv E p e).apply_symm_apply (ι (domain i))
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have hK : D * p ^ e + 1 ≤ p ^ e * (D + 1) := by nlinarith
  have hτpos : 0 < 2 * D * p ^ e - 1 := by
    have hDs := Nat.mul_pos hD hs
    have : 2 ≤ 2 * D * p ^ e := by nlinarith
    omega
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusSeparableSolutions
    (K := D * p ^ e + 1) domain f g ι roots Q p e (2 * D * p ^ e - 1) h b A
    hroots (by omega) hK (frobeniusTaylorExponentSufficient D (p ^ e))
    hτpos hb hDA hAn hheight hjet hirr hder hdegree
  refine ⟨ex.image (fun w ↦ w ^ (p ^ e)), ?_, ?_⟩
  · have hcard : ((ex.image (fun w ↦ w ^ (p ^ e))).card : ℚ) ≤ ex.card := by
      exact_mod_cast Finset.card_image_le
    have hn : n - (D + 1) + 1 = n - D := by omega
    have hA : A - (D + 1) + 1 = A - D := by omega
    have hn' : n - (D + 1) = n - D - 1 := by omega
    rw [hn, hA, hn'] at hexCard
    apply hcard.trans (hexCard.trans ?_)
    have hcharge := ordinaryFrobenius_charge_le
      (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D h (p ^ e) b
      (by positivity) hs hb
    unfold ordinaryFrobeniusMixedDegree at hcharge
    linarith
  · intro w hw P hdeg hsol hagree
    have hw' : w ∉ ex := fun hmem ↦ hw (Finset.mem_image.mpr ⟨w, hmem, rfl⟩)
    apply hex w hw' P _ hsol hagree
    apply lt_of_le_of_lt (Polynomial.degree_le_natDegree (p := expand E (p ^ e) P))
    apply WithBot.coe_lt_coe.mpr
    rw [Polynomial.natDegree_expand]
    have hnat : P.natDegree ≤ D := by
      by_cases hP : P = 0
      · simp [hP]
      · have hdeg' : P.degree < ((D + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hdeg
        have := (Polynomial.natDegree_lt_iff_degree_lt hP).mpr hdeg'
        omega
    nlinarith

end ReedSolomon
