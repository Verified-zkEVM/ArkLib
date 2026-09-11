/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Solutions
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.UnifiedBudget

/-!
# Unified ordinary recovery on polynomial challenge curves

The positive-part coefficient `ordinaryPsi` removes the former split between a sharp bounded
separable-degree theorem and a coarse unconditional theorem. This module first connects that
arithmetic to the existing all-characteristic Frobenius recovery of one irreducible factor.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

variable {F E : Type*} [Field F] [Field E] {n ell : ℕ}

/-- The polynomial-curve mixed degree satisfies the unified bound for every separable factor
degree, with no comparison between `b` and `D`. -/
theorem ordinaryFrobeniusPowerMixedDegree_le_unified {D s b : ℕ} (ell h : ℕ)
    (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ordinaryFrobeniusPowerMixedDegree D ell h s b ≤
      ell * (s * b) + h * ordinaryPsi D (s * b) := by
  rw [ordinaryFrobeniusPowerMixedDegree_eq D ell h s b hb]
  have hcoefficient := ordinaryFrobenius_unified_factor hD hs hb
  nlinarith

/-- One pulled polynomial-curve factor spends the unified budget at its original root degree. -/
theorem ordinaryFrobeniusPower_charge_le_unified (theta : ℚ) (n D ell h s b : ℕ)
    (htheta : 0 ≤ theta) (hD : 1 ≤ D) (hs : 1 ≤ s) (hb : 1 ≤ b) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusPowerMixedDegree D ell h s b +
        (ell * ((n - D - 1) * b) : ℕ) ≤
      ordinaryUnifiedPowerFactorRaw theta n D ell (s * b) h := by
  have hbs : b ≤ s * b := by nlinarith
  have hmixed := ordinaryFrobeniusPowerMixedDegree_le_unified ell h hD hs hb
  unfold ordinaryUnifiedPowerFactorRaw
  apply add_le_add
  · apply add_le_add
    · exact_mod_cast Nat.mul_le_mul_right h
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hbs) 1)
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmixed) htheta
  · exact_mod_cast Nat.mul_le_mul_left ell (Nat.mul_le_mul_left (n - D - 1) hbs)

open Classical in
/-- One irreducible Frobenius factor has the unified polynomial-curve charge. The constituent
message keeps its original degree bound; inseparability creates no extra challenge loss. -/
theorem exists_exceptional_frobeniusPowerFactorSolutions_unified [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (p e D h b A : ℕ) [ExpChar E p]
    (hD : 0 < D) (hell : 0 < ell) (hb : 0 < b) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hirr : Irreducible Q) (hder : pderiv (some 0) Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = b) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell (p ^ e * b) h ∧
      ∀ w : E, w ^ (p ^ e) ∉ exceptional → ∀ P : E[X],
        P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q w) (expand E (p ^ e) P) = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) (w ^ (p ^ e))) P).card →
        HasExactPowerAgreement domain values iota (D + 1) (w ^ (p ^ e)) P := by
  classical
  let roots : Fin n → E := fun i ↦ (iterateFrobeniusEquiv E p e).symm (iota (domain i))
  have hroots : ∀ i, roots i ^ (p ^ e) = iota (domain i) := by
    intro i
    exact (iterateFrobeniusEquiv E p e).apply_symm_apply (iota (domain i))
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have hK : D * p ^ e + 1 ≤ p ^ e * (D + 1) := by nlinarith
  have htau : 0 < 2 * D * p ^ e - 1 := by
    have hDs := Nat.mul_pos hD hs
    have : 2 ≤ 2 * D * p ^ e := by nlinarith
    omega
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusPowerSeparableSolutions
    (K := D * p ^ e + 1) domain values iota roots Q p e (2 * D * p ^ e - 1) h b A
    hroots (by omega) hK (by intro l; simp only [Nat.mul_assoc]; omega)
    htau hell hb hDA hAn hheight hjet hirr hder hdegree
  refine ⟨ex.image (fun w ↦ w ^ (p ^ e)), ?_, ?_⟩
  · have hcard : ((ex.image (fun w ↦ w ^ (p ^ e))).card : ℚ) ≤ ex.card := by
      exact_mod_cast Finset.card_image_le
    have hn : n - (D + 1) + 1 = n - D := by omega
    have hA : A - (D + 1) + 1 = A - D := by omega
    have hn' : n - (D + 1) = n - D - 1 := by omega
    rw [hn, hA, hn'] at hexCard
    apply hcard.trans (hexCard.trans ?_)
    let theta : ℚ := ((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)
    have htheta : 0 ≤ theta := by positivity
    have hcharge := ordinaryFrobeniusPower_charge_le_unified theta n D ell h (p ^ e) b
      htheta hD hs hb
    unfold ordinaryFrobeniusPowerMixedDegree at hcharge
    calc
      ((h * (1 + (2 * D * p ^ e - 1) * (b - 1)) +
              b * (p ^ e * ell + (2 * D * p ^ e - 1) * h) : ℕ) : ℚ) * theta +
            ((ell * (n - D - 1) * b : ℕ) : ℚ) + (((2 * b - 1) * h : ℕ) : ℚ) =
          (((2 * b - 1) * h : ℕ) : ℚ) + theta *
              ((h * (1 + (2 * D * p ^ e - 1) * (b - 1)) +
                b * (p ^ e * ell + (2 * D * p ^ e - 1) * h) : ℕ) : ℚ) +
            ((ell * ((n - D - 1) * b) : ℕ) : ℚ) := by
        push_cast
        ring
      _ ≤ ordinaryUnifiedPowerFactorRaw theta n D ell (p ^ e * b) h := hcharge
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
