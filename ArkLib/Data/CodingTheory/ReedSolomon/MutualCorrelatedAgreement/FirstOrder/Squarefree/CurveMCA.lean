/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.RetainedTail
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.DerivativeImage
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridTransfer

/-!
# Retained-product first-order curve agreement

This file combines the regular locus of the retained squarefree positive product with its
single content-times-resultant tail.  Both loci use polynomial-curve recovery, and their
exceptional sets are unioned before the challenge and candidate are chosen.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

/-- The ordinary part of the finite-length first-order MCA expression. -/
def retainedOrdinaryMCARaw (lambda : ℝ) (n D ell B M H : ℕ) : ℝ :=
  let b := B * (2 * M + 1)
  let h := H * (2 * M + 1)
  ((2 * b - 1) * h : ℕ) +
    lambda * (h + ell * b + 4 * D * b * h : ℕ) +
      (ell * ((n - D - 1) * b) : ℕ)

/-- Exact retained-product charge before the elementary closed-envelope comparison. -/
def retainedSquarefreeCurveMCARaw
    (lambda : ℝ) (n D ell L A B M H : ℕ) : ℝ :=
  retainedOrdinaryMCARaw lambda n D ell B M H +
    (regularSymbolicCurveMCADerivativeBoundTwo n ell (D + 1) (D + 1)
      L A B M H (2 * D - 1) : ℝ)

/-- The order-zero interface used by the retained-product union.  Its conclusion is exact
power agreement, including equality with the candidate's complete agreement set. -/
def HasRetainedOrdinaryCurveTransfer
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    {n D ell A B M H : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E) (Q₀ : DifferentialPolynomial E[X] 0) : Prop :=
  ∃ exceptional : Finset E,
    (exceptional.card : ℝ) ≤
      retainedOrdinaryMCARaw
        (HiddenDerivative.hybridTheta n D A) n D ell B M H ∧
    ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
      differentialSpecialization (challengeSpecialization Q₀ z) P = 0 →
      HasExactPowerAgreement domain values iota (D + 1) z P

private theorem natCast_ne_zero_of_retained_char_guard
    {E : Type*} [Field E] {D M i : ℕ}
    (hchar : ringChar E = 0 ∨ max D M < ringChar E)
    (hi : 0 < i) (hiD : i ≤ D) : (i : E) ≠ 0 := by
  intro hz
  have hdiv := (ringChar.spec E i).mp hz
  rcases hchar with hzero | hpos
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hi
      ((hiD.trans (Nat.le_max_left D M)).trans_lt hpos) hdiv

open Classical in
/-- A retained squarefree first-order equation and one ordinary-tail transfer give a single
exceptional set.  Outside it, every qualifying root of the original equation has exact
polynomial-curve power agreement. -/
theorem exists_exceptional_retainedSquarefreeCurveMCA_of_tail
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    [IsAlgClosed E] {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hellH : 0 < ell + H)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetWeight Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : ChallengeHeightLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasRetainedOrdinaryCurveTransfer (D := D) (A := A)
      (B := B) (M := M) (H := H) domain values iota (singularCurveEquation Q)) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveMCARaw
        (HiddenDerivative.hybridTheta n D A) n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hcharE : ringChar E = 0 ∨ max D M < ringChar E := by
    rwa [ringChar_eq_of_injective_fieldHom iota]
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiD
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_retained_char_guard hcharE (by omega) (by omega)
  have htaylor : TaylorExponentSufficient 1 (D + 1) (2 * D - 1) := by
    convert taylorExponentSufficient_two_mul_sub_three 1
      (K := D + 1) (by omega) using 1
    all_goals omega
  obtain ⟨regularExceptional, hregularCard, hregular⟩ :=
    exists_exceptional_regularSymbolicCurveMCA_derivativeCapped_of_exponent
      domain values iota (positiveCurveEquation Q)
      (D + 1) (D + 1) L A B M H (2 * D - 1)
      htaylor (by omega) (by omega) le_rfl (by omega) hDL hLA hAn
      hellH (hM.trans hMB) hM hMB
      ((positiveCurveEquation_jetWeight_le Q hQ).trans hjet)
      (fun d ↦ (positiveCurveEquation_challengeHeightLE Q d).trans
        ((Nat.le_add_left _ _).trans
          (flattened_content_add_positive_challengeDegree_le Q hQ hheight)))
      ((positiveCurveEquation_yOneDegree_le Q hQ).trans hderiv) hbin
  obtain ⟨tailExceptional, htailCard, htailGood⟩ := htail
  let exceptional := tailExceptional ∪ regularExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcard : (exceptional.card : ℝ) ≤
        (tailExceptional.card : ℝ) + regularExceptional.card := by
      exact_mod_cast Finset.card_union_le tailExceptional regularExceptional
    unfold retainedSquarefreeCurveMCARaw
    apply hcard.trans
    exact add_le_add htailCard (by exact_mod_cast hregularCard)
  · intro z hz P hdegree hagree hroot
    have hzTail : z ∉ tailExceptional := fun hmem ↦
      hz (Finset.mem_union_left regularExceptional hmem)
    have hzRegular : z ∉ regularExceptional := fun hmem ↦
      hz (Finset.mem_union_right tailExceptional hmem)
    by_cases hpositive : differentialSpecialization
        (challengeSpecialization (positiveCurveEquation Q) z) P = 0
    · by_cases hseparant : differentialSpecialization
          (challengeSpecialization
            (separant (positiveCurveEquation Q) (1 : Fin 2)) z) P = 0
      · apply htailGood z hzTail P hdegree hagree
        exact singularCurveEquation_routes_nonregular Q hQ z P hroot
          (Or.inr hseparant)
      · apply hregular z hzRegular P hdegree hagree hpositive
        simpa only [challengeSpecialization, separant, MvPolynomial.pderiv_map,
          show (Fin.last 1 : Fin 2) = 1 by decide] using hseparant
    · apply htailGood z hzTail P hdegree hagree
      exact singularCurveEquation_routes_nonregular Q hQ z P hroot
        (Or.inl hpositive)

end

end ReedSolomon.FirstOrder.Squarefree
