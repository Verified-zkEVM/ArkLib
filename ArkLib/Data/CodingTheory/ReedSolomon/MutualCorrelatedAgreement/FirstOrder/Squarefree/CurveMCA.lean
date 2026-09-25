/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.RetainedTail
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedDerivativeImage
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants

/-!
# Retained squarefree first-order curve agreement

The regular positive-factor locus and its retained singular tail give one exceptional set for
exact power agreement with a retained squarefree first-order curve.

## Main statements

* `retainedOrdinaryCurveAgreementCharge` defines the ordinary-tail charge.
* `retainedSquarefreeCurveAgreementCharge` adds the regular derivative-capped charge.
* `exists_exceptional_retainedSquarefreeCurveAgreement_of_tail` combines the regular and
  singular loci into one exceptional set.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-- The ordinary-tail charge for a retained curve with `ell + 1` received words. -/
def retainedOrdinaryCurveAgreementCharge (theta : ℝ) (n D ell B M H : ℕ) : ℝ :=
  let b := B * (2 * M + 1)
  let h := H * (2 * M + 1)
  ((2 * b - 1) * h : ℕ) +
    theta * (h + ell * b + 4 * D * b * h : ℕ) +
      (ell * ((n - D - 1) * b) : ℕ)

/-- The retained squarefree charge before an optimized exceptional-set comparison. -/
def retainedSquarefreeCurveAgreementCharge
    (theta : ℝ) (n D ell L A B M H : ℕ) : ℝ :=
  retainedOrdinaryCurveAgreementCharge theta n D ell B M H +
    (regularPowerBatchedDerivativeCappedBoundTwo n ell (D + 1) (D + 1)
      L A B M H (regularTaylorExponent D) : ℝ)

/-- The order-zero interface used for the retained singular tail. -/
def HasRetainedOrdinaryCurveAgreementTransfer
    {F E : Type*} [Field F] [Field E] [instF : DecidableEq F]
    [instE : DecidableEq E]
    {n D ell A B M H : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E) (Q₀ : DifferentialPolynomial E[X] 0) : Prop :=
  ∃ exceptional : Finset E,
    (exceptional.card : ℝ) ≤
      retainedOrdinaryCurveAgreementCharge
        (HiddenDerivative.agreementIncidenceRatio n D A) n D ell B M H ∧
    ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
      differentialSpecialization (challengeSpecialization Q₀ z) P = 0 →
      HasExactPowerAgreement domain values iota (D + 1) z P

open Classical in
/-- A retained squarefree equation and its singular-tail transfer give one exceptional set.
Outside it, every qualifying root of the equation has exact power agreement. -/
theorem exists_exceptional_retainedSquarefreeCurveAgreement_of_tail
    {F E : Type*} [Field F] [Field E] [instF : DecidableEq F]
    [instE : DecidableEq E]
    [IsAlgClosed E] {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hellH : 0 < ell + H)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : CoeffNatDegreeLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (htail : HasRetainedOrdinaryCurveAgreementTransfer (D := D) (A := A)
      (B := B) (M := M) (H := H) domain values iota (singularCurveEquation Q)) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveAgreementCharge
        (HiddenDerivative.agreementIncidenceRatio n D A) n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
    HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hdecF : instF = (fun a b : F ↦ Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  have hdecE : instE = (fun a b : E ↦ Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  have hcharE : ringChar E = 0 ∨ D < ringChar E := by
    have heq : ringChar E = ringChar F := by
      let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
      exact ringChar.eq E (ringChar F)
    rw [heq]
    rcases hchar with hzero | hpos
    · exact Or.inl hzero
    · exact Or.inr ((Nat.le_max_left D M).trans_lt hpos)
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiD
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_ringChar_eq_zero_or_lt
      (by simpa using hcharE) (by omega) (by omega)
  have htaylor :
      TaylorExponentSufficient 1 (D + 1) (regularTaylorExponent D) := by
    simpa only [regularTaylorExponent] using taylorExponentSufficient_firstOrder_tight D
  have hpositiveJet : jetTotalDegree (positiveCurveEquation Q) ≤ B :=
    (positiveCurveEquation_jetTotalDegree_le Q).trans hjet
  have hpositiveHeight : CoeffNatDegreeLE (positiveCurveEquation Q) H :=
    positiveCurveEquation_coeffNatDegreeLE_of_input Q hheight
  have hpositiveDerivative : (positiveCurveEquation Q).degreeOf (some 1) ≤ M :=
    (positiveCurveEquation_yOneDegree_le Q).trans hderiv
  obtain ⟨regularExceptional, hregularCard, hregular⟩ :
      ∃ regularExceptional : Finset E,
        (regularExceptional.card : ℚ) ≤
          regularPowerBatchedDerivativeCappedBoundTwo n ell (D + 1) (D + 1)
            L A B M H (regularTaylorExponent D) ∧
        ∀ z ∉ regularExceptional, ∀ P : E[X], P.degree < D + 1 →
          A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          differentialSpecialization
            (challengeSpecialization (positiveCurveEquation Q) z) P = 0 →
          differentialSpecialization
            (separant (challengeSpecialization (positiveCurveEquation Q) z)
              (Fin.last 1)) P ≠ 0 →
          HasExactPowerAgreement domain values iota (D + 1) z P := by
    by_cases hDone : D = 1
    · subst D
      have hresult :=
        exists_exceptional_regularPowerBatchedAgreement_identityPair
          domain values iota (positiveCurveEquation Q) L A B M H hDL hLA hAn
          (by omega) hpositiveJet hpositiveHeight
      rw [← hdecF, ← hdecE] at hresult
      convert hresult using 1
      norm_num [regularTaylorExponent]
    · have hresult :=
        exists_exceptional_regularPowerBatchedAgreement_derivativeCapped_of_exponent
          domain values iota (positiveCurveEquation Q)
          (D + 1) (D + 1) L A B M H (regularTaylorExponent D)
          htaylor (by unfold regularTaylorExponent; omega) (by omega) le_rfl hDL
          hLA hAn hellH (by omega) hM hMB hpositiveJet hpositiveHeight
          hpositiveDerivative hbin
      rw [← hdecF, ← hdecE] at hresult
      simpa only [Nat.cast_add, Nat.cast_one] using hresult
  obtain ⟨tailExceptional, htailCard, htailGood⟩ := htail
  let exceptional := tailExceptional ∪ regularExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcard : (exceptional.card : ℝ) ≤
        (tailExceptional.card : ℝ) + regularExceptional.card := by
      exact_mod_cast Finset.card_union_le tailExceptional regularExceptional
    unfold retainedSquarefreeCurveAgreementCharge
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
