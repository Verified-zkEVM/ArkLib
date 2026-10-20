/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveTransfer
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants

/-!
# First-order hybrid transfer from an ordinary tail

An ordinary order-zero transfer for a correlated pair combines with the regular first-derivative
stages to give exact degree-one power agreement. The resulting exceptional-set bounds use the
first-order exception charge, its split- and degree-optimized ceiling, and the closed
exception constant.

## Main statements

* `ReedSolomon.HasOrdinaryTailTransfer` specifies the order-zero transfer interface.
* `ReedSolomon.exists_exceptional_firstOrder_hybrid_raw_of_tail` combines that interface with
  the regular stages at a fixed split.
* `ReedSolomon.exists_exceptional_firstOrder_hybrid_optimized_of_tail` optimizes the split and
  actual derivative degree.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial MvPolynomial

namespace ReedSolomon

open HiddenDerivative

noncomputable section

/-- An ordinary order-zero transfer for a pair of words with its ordinary-tail charge. -/
def HasOrdinaryTailTransfer
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    {n D A h mu e : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q0 : DifferentialPolynomial E[X] 0) : Prop :=
  ∃ exceptional : Finset E,
    (exceptional.card : ℝ) ≤
      HiddenDerivative.ordinaryTailCharge
        (HiddenDerivative.agreementIncidenceRatio n D A) n D h (mu - e) ∧
    ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (fun i ↦ iota (f i) + z * iota (g i)) P).card →
      differentialSpecialization (challengeSpecialization Q0 z) P = 0 →
      HasExactCorrelatedPair domain f g iota (D + 1) z P

/-- The ordinary tail and regular stages combine at a fixed split into exact power agreement. -/
theorem exists_exceptional_firstOrder_hybrid_raw_of_tail
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n D A L mu M : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (Q : DifferentialPolynomial E[X] 1)
    (descent : HiddenDerivative.FirstOrderHybridDescent Q mu M)
    (hD : 1 ≤ D) (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ D < ringChar F)
    (htail : HasOrdinaryTailTransfer (D := D) (A := A)
      (h := coeffNatDegree Q) (mu := mu) (e := descent.actualDegree)
      domain f g iota descent.tail.equation) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.firstOrderExceptionCharge
          (HiddenDerivative.agreementIncidenceRatio n D A) n D A
          (coeffNatDegree Q) mu descent.actualDegree L ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
  classical
  obtain ⟨tailExceptional, htailCard, htailGood⟩ := htail
  have htailPower : ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.ordinaryTailCharge
          (HiddenDerivative.agreementIncidenceRatio n D A) n D
          (coeffNatDegree Q) (mu - descent.actualDegree) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization
          (challengeSpecialization descent.tail.equation z) P = 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
    refine ⟨tailExceptional, htailCard, ?_⟩
    intro z hz P hdegree hagree hroot
    apply powerAgreement_one_of_exactCorrelatedPair domain f g iota z P
    apply htailGood z hz P hdegree
    · rw [← powerBatchedWord_pair_eq f g iota z]
      exact hagree
    · exact hroot
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_firstOrder_hybridCurve_of_tail domain ![f, g] iota Q descent
      (coeffNatDegreeLE_coeffNatDegree Q) (by norm_num) hD hDL hLA hAn hchar _ htailPower
  refine ⟨exceptional, ?_, hgood⟩
  calc
    (exceptional.card : ℝ) ≤
        HiddenDerivative.ordinaryTailCharge
          (HiddenDerivative.agreementIncidenceRatio n D A) n D
          (coeffNatDegree Q) (mu - descent.actualDegree) +
          hybridCurveRegular n D 1 A (coeffNatDegree Q) mu descent.actualDegree L := hcard
    _ = HiddenDerivative.firstOrderExceptionCharge
        (HiddenDerivative.agreementIncidenceRatio n D A) n D A
        (coeffNatDegree Q) mu descent.actualDegree L := by
      simp [HiddenDerivative.firstOrderExceptionCharge, hybridCurveRegular,
        hybridCurveJointStageSum, HiddenDerivative.regularJointStageSum,
        HiddenDerivative.regularFiberStageSum]
      ring

/-- Optimizing the ordinary-tail transfer over the split and actual derivative degree gives the
optimized exception ceiling and the closed first-order exception bound. -/
theorem exists_exceptional_firstOrder_hybrid_optimized_of_tail
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n D A mu M : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (Q : DifferentialPolynomial E[X] 1)
    (descent : HiddenDerivative.FirstOrderHybridDescent Q mu M)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) (hMmu : M ≤ mu)
    (hchar : ringChar F = 0 ∨ D < ringChar F)
    (htail : HasOrdinaryTailTransfer (D := D) (A := A)
      (h := coeffNatDegree Q) (mu := mu) (e := descent.actualDegree)
      domain f g iota descent.tail.equation) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        HiddenDerivative.maxMinFirstOrderExceptionCharge
          (HiddenDerivative.agreementIncidenceRatio n D A) n D A
          (coeffNatDegree Q) mu M ∧
      exceptional.card ≤
        HiddenDerivative.firstOrderExceptionBound
          (HiddenDerivative.agreementIncidenceRatio n D A) n D A
          (coeffNatDegree Q) mu M ∧
      (exceptional.card : ℝ) ≤
        HiddenDerivative.firstOrderExceptionConstant
          (HiddenDerivative.agreementIncidenceRatio n D A) n D
          (coeffNatDegree Q) mu M ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (![f, g] t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain ![f, g] iota (D + 1) z P := by
  obtain ⟨L, hDL, hLA, hL⟩ := exists_curveRetentionMinimum
    (HiddenDerivative.firstOrderExceptionCharge
      (HiddenDerivative.agreementIncidenceRatio n D A) n D A
      (coeffNatDegree Q) mu descent.actualDegree) hDA
  obtain ⟨exceptional, hcardL, hgood⟩ :=
    exists_exceptional_firstOrder_hybrid_raw_of_tail domain f g iota Q descent
      hD hDL hLA hAn hchar htail
  have hmin : HiddenDerivative.firstOrderExceptionCharge
      (HiddenDerivative.agreementIncidenceRatio n D A) n D A
      (coeffNatDegree Q) mu descent.actualDegree L =
    HiddenDerivative.minFirstOrderExceptionCharge
      (HiddenDerivative.agreementIncidenceRatio n D A) n D A
      (coeffNatDegree Q) mu descent.actualDegree := by
    rw [hL]
    simp [curveRetentionMinimum, HiddenDerivative.minFirstOrderExceptionCharge, hDA]
  have hoptimized := HiddenDerivative.minFirstOrderExceptionCharge_le_maxMin
    (θ := HiddenDerivative.agreementIncidenceRatio n D A) (n := n) (D := D)
    (A := A) (h := coeffNatDegree Q) (μ := mu)
    (e := descent.actualDegree) (M := M) descent.actualDegree_le
  have hcardMin := hcardL.trans_eq hmin
  have hcardRaw := hcardMin.trans hoptimized
  have hcardCeil : exceptional.card ≤
      HiddenDerivative.firstOrderExceptionBound
        (HiddenDerivative.agreementIncidenceRatio n D A) n D A
        (coeffNatDegree Q) mu M := by
    unfold HiddenDerivative.firstOrderExceptionBound
    exact_mod_cast hcardRaw.trans (Nat.le_ceil _)
  have hclosed := HiddenDerivative.maxMinFirstOrderExceptionCharge_le_firstOrderExceptionConstant
    (h := coeffNatDegree Q) hD hDA hAn hMmu
  exact ⟨exceptional, hcardRaw, hcardCeil, hcardRaw.trans hclosed, hgood⟩

end

end ReedSolomon
