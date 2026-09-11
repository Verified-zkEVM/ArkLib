/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CurveMCA
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.UnifiedCurve

/-!
# Unified ordinary tail for retained first-order curves

The retained squarefree first-order transfer leaves one order-zero content/resultant equation.
This module discharges that seam with the common all-characteristic `ordinaryPsi` theorem and
then combines it with the regular curve locus. The exceptional set is fixed before the challenge
and candidate, and the conclusion retains equality of the complete agreement set.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

/-- The unified positive-part coefficient is bounded by the retained coarse tail expression. -/
theorem ordinaryUnifiedPowerFactorRaw_le_retainedOrdinaryMCARaw
    {theta : ℚ} {n D ell B H : ℕ}
    (htheta : 0 ≤ theta) (hD : 1 ≤ D) (hB : 1 ≤ B) :
    (ordinaryUnifiedPowerFactorRaw theta n D ell B H : ℝ) ≤
      retainedOrdinaryMCARaw (theta : ℝ) n D ell B 0 H := by
  have hpsi : ordinaryPsi D B ≤ 4 * D * B := ordinaryPsi_le_four_mul hD hB
  have hpsiReal : ((H * ordinaryPsi D B : ℕ) : ℝ) ≤
      (H * (4 * D * B) : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left H hpsi
  have hthetaReal : (0 : ℝ) ≤ (theta : ℝ) := by exact_mod_cast htheta
  have hmiddle : (theta : ℝ) * ((ell * B + H * ordinaryPsi D B : ℕ) : ℝ) ≤
      (theta : ℝ) * ((H + ell * B + 4 * D * B * H : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hthetaReal
    push_cast
    push_cast at hpsiReal
    ring_nf at hpsiReal ⊢
    linarith
  simp only [retainedOrdinaryMCARaw, Nat.reduceMul, Nat.mul_one, Nat.zero_add]
  unfold ordinaryUnifiedPowerFactorRaw
  push_cast
  push_cast at hmiddle
  ring_nf at hmiddle ⊢
  linarith

open Classical in
/-- The common unified ordinary theorem supplies the retained content/resultant tail. -/
theorem hasRetainedOrdinaryCurveTransfer_of_unified
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n D ell A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E) (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hell : 0 < ell) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetWeight Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : ChallengeHeightLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    HasRetainedOrdinaryCurveTransfer (D := D) (A := A)
      (B := B) (M := M) (H := H) domain values iota (singularCurveEquation Q) := by
  let b := B * (2 * M + 1)
  let h := H * (2 * M + 1)
  have hcharE : ringChar E = 0 ∨ max D M < ringChar E := by
    rwa [ringChar_eq_of_injective_fieldHom iota]
  have htailQ : singularCurveEquation Q ≠ 0 :=
    singularCurveEquation_ne_zero Q hQ hderiv
      (hcharE.imp_right fun hmax => (Nat.le_max_right D M).trans_lt hmax)
  have hb : 1 ≤ b := by
    dsimp only [b]
    exact Nat.mul_pos (hM.trans hMB) (by omega)
  have htailDegree : (singularCurveEquation Q).degreeOf (some 0) ≤ b := by
    apply (singularCurveEquation_degree_le Q hQ hjet hderiv hMB).trans
    calc
      ordinaryDegreeEnvelope B M ≤ B + 2 * B * M := ordinaryDegreeEnvelope_le B M
      _ = b := by simp only [b]; ring
  have htailHeight : ChallengeHeightLE (singularCurveEquation Q) h := by
    intro u
    apply (singularCurveEquation_challengeHeightLE Q hQ hheight hM hderiv u).trans
    apply (resultantChallengeEnvelope_le H M).trans
    dsimp only [h]
    nlinarith
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_ordinaryPowerEquation_unified domain values iota
      (singularCurveEquation Q) D h b A htailQ (by omega) hell hb hDA hAn
      htailHeight htailDegree
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardReal : (exceptional.card : ℝ) ≤
        (ordinaryUnifiedPowerFactorRaw
          (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell b h : ℚ) := by
      exact_mod_cast hcard
    apply hcardReal.trans
    have htheta : (0 : ℚ) ≤
        ((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ) := by positivity
    have hunified := ordinaryUnifiedPowerFactorRaw_le_retainedOrdinaryMCARaw
      (theta := ((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) (n := n) (D := D)
      (ell := ell) (B := b) (H := h) htheta hD hb
    dsimp only [b, h] at hunified
    simpa [retainedOrdinaryMCARaw, HiddenDerivative.hybridTheta] using hunified
  · intro z hz P hdegree hagree hroot
    simpa only using hgood z hz P hdegree hroot hagree

open Classical in
/-- General positive-derivative retained squarefree curve transfer using the common ordinary
budget. This is the shared semantic theorem consumed by concrete polynomial curves and by its
degree-one line specialization. -/
theorem exists_exceptional_retainedSquarefreeCurveMCA_unified
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell)
    (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetWeight Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : ChallengeHeightLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ retainedSquarefreeCurveMCARaw
        (HiddenDerivative.hybridTheta n D A) n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  apply exists_exceptional_retainedSquarefreeCurveMCA_of_tail domain values iota Q hQ
    hD hDL hLA hAn (Nat.add_pos_left hell H) hM hMB hjet hderiv hheight hchar
  exact hasRetainedOrdinaryCurveTransfer_of_unified domain values iota Q hQ hD hell
    (hDL.trans hLA) hAn hM hMB hjet hderiv hheight hchar

end

end ReedSolomon.FirstOrder.Squarefree
