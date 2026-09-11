/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.OrdinaryTail
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.UnifiedCurve

/-!
# Unconditional optimized first-order curve recovery

The ordinary tail and the actual regular stages choose their retention thresholds independently.
The zero root-degree tail retains its separate height bound. No recovery premise is assumed.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative
open HiddenDerivative.SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

open Classical in
/-- The actual ordinary tail satisfies the free-retention curve bound,
including root degree zero. -/
theorem HiddenDerivative.FirstOrderHybridDescent.hasOrdinaryCurveTailTransfer
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E]
    {n D A L h mu M ell : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (descent : FirstOrderHybridDescent Q mu M h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDn : D + 2 ≤ n)
    (hDL : D < L) (hLA : L ≤ A) (hAn : A ≤ n) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤
        hybridCurveTail n D ell (mu - descent.actualDegree) h A L ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization descent.tail.equation z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  classical
  have hheight : ChallengeHeightLE descent.tail.equation h :=
    descent.tail_challengeHeight_le
  have hdegree := descent.tail_rootDegree_le
  by_cases hb : mu - descent.actualDegree = 0
  · obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryContent
      descent.tail.equation descent.tail_nonzero (by omega) hheight
    refine ⟨exceptional, ?_, ?_⟩
    · simpa only [hybridCurveTail, hb, if_pos] using
        (show (exceptional.card : ℝ) ≤ h by exact_mod_cast hcard)
    · intro z hz P _ _ hroot
      exact (hgood z hz P hroot).elim
  · obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_ordinaryPowerEquation_freeRetention domain values iota
        descent.tail.equation D h (mu - descent.actualDegree) L A
          descent.tail_nonzero hD hell (by omega) hDn hDL hLA hAn hheight hdegree
    refine ⟨exceptional, ?_, fun z hz P hP hagree hroot ↦
      hgood z hz P hP hroot hagree⟩
    simpa only [hybridCurveTail, if_neg hb] using
      (show (exceptional.card : ℝ) ≤
        (ordinaryUnifiedPowerFactorAt n D ell (mu - descent.actualDegree) h A L : ℝ) by
          exact_mod_cast hcard)

open Classical in
/-- An explicit nonzero first-order equation gives one exceptional set before every challenge
and candidate. Both retention minima precede the maximum over actual derivative degrees.
Recovered constituents are over the original field and have equality of full agreement sets. -/
theorem exists_exceptional_firstOrder_hybridCurve_optimized
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E]
    {n D A h mu M ell : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1)
    (hQ : Q ≠ 0) (hweight : jetWeight Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hheight : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDn : D + 2 ≤ n)
    (hDA : D < A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D (jetDegree Q (1 : Fin 2)) < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ hybridCurveOptimized n D ell A h mu M ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hcharE : ringChar E = 0 ∨ jetDegree Q (1 : Fin 2) < ringChar E := by
    have heq : ringChar E = ringChar F := by
      let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
      exact ringChar.eq E (ringChar F)
    rw [heq]
    exact hchar.imp_right (fun h ↦ (le_max_right D _).trans_lt h)
  obtain ⟨descent⟩ := exists_firstOrderHybridDescent Q hQ hweight hdegree hheight hcharE
  apply exists_exceptional_firstOrder_hybridCurve_optimized_of_tail
    domain values iota Q descent hell hD hDA hAn
      (hchar.imp_right (fun h ↦ (le_max_left D _).trans_lt h))
  intro L hDL hLA
  exact descent.hasOrdinaryCurveTailTransfer domain values iota Q
    hell hD hDn hDL hLA hAn

end

end ReedSolomon
