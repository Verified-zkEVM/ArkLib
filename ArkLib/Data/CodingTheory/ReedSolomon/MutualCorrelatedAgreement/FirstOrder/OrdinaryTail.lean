/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridTransfer
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equations.Equation
/-!
# The actual ordinary tail of the first-order descent

This file discharges the ordinary-tail premise of the first-order hybrid transfer.  The tail
equation supplied by `FirstOrderHybridDescent` has root degree at most the residual jet budget.
When that budget is positive, the ordinary equation theorem applies.  When it is zero, the
content-exception theorem rules out every specialized root away from at most `h` challenges.
-/

@[expose] public section

open Polynomial

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential SymbolicSeparantChain

set_option autoImplicit false

/-- The root degree of the ordinary tail is bounded by the jet budget left after the actual
first-order degree. -/
theorem FirstOrderHybridDescent.tail_rootDegree_le
    {F : Type*} [Field F] {Q : DifferentialPolynomial F[X] 1} {mu M h : ℕ}
    (descent : FirstOrderHybridDescent Q mu M h) :
    descent.tail.equation.degreeOf (some 0) ≤ mu - descent.actualDegree := by
  have hrename := MvPolynomial.degreeOf_rename_of_injective
    (jetPrefixEmbedding (0 : Fin 2)).injective (some (0 : Fin 1))
    (p := descent.tail.equation)
  rw [descent.tail.ambient_eq] at hrename
  have hstage := (jetDegree_le_jetWeight
    (firstOrderDerivativeStage Q descent.actualDegree) (0 : Fin 2)).trans
      (descent.stage_jetWeight_le descent.actualDegree le_rfl)
  rw [show jetPrefixEmbedding (0 : Fin 2) (some (0 : Fin 1)) = some (0 : Fin 2) by rfl]
    at hrename
  exact hrename.symm.le.trans hstage

end ReedSolomon.HiddenDerivative

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative
open HiddenDerivative.SymbolicSeparantChain

set_option autoImplicit false

open Classical in
/-- The actual order-zero tail of a first-order descent satisfies the exact tail interface used
by the hybrid transfer.  The statement uses classical decidable equality locally so the
agreement-set instance agrees definitionally with the ordinary equation theorem. -/
theorem HiddenDerivative.FirstOrderHybridDescent.hasOrdinaryTailTransfer
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n D A h mu M : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1)
    (descent : FirstOrderHybridDescent Q mu M h)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) :
    HasOrdinaryTailTransfer (D := D) (A := A) (h := h) (mu := mu)
      (e := descent.actualDegree) domain f g iota descent.tail.equation := by
  classical
  let b := mu - descent.actualDegree
  have hheight : ChallengeHeightLE descent.tail.equation h :=
    descent.tail_challengeHeight_le
  have hdegree : descent.tail.equation.degreeOf (some 0) ≤ b :=
    descent.tail_rootDegree_le
  by_cases hb : b = 0
  · have hdegree0 : descent.tail.equation.degreeOf (some 0) = 0 := by omega
    obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryContent
      descent.tail.equation descent.tail_nonzero hdegree0 hheight
    refine ⟨exceptional, ?_, ?_⟩
    · change (exceptional.card : ℝ) ≤ HiddenDerivative.hybridOrdinaryRaw
        (HiddenDerivative.hybridTheta n D A) n D h b
      simpa only [HiddenDerivative.hybridOrdinaryRaw, hb, if_pos]
        using (show (exceptional.card : ℝ) ≤ h by exact_mod_cast hcard)
    · intro z hz P hP hagree hroot
      exact (hgood z hz P hroot).elim
  · obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryEquation
      domain f g iota descent.tail.equation D h b A descent.tail_nonzero
      (by omega) (by omega) (by omega) hAn hheight hdegree
    refine ⟨exceptional, ?_, ?_⟩
    · change (exceptional.card : ℝ) ≤ HiddenDerivative.hybridOrdinaryRaw
        (HiddenDerivative.hybridTheta n D A) n D h b
      have hcardReal : (exceptional.card : ℝ) ≤
          ((ordinaryFactorRaw
            (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D b h : ℚ) : ℝ) := by
        exact_mod_cast hcard
      norm_num [ordinaryFactorRaw, HiddenDerivative.hybridOrdinaryRaw,
        HiddenDerivative.hybridTheta, hb] at hcardReal ⊢
      exact hcardReal
    · intro z hz P hP hagree hroot
      exact hgood z hz P hP hroot hagree

end ReedSolomon
