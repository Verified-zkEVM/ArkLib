/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridTransfer
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equation

/-!
# The ordinary tail of a first-order descent

The order-zero tail of a first-order hybrid descent satisfies the ordinary-tail transfer
interface. Its `Y₀` degree is at most the residual jet budget `mu - e`. When that budget is
positive, the exceptional-set theorem for ordinary equations applies. When it is zero, the tail
is independent of its jet, and outside at most `coeffNatDegree Q` challenges it has no
specialized root.

## Main statements

* `ReedSolomon.HiddenDerivative.FirstOrderHybridDescent.hasOrdinaryTailTransfer`: the tail of
  every first-order hybrid descent satisfies `ReedSolomon.HasOrdinaryTailTransfer`.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

open HiddenDerivative

/-- The order-zero tail of a first-order hybrid descent satisfies the ordinary-tail transfer
interface, with the ordinary-tail charge at the residual jet budget. -/
theorem HiddenDerivative.FirstOrderHybridDescent.hasOrdinaryTailTransfer
    {F E : Type*} [Field F] [Field E] [instF : DecidableEq F] [instE : DecidableEq E]
    [IsAlgClosed E] {n D A mu M : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    {Q : DifferentialPolynomial E[X] 1} (descent : FirstOrderHybridDescent Q mu M)
    (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n) :
    HasOrdinaryTailTransfer (D := D) (A := A) (h := coeffNatDegree Q) (mu := mu)
      (e := descent.actualDegree) domain f g iota descent.tail.equation := by
  obtain rfl : instF = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  obtain rfl : instE = fun a b ↦ Classical.propDecidable (a = b) := Subsingleton.elim _ _
  let h := coeffNatDegree Q
  let b := mu - descent.actualDegree
  have hheight : CoeffNatDegreeLE descent.tail.equation h :=
    descent.tail.natDegree_coeff_equation_le
      ((coeffNatDegreeLE_coeffNatDegree Q).iterate_pderiv _ descent.actualDegree)
  have hdegree : descent.tail.equation.degreeOf (some 0) ≤ b := descent.tail_rootDegree_le
  unfold HasOrdinaryTailTransfer ordinaryTailCharge
  by_cases hb : b = 0
  · obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_jet_independent_content
      descent.tail.equation descent.tail_nonzero (by omega) hheight
    refine ⟨exceptional, ?_, fun z hz P _ _ hroot ↦ (hgood z hz P hroot).elim⟩
    simpa only [b, hb, ↓reduceIte] using (show (exceptional.card : ℝ) ≤ h by exact_mod_cast hcard)
  · obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_ordinaryEquation
      domain f g iota descent.tail.equation D h b A descent.tail_nonzero
      (by omega) (by omega) (by omega) hAn hheight hdegree
    refine ⟨exceptional, ?_, fun z hz P hP hagree hroot ↦ hgood z hz P hP hroot hagree⟩
    have hcardReal : (exceptional.card : ℝ) ≤
        ((ordinaryFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D b h : ℚ) : ℝ) := by
      exact_mod_cast hcard
    simp only [b, hb, ↓reduceIte]
    convert hcardReal using 1
    simp [ordinaryFactorRaw, agreementIncidenceRatio, h, b]

end ReedSolomon
