/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.RootPresentation
/-!
# Exceptional challenges of ordinary content

An equation independent of its root variable can vanish identically only at a number of
challenges bounded by its coefficient height. This supplies the zero-degree ordinary tail
and the content charge in factor aggregation.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Polynomial MvPolynomial PolynomialDifferential

variable {F : Type*} [Field F]

open Classical in
/-- Nonzero root-independent content contributes at most its challenge height. -/
theorem exists_exceptional_ordinaryContent
    (Q : DifferentialPolynomial F[X] 0) (hQ : Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = 0) {h : ℕ} (hheight : ChallengeHeightLE Q h) :
    ∃ exceptional : Finset F, exceptional.card ≤ h ∧
      ∀ w ∉ exceptional, ∀ P : F[X],
        differentialSpecialization (challengeSpecialization Q w) P ≠ 0 := by
  classical
  let A := ordinaryRootPresentation Q
  let B := A.coeff 0
  have hAeq : A = Polynomial.C B :=
    Polynomial.eq_C_of_natDegree_eq_zero ((natDegree_ordinaryRootPresentation Q).trans hdegree)
  have hB : B ≠ 0 := by
    intro hz
    apply ordinaryRootPresentation_ne_zero hQ
    change A = 0
    rw [hAeq, hz, Polynomial.C_0]
  have hBheight : B.natDegree ≤ h :=
    (Polynomial.Bivariate.coeff_natDegree_le_degreeX A 0).trans
      (degreeX_ordinaryRootPresentation_le Q hheight)
  have hfinite : {w : F | B.eval (Polynomial.C w) = 0}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hB).preimage Polynomial.C_injective.injOn
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · exact (Polynomial.finite_polynomial_specializations_eq_zero_card_le B hB _
      (fun w hw ↦ hfinite.mem_toFinset.mp hw)).trans hBheight
  · intro w hw P hroot
    apply hw
    apply hfinite.mem_toFinset.mpr
    change B.eval (Polynomial.C w) = 0
    rw [← eval_ordinaryRootPresentation] at hroot
    change (A.map (Polynomial.evalRingHom (Polynomial.C w))).eval P = 0 at hroot
    simpa only [hAeq, Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom] using hroot

end ReedSolomon.HiddenDerivative
