/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RootPresentation

/-!
# Exceptional challenges for jet-independent equations

Over a domain, a nonzero ordinary differential equation that is independent of its jet variable
can vanish under polynomial specialization only at a bounded set of challenge values. The
coefficient-degree bound controls the size of this set.

## Main statements

* `PolynomialDifferential.exists_exceptional_jet_independent_content`: the exceptional challenge
  set for a nonzero equation of jet degree zero.

## References
-/

@[expose] public section

noncomputable section

namespace PolynomialDifferential

open Polynomial MvPolynomial

variable {F : Type*} [CommRing F]

/-- Over an integral domain, a nonzero ordinary differential equation of jet degree zero
specializes to a nonzero polynomial for every polynomial input outside a set of at most `h`
challenge values, provided each challenge coefficient has degree at most `h`. -/
theorem exists_exceptional_jet_independent_content
    [IsDomain F]
    (Q : DifferentialPolynomial F[X] 0) (hQ : Q ≠ 0)
    (hdegree : Q.degreeOf (some 0) = 0) {h : ℕ}
    (hheight : MvPolynomial.CoeffNatDegreeLE Q h) :
    ∃ exceptional : Finset F, exceptional.card ≤ h ∧
      ∀ w ∉ exceptional, ∀ P : F[X],
        differentialSpecialization (challengeSpecialization Q w) P ≠ 0 := by
  classical
  let A := ordinaryRootPresentation Q
  let B := A.coeff 0
  have hAeq : A = Polynomial.C B :=
    Polynomial.eq_C_of_natDegree_eq_zero
      ((natDegree_ordinaryRootPresentation Q).trans hdegree)
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
  · exact (Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hB
      (x := Polynomial.C) (s := hfinite.toFinset) Polynomial.C_injective.injOn
      (fun w hw ↦ hfinite.mem_toFinset.mp hw)).trans hBheight
  · intro w hw P hroot
    apply hw
    apply hfinite.mem_toFinset.mpr
    change B.eval (Polynomial.C w) = 0
    rw [← eval_ordinaryRootPresentation] at hroot
    change (A.map (Polynomial.evalRingHom (Polynomial.C w))).eval P = 0 at hroot
    simpa only [hAeq, Polynomial.map_C, Polynomial.eval_C,
      Polynomial.coe_evalRingHom] using hroot

end PolynomialDifferential
