/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
import ArkLib.Data.Polynomial.SpecializationAvoidance
import ArkLib.Data.Polynomial.Bivariate
import ArkLib.ToMathlib.MvPolynomial.RootContraction
import Mathlib.Algebra.Polynomial.Bivariate

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

private def ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0) : F[X][X][X] :=
  Polynomial.map (Polynomial.Bivariate.swap (R := F)).toRingHom
    (Polynomial.map (uniqueAlgEquiv F[X] (Fin 1)).toRingHom
      (optionEquivLeft F[X] (Fin 1)
        (renameEquiv F[X] (Equiv.swap none (some 0)) Q)))

private theorem natDegree_ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0) :
    (ordinaryRootPresentation Q).natDegree = Q.degreeOf (some 0) := by
  rw [ordinaryRootPresentation,
    Polynomial.natDegree_map_eq_of_injective
      (f := (Polynomial.Bivariate.swap (R := F)).toRingHom)
      (Polynomial.Bivariate.swap (R := F)).injective,
    Polynomial.natDegree_map_eq_of_injective
      (f := (uniqueAlgEquiv F[X] (Fin 1)).toRingHom)
      (uniqueAlgEquiv F[X] (Fin 1)).injective,
    natDegree_optionEquivLeft]
  simpa only [renameEquiv_apply, Equiv.swap_apply_right] using
    degreeOf_rename_of_injective (p := Q)
      (Equiv.swap none (some (0 : Fin 1))).injective (some 0)

private theorem ordinaryRootPresentation_ne_zero {Q : DifferentialPolynomial F[X] 0}
    (hQ : Q ≠ 0) : ordinaryRootPresentation Q ≠ 0 := by
  intro hz
  apply hQ
  apply (renameEquiv F[X] (Equiv.swap none (some (0 : Fin 1)))).injective
  apply (optionEquivLeft F[X] (Fin 1)).injective
  apply Polynomial.map_injective (uniqueAlgEquiv F[X] (Fin 1)).toRingHom
    (uniqueAlgEquiv F[X] (Fin 1)).injective
  apply Polynomial.map_injective (Polynomial.Bivariate.swap (R := F)).toRingHom
    (Polynomial.Bivariate.swap (R := F)).injective
  simpa only [ordinaryRootPresentation, map_zero, Polynomial.map_zero] using hz

private theorem ordinaryRootPresentation_monomial
    (m : Option (Fin 1) →₀ ℕ) (c : F[X]) :
    ordinaryRootPresentation (MvPolynomial.monomial m c) =
      Polynomial.C (c.map Polynomial.C * Polynomial.C (Polynomial.X ^ m none)) *
        Polynomial.X ^ m (some 0) := by
  classical
  simp [ordinaryRootPresentation, MvPolynomial.monomial_eq, Finsupp.prod_fintype,
    Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y, Polynomial.C_mul, mul_assoc]

private theorem degreeX_ordinaryRootPresentation_le
    (Q : DifferentialPolynomial F[X] 0) {h : ℕ}
    (hQ : MvPolynomial.CoeffNatDegreeLE Q h) :
    Polynomial.Bivariate.degreeX (ordinaryRootPresentation Q) ≤ h := by
  classical
  have hsum : ordinaryRootPresentation Q =
      ∑ m ∈ Q.support,
        ordinaryRootPresentation (MvPolynomial.monomial m (Q.coeff m)) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [ordinaryRootPresentation, map_sum, Polynomial.map_sum]
  rw [hsum]
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i _
  rw [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  rw [ordinaryRootPresentation_monomial, Polynomial.coeff_C_mul_X_pow]
  split_ifs
  · exact (Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, Nat.add_zero] using
        (Polynomial.natDegree_map_le (p := Q.coeff m)
          (f := Polynomial.C)).trans (hQ m)))
  · simp

private theorem ordinaryRootPresentation_add (Q R : DifferentialPolynomial F[X] 0) :
    ordinaryRootPresentation (Q + R) = ordinaryRootPresentation Q + ordinaryRootPresentation R := by
  simp only [ordinaryRootPresentation, Polynomial.map_add, map_add]

private theorem ordinaryRootPresentation_mul (Q R : DifferentialPolynomial F[X] 0) :
    ordinaryRootPresentation (Q * R) = ordinaryRootPresentation Q * ordinaryRootPresentation R := by
  simp only [ordinaryRootPresentation, Polynomial.map_mul, map_mul]

private theorem eval_ordinaryRootPresentation_C (c : F[X]) (w : F) (P : F[X]) :
    ((ordinaryRootPresentation (MvPolynomial.C c)).map
      (Polynomial.evalRingHom (Polynomial.C w))).eval P = Polynomial.C (c.eval w) := by
  have hm : (MvPolynomial.C c : DifferentialPolynomial F[X] 0) = MvPolynomial.monomial 0 c := by
    simp [MvPolynomial.monomial_eq]
  rw [hm, ordinaryRootPresentation_monomial]
  simp

private theorem eval_ordinaryRootPresentation_X_none (w : F) (P : F[X]) :
    ((ordinaryRootPresentation (MvPolynomial.X none)).map
      (Polynomial.evalRingHom (Polynomial.C w))).eval P = Polynomial.X := by
  have hm : (MvPolynomial.X none : DifferentialPolynomial F[X] 0) =
      MvPolynomial.monomial (Finsupp.single none 1) 1 := by
    simp [MvPolynomial.monomial_eq]
  rw [hm, ordinaryRootPresentation_monomial]
  simp

private theorem eval_ordinaryRootPresentation_X_some (w : F) (P : F[X]) :
    (((ordinaryRootPresentation (MvPolynomial.X (some (0 : Fin 1)))).map
      (Polynomial.evalRingHom (Polynomial.C w))).eval P) = P := by
  have hm : (MvPolynomial.X (some (0 : Fin 1)) : DifferentialPolynomial F[X] 0) =
      MvPolynomial.monomial (Finsupp.single (some (0 : Fin 1)) 1) 1 := by
    simp [MvPolynomial.monomial_eq]
  rw [hm, ordinaryRootPresentation_monomial]
  simp

private theorem eval_ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0)
    (w : F) (P : F[X]) :
    ((ordinaryRootPresentation Q).map (Polynomial.evalRingHom (Polynomial.C w))).eval P =
      differentialSpecialization (challengeSpecialization Q w) P := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
      rw [eval_ordinaryRootPresentation_C]
      simp [challengeSpecialization, differentialSpecialization]
  | add Q R hQ hR =>
      rw [ordinaryRootPresentation_add, Polynomial.map_add, Polynomial.eval_add, hQ, hR]
      simp only [challengeSpecialization, differentialSpecialization, map_add]
  | mul_X Q i hQ =>
      rw [ordinaryRootPresentation_mul, Polynomial.map_mul, Polynomial.eval_mul,
        hQ]
      simp only [challengeSpecialization, differentialSpecialization, map_mul]
      cases i with
      | none =>
          rw [eval_ordinaryRootPresentation_X_none]
          simp [differentialSpecializationHom]
      | some i =>
          have hi : i = 0 := by omega
          subst i
          rw [eval_ordinaryRootPresentation_X_some]
          simp [differentialSpecializationHom]

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
