/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.FractionFieldResultant
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.Data.Polynomial.ResultantSpecialization
public import ArkLib.Data.Polynomial.SpecializationAvoidance
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import ArkLib.ToMathlib.MvPolynomial.RootContraction
public import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Ordinary symbolic root polynomials

A degree-zero differential polynomial with challenge-polynomial coefficients can be rearranged
as a polynomial in its root. This presentation preserves the root degree and irreducibility,
turns formal differentiation in the root into ordinary polynomial differentiation, and commutes
with challenge specialization. A nonzero derivative resultant then bounds the exceptional
challenges where a root can have zero separant.

## Main statements

* `ordinaryRootPresentation`: the polynomial representation in the root, independent coordinate,
  and challenge.
* `natDegree_ordinaryRootPresentation`, `irreducible_ordinaryRootPresentation` and
  `derivative_ordinaryRootPresentation`: degree, irreducibility, and differentiation laws.
* `resultant_derivative_ordinaryRootPresentation_ne_zero`: a nonzero derivative resultant for an
  irreducible equation with nonzero root derivative.
* `degreeX_ordinaryRootPresentation_le` and `eval_ordinaryRootPresentation`: challenge-height and
  specialization laws.
* `exists_exceptional_ordinary_separant`: a bound on challenges admitting a root with zero
  separant.

## References

* [BCHKS25]
* [DKT26]
-/

@[expose] public section

noncomputable section

namespace PolynomialDifferential

open Polynomial MvPolynomial

variable {F : Type*} [CommRing F]

/-- Reorder a degree-zero differential equation as a polynomial in its root. -/
def ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0) : F[X][X][X] :=
  Polynomial.map (Polynomial.Bivariate.swap (R := F)).toRingHom
    (Polynomial.map (uniqueAlgEquiv F[X] (Fin 1)).toRingHom
      (optionEquivLeft F[X] (Fin 1)
        (renameEquiv F[X] (Equiv.swap none (some 0)) Q)))

/-- The root degree of the presentation equals the degree in the differential variable. -/
theorem natDegree_ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0) :
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

/-- The root presentation is nonzero whenever its differential equation is nonzero. -/
theorem ordinaryRootPresentation_ne_zero {Q : DifferentialPolynomial F[X] 0} (hQ : Q ≠ 0) :
    ordinaryRootPresentation Q ≠ 0 := by
  intro hz
  apply hQ
  apply (renameEquiv F[X] (Equiv.swap none (some (0 : Fin 1)))).injective
  apply (optionEquivLeft F[X] (Fin 1)).injective
  apply Polynomial.map_injective (uniqueAlgEquiv F[X] (Fin 1)).toRingHom
    (uniqueAlgEquiv F[X] (Fin 1)).injective
  apply Polynomial.map_injective (Polynomial.Bivariate.swap (R := F)).toRingHom
    (Polynomial.Bivariate.swap (R := F)).injective
  simpa only [ordinaryRootPresentation, map_zero, Polynomial.map_zero] using hz

/-- Irreducibility is preserved by the coordinate changes in the root presentation. -/
theorem irreducible_ordinaryRootPresentation {Q : DifferentialPolynomial F[X] 0}
    (hQ : Irreducible Q) : Irreducible (ordinaryRootPresentation Q) := by
  have h₁ := hQ.map (renameEquiv F[X] (Equiv.swap none (some (0 : Fin 1))))
  have h₂ := h₁.map (optionEquivLeft F[X] (Fin 1))
  have h₃ := h₂.map (Polynomial.mapEquiv (uniqueAlgEquiv F[X] (Fin 1)).toRingEquiv)
  exact h₃.map (Polynomial.mapEquiv (Polynomial.Bivariate.swap (R := F)).toRingEquiv)

/-- Formal differentiation in the differential variable becomes root-polynomial differentiation.
-/
theorem derivative_ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0) :
    (ordinaryRootPresentation Q).derivative =
      ordinaryRootPresentation (MvPolynomial.pderiv (some 0) Q) := by
  unfold ordinaryRootPresentation
  rw [Polynomial.derivative_map, Polynomial.derivative_map,
    ← optionEquivLeft_pderiv_none]
  congr 3
  simpa only [renameEquiv_apply, Equiv.swap_apply_right] using
    pderiv_rename (Equiv.swap none (some (0 : Fin 1))).injective (some 0) Q

/-- Explicit monomial coordinates of the root presentation. -/
theorem ordinaryRootPresentation_monomial (m : Option (Fin 1) →₀ ℕ) (c : F[X]) :
    ordinaryRootPresentation (MvPolynomial.monomial m c) =
      Polynomial.C (c.map Polynomial.C * Polynomial.C (Polynomial.X ^ m none)) *
        Polynomial.X ^ m (some 0) := by
  classical
  simp [ordinaryRootPresentation, MvPolynomial.monomial_eq, Finsupp.prod_fintype,
    Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y,
    Polynomial.C_mul, mul_assoc]

/-- The challenge-variable degree of the presentation is bounded by coefficient degree. -/
theorem degreeX_ordinaryRootPresentation_le (Q : DifferentialPolynomial F[X] 0)
    {h : ℕ} (hQ : MvPolynomial.CoeffNatDegreeLE Q h) :
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

/-- Evaluation of the root presentation agrees with differential specialization. -/
theorem eval_ordinaryRootPresentation (Q : DifferentialPolynomial F[X] 0)
    (w : F) (P : F[X]) :
    ((ordinaryRootPresentation Q).map (Polynomial.evalRingHom (Polynomial.C w))).eval P =
      differentialSpecialization (challengeSpecialization Q w) P := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp [ordinaryRootPresentation, challengeSpecialization, differentialSpecialization,
      Polynomial.Bivariate.swap_C, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  | add Q R hQ hR =>
    simpa only [ordinaryRootPresentation, challengeSpecialization,
      differentialSpecialization, differentialSpecializationHom, map_add,
      Polynomial.map_add, Polynomial.eval_add, hQ, hR]
      using congrArg₂ (· + ·) hQ hR
  | mul_X Q i hQ =>
    cases i with
    | none =>
      have hX :
          ((ordinaryRootPresentation (MvPolynomial.X none)).map
            (Polynomial.evalRingHom (Polynomial.C w))).eval P = Polynomial.X := by
        simp [ordinaryRootPresentation, Polynomial.Bivariate.swap_Y]
      have hX' := hX
      simp only [ordinaryRootPresentation] at hX'
      simpa only [ordinaryRootPresentation, challengeSpecialization,
        differentialSpecialization, differentialSpecializationHom, map_mul,
        Polynomial.map_mul, Polynomial.eval_mul, MvPolynomial.map_X,
        MvPolynomial.aeval_X, hQ, hX'] using
          congrArg (· * Polynomial.X) hQ
    | some i =>
      have hi : i = 0 := by omega
      subst i
      have hX :
          ((ordinaryRootPresentation (MvPolynomial.X (some (0 : Fin 1)))).map
            (Polynomial.evalRingHom (Polynomial.C w))).eval P = P := by
        simp [ordinaryRootPresentation]
      have hX' := hX
      simp only [ordinaryRootPresentation] at hX'
      have hhasse : Polynomial.hasseDeriv 0 P = P := Polynomial.hasseDeriv_zero' P
      have hidx : (↑(0 : Fin 1) : ℕ) = 0 := rfl
      simpa only [ordinaryRootPresentation, challengeSpecialization,
        differentialSpecialization, differentialSpecializationHom, map_mul,
        Polynomial.map_mul, Polynomial.eval_mul, MvPolynomial.map_X,
        MvPolynomial.aeval_X, hQ, hX', hidx, hhasse] using congrArg (· * P) hQ

section

variable {F : Type*} [Field F]

/-- An irreducible equation with nonzero root derivative has a nonzero padded derivative
resultant for its root presentation. -/
theorem resultant_derivative_ordinaryRootPresentation_ne_zero
    {Q : DifferentialPolynomial F[X] 0} (hQ : Irreducible Q)
    (hder : MvPolynomial.pderiv (some 0) Q ≠ 0) :
    Polynomial.resultant (ordinaryRootPresentation Q)
      (ordinaryRootPresentation Q).derivative (Q.degreeOf (some 0))
      (Q.degreeOf (some 0) - 1) ≠ 0 := by
  let A := ordinaryRootPresentation Q
  have hirr : Irreducible A := irreducible_ordinaryRootPresentation hQ
  have hderA : A.derivative ≠ 0 := by
    rw [show A = ordinaryRootPresentation Q from rfl, derivative_ordinaryRootPresentation]
    exact ordinaryRootPresentation_ne_zero hder
  have hres := Polynomial.resultant_derivative_ne_zero_of_irreducible A hirr hderA
  rw [natDegree_ordinaryRootPresentation] at hres
  exact hres

/-- If the derivative resultant is nonzero at a challenge, every actual root has nonzero
separant. -/
theorem ordinary_separant_ne_zero_of_resultant_eval_ne_zero
    (Q : DifferentialPolynomial F[X] 0) (hpos : 0 < Q.degreeOf (some 0))
    (w : F) (P : F[X])
    (hresultant :
      (Polynomial.resultant (ordinaryRootPresentation Q)
        (ordinaryRootPresentation Q).derivative (Q.degreeOf (some 0))
        (Q.degreeOf (some 0) - 1)).eval (Polynomial.C w) ≠ 0)
    (hroot : differentialSpecialization (challengeSpecialization Q w) P = 0) :
    differentialSpecialization (separant (challengeSpecialization Q w) (Fin.last 0)) P ≠ 0 := by
  have hroot' : ((ordinaryRootPresentation Q).map
      (Polynomial.evalRingHom (Polynomial.C w))).eval P = 0 := by
    rw [eval_ordinaryRootPresentation]
    exact hroot
  let A := ordinaryRootPresentation Q
  have hAdegree : A.natDegree = Q.degreeOf (some 0) :=
    natDegree_ordinaryRootPresentation Q
  have hres : (Polynomial.evalRingHom (Polynomial.C w))
      (Polynomial.resultant A A.derivative (Q.degreeOf (some 0))
        (Q.degreeOf (some 0) - 1)) ≠ 0 := by
    simpa [Polynomial.evalRingHom, A] using hresultant
  have h := Polynomial.eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero
    (Polynomial.evalRingHom (Polynomial.C w)) A hAdegree.le hpos hres P hroot'
  rw [Polynomial.derivative_map, derivative_ordinaryRootPresentation,
    eval_ordinaryRootPresentation] at h
  simpa only [challengeSpecialization, separant, MvPolynomial.pderiv_map,
    show Fin.last 0 = (0 : Fin 1) from rfl] using h

open Classical in
/-- One exceptional set controls every ordinary root whose separant vanishes. -/
theorem exists_exceptional_ordinary_separant
    {Q : DifferentialPolynomial F[X] 0} (hQ : Irreducible Q)
    (hpos : 0 < Q.degreeOf (some 0))
    (hder : MvPolynomial.pderiv (some 0) Q ≠ 0)
    {h : ℕ} (hheight : MvPolynomial.CoeffNatDegreeLE Q h) :
    ∃ exceptional : Finset F,
      exceptional.card ≤ (2 * Q.degreeOf (some 0) - 1) * h ∧
      ∀ w ∉ exceptional, ∀ P : F[X],
        differentialSpecialization (challengeSpecialization Q w) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q w) (Fin.last 0)) P ≠ 0 := by
  classical
  let A := ordinaryRootPresentation Q
  let R := Polynomial.resultant A A.derivative (Q.degreeOf (some 0))
    (Q.degreeOf (some 0) - 1)
  have hR : R ≠ 0 := resultant_derivative_ordinaryRootPresentation_ne_zero hQ hder
  have hfinite : {w : F | R.eval (Polynomial.C w) = 0}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hR).preimage Polynomial.C_injective.injOn
  have hcard : hfinite.toFinset.card ≤ R.natDegree :=
    Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hR
      Polynomial.C_injective.injOn fun w hw ↦ hfinite.mem_toFinset.mp hw
  have hdegree : R.natDegree ≤ (2 * Q.degreeOf (some 0) - 1) * h := by
    have hAdegree : A.natDegree = Q.degreeOf (some 0) :=
      natDegree_ordinaryRootPresentation Q
    have hbound := Polynomial.natDegree_resultant_derivative_padded_le A
    rw [hAdegree] at hbound
    exact hbound.trans (Nat.mul_le_mul_left _ (degreeX_ordinaryRootPresentation_le Q hheight))
  refine ⟨hfinite.toFinset, hcard.trans hdegree, ?_⟩
  intro w hw P hroot
  apply ordinary_separant_ne_zero_of_resultant_eval_ne_zero Q hpos w P _ hroot
  intro hzero
  exact hw (hfinite.mem_toFinset.mpr hzero)

end

end PolynomialDifferential

end
