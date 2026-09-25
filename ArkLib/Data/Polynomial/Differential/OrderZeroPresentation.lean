/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetDegree
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Order-zero differential polynomial presentation

This module converts between an order-zero differential polynomial and a univariate polynomial
in `Y₀` over `F[X]`, preserving total jet degree and differential specialization.

## Main statements

* `orderZeroAsPolynomial` and `orderZeroOfPolynomial`: the two polynomial presentations.
* `orderZeroOfPolynomial_jetTotalDegree` and `orderZeroAsPolynomial_eval`: degree and evaluation
  laws for the conversion.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace PolynomialDifferential

open Polynomial MvPolynomial

universe u

variable {F : Type u} [CommSemiring F]

/-- Reindex the order-zero variables so `Y₀` is the outer variable and `X` is its coefficient.
-/
def orderZeroVariableEquiv : JetVariable 0 ≃ Fin 2 :=
  (_root_.finSuccEquiv 1).symm.trans (Equiv.swap 0 1)

/-- Regard an order-zero differential equation as a polynomial in `Y₀` over `F[X]`. -/
def orderZeroAsPolynomial (Q : DifferentialPolynomial F 0) : F[X][X] :=
  Polynomial.map (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv F 1 (MvPolynomial.rename orderZeroVariableEquiv Q))

/-- Convert a polynomial in `Y₀` over `F[X]` to an order-zero differential equation. -/
def orderZeroOfPolynomial (R : F[X][X]) : DifferentialPolynomial F 0 :=
  (MvPolynomial.renameEquiv F orderZeroVariableEquiv).symm
    ((MvPolynomial.finSuccEquiv F 1).symm
      ((Polynomial.mapEquiv
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv).symm R))

/-- Converting a polynomial to an order-zero equation and back returns that polynomial. -/
@[simp]
theorem orderZeroAsPolynomial_orderZeroOfPolynomial (R : F[X][X]) :
    orderZeroAsPolynomial (orderZeroOfPolynomial R) = R := by
  unfold orderZeroAsPolynomial orderZeroOfPolynomial
  rw [← MvPolynomial.renameEquiv_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]
  change (Polynomial.mapEquiv
    (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv)
      ((Polynomial.mapEquiv
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv).symm R) = R
  exact RingEquiv.apply_symm_apply _ R

/-- The total jet degree of an order-zero equation is the degree of its outer polynomial. -/
theorem orderZeroOfPolynomial_jetTotalDegree (R : F[X][X]) :
    jetTotalDegree (orderZeroOfPolynomial R) = R.natDegree := by
  have hweight : jetTotalDegree (orderZeroOfPolynomial R) =
      degreeOf (some (0 : Fin 1)) (orderZeroOfPolynomial R) := by
    unfold jetTotalDegree
    rw [← MvPolynomial.weightedTotalDegree_piSingle (some (0 : Fin 1))]
    congr 1
    funext i
    rcases i with _ | j
    · simp [jetDegreeWeight]
    · fin_cases j
      simp [jetDegreeWeight]
  rw [hweight]
  have hdegree : degreeOf (0 : Fin 2)
      (MvPolynomial.rename orderZeroVariableEquiv (orderZeroOfPolynomial R)) =
        degreeOf (some (0 : Fin 1)) (orderZeroOfPolynomial R) := by
    have hrename := MvPolynomial.degreeOf_rename_of_injective
      orderZeroVariableEquiv.injective (some (0 : Fin 1))
        (p := orderZeroOfPolynomial R)
    rw [show orderZeroVariableEquiv (some (0 : Fin 1)) = (0 : Fin 2) by decide] at hrename
    exact hrename
  rw [← hdegree, ← MvPolynomial.natDegree_finSuccEquiv]
  have hmapdeg := Polynomial.natDegree_map_eq_of_injective
    (f := (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom)
    (MvPolynomial.uniqueAlgEquiv F (Fin 1)).injective
    (MvPolynomial.finSuccEquiv F 1
      (MvPolynomial.rename orderZeroVariableEquiv (orderZeroOfPolynomial R)))
  rw [← hmapdeg]
  change (orderZeroAsPolynomial (orderZeroOfPolynomial R)).natDegree = R.natDegree
  exact congrArg Polynomial.natDegree (orderZeroAsPolynomial_orderZeroOfPolynomial R)

/-- Evaluating the order-zero polynomial in `Y₀` is differential specialization. -/
theorem orderZeroAsPolynomial_eval (Q : DifferentialPolynomial F 0) (P : F[X]) :
    (orderZeroAsPolynomial Q).eval P = differentialSpecialization Q P := by
  let lhs : DifferentialPolynomial F 0 →ₐ[F] F[X] :=
    ((Polynomial.aeval P).restrictScalars F).comp
      (((Polynomial.mapAlgHom
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toAlgHom).restrictScalars F).comp
          ((MvPolynomial.finSuccEquiv F 1).toAlgHom.comp
            (MvPolynomial.renameEquiv F orderZeroVariableEquiv).toAlgHom))
  have hlhs : lhs Q = (orderZeroAsPolynomial Q).eval P := by rfl
  rw [← hlhs]
  change lhs Q = differentialSpecializationHom P Q
  congr 1
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · dsimp [lhs]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      differentialSpecialization_x]
    change Polynomial.eval P (Polynomial.map
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
          (MvPolynomial.finSuccEquiv F 1 (MvPolynomial.X (1 : Fin 2)))) = Polynomial.X
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide,
      MvPolynomial.finSuccEquiv_X_succ]
    rw [Polynomial.map_C, Polynomial.eval_C]
    simp [MvPolynomial.X]
  · fin_cases j
    dsimp [lhs]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      differentialSpecialization_jet]
    rw [show orderZeroVariableEquiv (some (0 : Fin 1)) = (0 : Fin 2) by decide]
    change Polynomial.eval P (Polynomial.map
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
          (MvPolynomial.finSuccEquiv F 1 (MvPolynomial.X (0 : Fin 2)))) =
      Polynomial.hasseDeriv 0 P
    rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.eval_X]
    simp


end PolynomialDifferential
