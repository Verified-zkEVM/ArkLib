/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Factorwise
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.SingularTail
public import ArkLib.Data.MvPolynomial.RadicalSplit.Separable
public import ArkLib.Data.MvPolynomial.WeightedDegree.Products
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.Data.Polynomial.ResultantSpecialization
public import ArkLib.Data.Polynomial.Differential.OrderZeroPresentation
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
public import ArkLib.ToMathlib.MvPolynomial.PDeriv
public import ArkLib.ToMathlib.MvPolynomial.SupportWeight
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Singular-tail equations for first-order squarefree agreement

This file builds a nonzero order-zero equation from the radical content and the padded derivative
resultant of the positive-jet factor. Its roots contain every solution outside the regular branch,
and its degree fits the ordinary-degree envelope used by factorwise list counting.

## Main statements

* `positiveJetFactor`: the positive-degree radical factor returned to first-order coordinates.
* `singularEquation`: the order-zero equation combining radical content and a derivative resultant.
* `fixedWordSingularTailOfBounds`: the regular-branch and singular-tail data for a first-order
  equation with declared degree bounds.
* `finite_squarefree_agreement_solutions_card_le`: the resulting fixed-word agreement bound.
* Coordinate changes and degree, coefficient, and specialization identities for these equations.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

noncomputable section

universe u

variable {F : Type u} [Field F]

/-- The first-order variables with `Y₁` moved to the distinguished root coordinate. -/
def firstOrderRootEquiv : JetVariable 1 ≃ Option (Fin 2) :=
  Equiv.swap none (some 1)

/-- Express a first-order equation with `Y₁` as its distinguished root variable. -/
def firstOrderRootCoordinates (Q : DifferentialPolynomial F 1) :
    MvPolynomial (Option (Fin 2)) F :=
  renameEquiv F firstOrderRootEquiv Q

/-- Recover a first-order equation from coordinates with `Y₁` in the root position. -/
def fromFirstOrderRootCoordinates (R : MvPolynomial (Option (Fin 2)) F) :
    DifferentialPolynomial F 1 :=
  renameEquiv F firstOrderRootEquiv.symm R

/-- Returning a root-coordinate polynomial to first-order coordinates is inverse to the
coordinate change. -/
@[simp]
theorem firstOrderRootCoordinates_fromFirstOrderRootCoordinates
    (R : MvPolynomial (Option (Fin 2)) F) :
    firstOrderRootCoordinates (fromFirstOrderRootCoordinates R) = R := by
  simp [firstOrderRootCoordinates, fromFirstOrderRootCoordinates]

/-- Putting a first-order equation in root coordinates and recovering it returns the equation. -/
@[simp]
theorem fromFirstOrderRootCoordinates_firstOrderRootCoordinates
    (Q : DifferentialPolynomial F 1) :
    fromFirstOrderRootCoordinates (firstOrderRootCoordinates Q) = Q := by
  simp [firstOrderRootCoordinates, fromFirstOrderRootCoordinates]

/-- The degree of the distinguished root coordinate is the degree in `Y₁`. -/
theorem firstOrderRootCoordinates_rootDegree (Q : DifferentialPolynomial F 1) :
    degreeOf none (firstOrderRootCoordinates Q) = jetDegree Q 1 := by
  simpa only [firstOrderRootCoordinates, renameEquiv_apply, firstOrderRootEquiv,
    Equiv.swap_apply_right, jetDegree] using
      (degreeOf_rename_of_injective firstOrderRootEquiv.injective
        (some (1 : Fin 2)) (p := Q))

/-- The jet weight in root coordinates: `Y₁` and `Y₀` have weight one, while `X` has weight
zero. -/
def rootJetWeight : Option (Fin 2) → ℕ
  | none => 1
  | some j => if j = 0 then 1 else 0

/-- Weighted degree in root coordinates equals total jet degree in differential coordinates. -/
theorem firstOrderRootCoordinates_weightedTotalDegree
    (Q : DifferentialPolynomial F 1) :
    (firstOrderRootCoordinates Q).weightedTotalDegree rootJetWeight = jetTotalDegree Q := by
  rw [firstOrderRootCoordinates, renameEquiv_apply,
    weightedTotalDegree_rename_of_injective firstOrderRootEquiv.injective]
  congr 1
  funext v
  rcases v with _ | j
  · rfl
  · fin_cases j <;> rfl

/-- Weighted degree of a root-coordinate equation equals the total jet degree after recovery. -/
theorem fromFirstOrderRootCoordinates_weightedTotalDegree
    (R : MvPolynomial (Option (Fin 2)) F) :
    R.weightedTotalDegree rootJetWeight =
      jetTotalDegree (fromFirstOrderRootCoordinates R) := by
  calc
    R.weightedTotalDegree rootJetWeight =
        (firstOrderRootCoordinates (fromFirstOrderRootCoordinates R)).weightedTotalDegree
          rootJetWeight := by
      rw [firstOrderRootCoordinates_fromFirstOrderRootCoordinates]
    _ = jetTotalDegree (fromFirstOrderRootCoordinates R) :=
      firstOrderRootCoordinates_weightedTotalDegree _

/-- The positive-degree radical factor, returned to first-order coordinates. -/
def positiveJetFactor (Q : DifferentialPolynomial F 1) : DifferentialPolynomial F 1 :=
  fromFirstOrderRootCoordinates
    (radicalPrimPart none (firstOrderRootCoordinates Q))

/-- Returning the positive-jet factor to root coordinates recovers the radical primitive part. -/
@[simp]
theorem firstOrderRootCoordinates_positiveJetFactor (Q : DifferentialPolynomial F 1) :
    firstOrderRootCoordinates (positiveJetFactor Q) =
      radicalPrimPart none (firstOrderRootCoordinates Q) := by
  simp [positiveJetFactor]

/-- The positive-jet factor has no larger total jet degree than its input. -/
theorem positiveJetFactor_jetTotalDegree_le (Q : DifferentialPolynomial F 1) :
    jetTotalDegree (positiveJetFactor Q) ≤ jetTotalDegree Q := by
  have hdegree := map_radicalPrimPart_le
    (d := fun R ↦ R.weightedTotalDegree rootJetWeight)
    (fun p q hp hq ↦ weightedTotalDegree_mul rootJetWeight p q hp hq)
    none (firstOrderRootCoordinates Q)
  calc
    jetTotalDegree (positiveJetFactor Q) =
        (radicalPrimPart none (firstOrderRootCoordinates Q)).weightedTotalDegree
          rootJetWeight := by
      simpa only [positiveJetFactor, firstOrderRootCoordinates_fromFirstOrderRootCoordinates]
        using (fromFirstOrderRootCoordinates_weightedTotalDegree
          (radicalPrimPart none (firstOrderRootCoordinates Q))).symm
    _ ≤ (firstOrderRootCoordinates Q).weightedTotalDegree rootJetWeight := hdegree
    _ = jetTotalDegree Q := firstOrderRootCoordinates_weightedTotalDegree Q

/-- The `Y₁` degree of the positive-jet factor is at most that of the input. -/
theorem positiveJetFactor_yOneDegree_le (Q : DifferentialPolynomial F 1) :
    jetDegree (positiveJetFactor Q) 1 ≤ jetDegree Q 1 := by
  change degreeOf (some 1) (positiveJetFactor Q) ≤ degreeOf (some 1) Q
  have hleft := degreeOf_rename_of_injective firstOrderRootEquiv.injective
    (some (1 : Fin 2)) (p := positiveJetFactor Q)
  have hright := degreeOf_rename_of_injective firstOrderRootEquiv.injective
    (some (1 : Fin 2)) (p := Q)
  calc
    degreeOf (some 1) (positiveJetFactor Q) =
        degreeOf none (firstOrderRootCoordinates (positiveJetFactor Q)) := by
          rw [firstOrderRootCoordinates, renameEquiv_apply]
          change degreeOf (some 1) (positiveJetFactor Q) =
            degreeOf (firstOrderRootEquiv (some 1))
              (rename firstOrderRootEquiv (positiveJetFactor Q))
          exact hleft.symm
    _ = degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q)) := by
      rw [firstOrderRootCoordinates_positiveJetFactor]
    _ ≤ degreeOf none (firstOrderRootCoordinates Q) :=
      degreeOf_radicalPrimPart_le none none _
    _ = degreeOf (some 1) Q := by
      rw [firstOrderRootCoordinates, renameEquiv_apply]
      change degreeOf (firstOrderRootEquiv (some 1))
          (rename firstOrderRootEquiv Q) = degreeOf (some 1) Q
      exact hright

/-- Regard the remaining variables `(Y₀, X)` as a polynomial in `Y₀` over `F[X]`. -/
def remainingPolynomialEquiv : MvPolynomial (Fin 2) F ≃+* F[X][X] :=
  (MvPolynomial.finSuccEquiv F 1).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingEquiv)

/-- The polynomial degree in `Y₀` is the `Y₀` degree in the multivariate presentation. -/
theorem remainingPolynomialEquiv_natDegree (R : MvPolynomial (Fin 2) F) :
    (remainingPolynomialEquiv R).natDegree = degreeOf (0 : Fin 2) R := by
  unfold remainingPolynomialEquiv
  rw [RingEquiv.trans_apply]
  change (Polynomial.map (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv F 1 R)).natDegree = degreeOf (0 : Fin 2) R
  rw [Polynomial.natDegree_map_eq_of_injective
    (MvPolynomial.uniqueAlgEquiv F (Fin 1)).injective]
  exact MvPolynomial.natDegree_finSuccEquiv R

/-- Evaluate the remaining coordinates at `(Y₀, X) = (P, X)`. -/
def remainingSpecializationHom (P : F[X]) : MvPolynomial (Fin 2) F →+* F[X] :=
  eval₂Hom Polynomial.C (Fin.cases P fun _ ↦ Polynomial.X)

/-- Specialize the remaining-coordinate polynomial at its outer variable. -/
theorem remainingSpecializationHom_eq_eval (P : F[X]) (R : MvPolynomial (Fin 2) F) :
    (remainingPolynomialEquiv R).eval P = remainingSpecializationHom P R := by
  let lhs : MvPolynomial (Fin 2) F →+* F[X] :=
    (Polynomial.evalRingHom P).comp
      ((Polynomial.mapRingHom
        (MvPolynomial.uniqueAlgEquiv F (Fin 1)).toRingHom).comp
          (MvPolynomial.finSuccEquiv F 1).toRingHom)
  let rhs : MvPolynomial (Fin 2) F →+* F[X] := remainingSpecializationHom P
  change lhs R = rhs R
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs, remainingSpecializationHom, MvPolynomial.finSuccEquiv_apply]
  · intro i
    fin_cases i
    · dsimp [lhs, rhs, remainingSpecializationHom]
      rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.eval_X,
        MvPolynomial.eval₂_X]
      congr
    · dsimp [lhs, rhs, remainingSpecializationHom]
      rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide,
        MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, Polynomial.eval_C]
      simp [MvPolynomial.X]
      congr

/-- Evaluate a root-coordinate polynomial by substituting the first Hasse derivative for `Y₁`.
-/
def rootFirstSpecializationHom (P : F[X]) :
    MvPolynomial (Option (Fin 2)) F →+* F[X] :=
  eval₂Hom Polynomial.C fun v ↦
    match firstOrderRootEquiv.symm v with
    | none => Polynomial.X
    | some j => P.hasseDeriv j

/-- Root-coordinate evaluation agrees with differential specialization. -/
theorem rootFirstSpecializationHom_firstOrderRootCoordinates
    (Q : DifferentialPolynomial F 1) (P : F[X]) :
    rootFirstSpecializationHom P (firstOrderRootCoordinates Q) =
      differentialSpecialization Q P := by
  rw [rootFirstSpecializationHom, firstOrderRootCoordinates, renameEquiv_apply,
    eval₂Hom_rename]
  apply eval₂Hom_congr
  · rfl
  · funext v
    rcases v with _ | j
    · rfl
    · simp only [Function.comp_apply, Equiv.symm_apply_apply]
  · rfl

/-- Root-coordinate evaluation agrees with specialization after recovering the equation. -/
theorem rootFirstSpecializationHom_fromFirstOrderRootCoordinates
    (R : MvPolynomial (Option (Fin 2)) F) (P : F[X]) :
    rootFirstSpecializationHom P R =
      differentialSpecialization (fromFirstOrderRootCoordinates R) P := by
  calc
    rootFirstSpecializationHom P R = rootFirstSpecializationHom P
        (firstOrderRootCoordinates (fromFirstOrderRootCoordinates R)) := by simp
    _ = differentialSpecialization (fromFirstOrderRootCoordinates R) P :=
      rootFirstSpecializationHom_firstOrderRootCoordinates _ _

/-- Root-coordinate evaluation is evaluation of the corresponding ordinary-root polynomial. -/
theorem rootFirstSpecializationHom_eq_eval_rootPolynomial
    (R : MvPolynomial (Option (Fin 2)) F) (P : F[X]) :
    rootFirstSpecializationHom P R =
      ((optionEquivLeft F (Fin 2) R).map (remainingSpecializationHom P)).eval
        (P.hasseDeriv 1) := by
  let lhs : MvPolynomial (Option (Fin 2)) F →+* F[X] := rootFirstSpecializationHom P
  let rhs : MvPolynomial (Option (Fin 2)) F →+* F[X] :=
    (Polynomial.evalRingHom (P.hasseDeriv 1)).comp
      ((Polynomial.mapRingHom (remainingSpecializationHom P)).comp
        (optionEquivLeft F (Fin 2)).toRingHom)
  change lhs R = rhs R
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs, rootFirstSpecializationHom, remainingSpecializationHom]
  · intro v
    rcases v with _ | j
    · simp [lhs, rhs, rootFirstSpecializationHom, firstOrderRootEquiv]
    · fin_cases j
      · have hj : firstOrderRootEquiv.symm (some (0 : Fin 2)) = some 0 := by decide
        simp [lhs, rhs, rootFirstSpecializationHom, remainingSpecializationHom, hj]
      · have hj : firstOrderRootEquiv.symm (some (1 : Fin 2)) = none := by decide
        simp [lhs, rhs, rootFirstSpecializationHom, remainingSpecializationHom, hj]
        congr

/-- The radical content coefficient after extracting the constant root-variable coefficient. -/
def contentCoefficient (Q : DifferentialPolynomial F 1) : MvPolynomial (Fin 2) F :=
  (optionEquivLeft F (Fin 2)
    (radicalContent none (firstOrderRootCoordinates Q))).coeff 0

/-- The radical content as a polynomial in `Y₀` over `F[X]`. -/
def contentAsPolynomial (Q : DifferentialPolynomial F 1) : F[X][X] :=
  remainingPolynomialEquiv (contentCoefficient Q)

/-- The positive-jet factor as a polynomial in `Y₁` over `F[X][X]`. -/
def positiveAsPolynomial (Q : DifferentialPolynomial F 1) : F[X][X][X] :=
  (ordinaryRootPolynomial (firstOrderRootCoordinates Q)).map
    remainingPolynomialEquiv.toRingHom

/-- The nonzero radical content has a nonzero constant coefficient in the root variable. -/
theorem contentCoefficient_ne_zero (Q : DifferentialPolynomial F 1) :
    contentCoefficient Q ≠ 0 := by
  let U := optionEquivLeft F (Fin 2) (radicalContent none (firstOrderRootCoordinates Q))
  have hU : U ≠ 0 :=
    (optionEquivLeft F (Fin 2)).injective.ne_iff.mpr
      (radicalContent_ne_zero none (firstOrderRootCoordinates Q))
  have hdeg : U.natDegree = 0 := by
    dsimp only [U]
    rw [natDegree_optionEquivLeft, degreeOf_radicalContent]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hU
  simpa [U, contentCoefficient] using hU

/-- Specializing the content coefficient gives the specialization of the radical content. -/
theorem remainingSpecializationHom_contentCoefficient
    (Q : DifferentialPolynomial F 1) (P : F[X]) :
    remainingSpecializationHom P (contentCoefficient Q) =
      rootFirstSpecializationHom P
        (radicalContent none (firstOrderRootCoordinates Q)) := by
  let U := optionEquivLeft F (Fin 2)
    (radicalContent none (firstOrderRootCoordinates Q))
  have hdeg :
      (optionEquivLeft F (Fin 2)
        (radicalContent none (firstOrderRootCoordinates Q))).natDegree = 0 := by
    rw [natDegree_optionEquivLeft, degreeOf_radicalContent]
  have hU : U = Polynomial.C (contentCoefficient Q) := by
    exact Polynomial.eq_C_of_natDegree_eq_zero (by simpa only [U] using hdeg)
  rw [rootFirstSpecializationHom_eq_eval_rootPolynomial]
  change remainingSpecializationHom P (contentCoefficient Q) =
    (U.map (remainingSpecializationHom P)).eval (P.hasseDeriv 1)
  rw [hU, Polynomial.map_C, Polynomial.eval_C]

/-- The constructed singular polynomial in the remaining `(Y₀, X)` coordinates. -/
def singularPolynomial (Q : DifferentialPolynomial F 1) : MvPolynomial (Fin 2) F :=
  contentCoefficient Q *
    resultant (ordinaryRootPolynomial (firstOrderRootCoordinates Q))
      (ordinaryRootPolynomial (firstOrderRootCoordinates Q)).derivative
      (degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q)))
      (degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q)) - 1)

/-- Regard the singular polynomial as a polynomial in `Y₀` over `F[X]`. -/
def singularAsPolynomial (Q : DifferentialPolynomial F 1) : F[X][X] :=
  remainingPolynomialEquiv (singularPolynomial Q)

/-- Each `Y₁` coefficient satisfies the exact `Y₀`/`Y₁` weighted-degree triangle. -/
theorem degreeOf_coeff_optionEquivLeft_add_le_rootJetWeight
    (V : MvPolynomial (Option (Fin 2)) F) (i b : ℕ) (hi : i ≤ b)
    (hdegree : degreeOf none V = b) :
    degreeOf (0 : Fin 2) ((optionEquivLeft F (Fin 2) V).coeff i) + i ≤
      V.weightedTotalDegree rootJetWeight := by
  classical
  have hiweight : i ≤ V.weightedTotalDegree rootJetWeight := by
    calc
      i ≤ b := hi
      _ = degreeOf none V := hdegree.symm
      _ ≤ V.weightedTotalDegree rootJetWeight := by
        apply degreeOf_le_iff.mpr
        intro u hu
        have h := le_weightedTotalDegree rootJetWeight hu
        have hnone : u none ≤ u.weight rootJetWeight := by
          rw [Finsupp.weight_eq_sum]
          simp [rootJetWeight]
        exact hnone.trans h
  have hdeg : degreeOf (0 : Fin 2) ((optionEquivLeft F (Fin 2) V).coeff i) ≤
      V.weightedTotalDegree rootJetWeight - i := by
    apply degreeOf_le_iff.mpr
    intro u hu
    have hexp : u.embDomain .some + Finsupp.single none i = u.optionElim i := by
      ext (_ | j) <;> simp
    have hsource : u.embDomain .some + Finsupp.single none i ∈ V.support := by
      rw [hexp]
      exact (MvPolynomial.mem_support_coeff_optionEquivLeft F).mp hu
    have hle := le_weightedTotalDegree rootJetWeight hsource
    have hemb : Finsupp.weight rootJetWeight (u.embDomain .some) = u 0 := by
      have hw : (fun j : Fin 2 ↦ rootJetWeight (Function.Embedding.some j)) =
          Pi.single 0 1 := by
        funext j
        fin_cases j <;> simp [rootJetWeight]
      rw [Finsupp.weight_apply]
      rw [Finsupp.sum_embDomain, ← Finsupp.weight_apply, hw,
        Finsupp.weight_single_one_apply]
    have hsingle : u 0 + i =
        (u.embDomain .some + Finsupp.single none i).weight rootJetWeight := by
      rw [map_add, hemb, Finsupp.weight_single]
      simp [rootJetWeight]
    omega
  omega

/-- The positive-root polynomial has the actual `Y₁` degree of the positive-jet factor. -/
theorem positiveAsPolynomial_natDegree (Q : DifferentialPolynomial F 1) :
    (positiveAsPolynomial Q).natDegree =
      degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q)) := by
  unfold positiveAsPolynomial
  rw [Polynomial.natDegree_map_eq_of_injective remainingPolynomialEquiv.injective,
    natDegree_ordinaryRootPolynomial]

/-- Every positive-root coefficient fits the jet-degree triangle. -/
theorem positiveAsPolynomial_coeff_triangle (Q : DifferentialPolynomial F 1)
    (i : ℕ) (hi : i ≤ degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q))) :
    i + ((positiveAsPolynomial Q).coeff i).natDegree ≤
      jetTotalDegree (positiveJetFactor Q) := by
  rw [positiveAsPolynomial, Polynomial.coeff_map, add_comm]
  change (remainingPolynomialEquiv
    ((ordinaryRootPolynomial (firstOrderRootCoordinates Q)).coeff i)).natDegree + i ≤ _
  rw [remainingPolynomialEquiv_natDegree]
  change degreeOf (0 : Fin 2)
      ((optionEquivLeft F (Fin 2)
        (radicalPrimPart none (firstOrderRootCoordinates Q))).coeff i) + i ≤ _
  calc
    _ ≤ (radicalPrimPart none (firstOrderRootCoordinates Q)).weightedTotalDegree
        rootJetWeight := degreeOf_coeff_optionEquivLeft_add_le_rootJetWeight
          (radicalPrimPart none (firstOrderRootCoordinates Q)) i
          (degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q))) hi rfl
    _ = jetTotalDegree (positiveJetFactor Q) := by
      simpa only [positiveJetFactor, firstOrderRootCoordinates_fromFirstOrderRootCoordinates]
        using fromFirstOrderRootCoordinates_weightedTotalDegree
          (radicalPrimPart none (firstOrderRootCoordinates Q))

/-- The separated derivative of the positive-jet factor is the root-variable derivative in root
coordinates. -/
theorem firstOrderRootCoordinates_separant_positiveJetFactor
    (Q : DifferentialPolynomial F 1) :
    firstOrderRootCoordinates (separant (positiveJetFactor Q) (1 : Fin 2)) =
      pderiv none (radicalPrimPart none (firstOrderRootCoordinates Q)) := by
  rw [firstOrderRootCoordinates, separant, positiveJetFactor,
    fromFirstOrderRootCoordinates, renameEquiv_apply]
  have h := pderiv_rename firstOrderRootEquiv.symm.injective none
    (radicalPrimPart none (firstOrderRootCoordinates Q))
  have h' : pderiv (some 1)
      (renameEquiv F firstOrderRootEquiv.symm
        (radicalPrimPart none (firstOrderRootCoordinates Q))) =
      renameEquiv F firstOrderRootEquiv.symm
        (pderiv none (radicalPrimPart none (firstOrderRootCoordinates Q))) := by
    simpa [firstOrderRootEquiv, renameEquiv_apply] using h
  change renameEquiv F firstOrderRootEquiv
      (pderiv (some 1)
        (renameEquiv F firstOrderRootEquiv.symm
          (radicalPrimPart none (firstOrderRootCoordinates Q)))) = _
  rw [h']
  exact (renameEquiv F firstOrderRootEquiv).apply_symm_apply _

/-- Specializing the positive-jet factor evaluates its ordinary-root polynomial at `P'`. -/
theorem positiveJetFactor_specialization_eq
    (Q : DifferentialPolynomial F 1) (P : F[X]) :
    differentialSpecialization (positiveJetFactor Q) P =
      ((ordinaryRootPolynomial (firstOrderRootCoordinates Q)).map
        (remainingSpecializationHom P)).eval (P.hasseDeriv 1) := by
  calc
    differentialSpecialization (positiveJetFactor Q) P =
        rootFirstSpecializationHom P
          (firstOrderRootCoordinates (positiveJetFactor Q)) :=
      (rootFirstSpecializationHom_firstOrderRootCoordinates _ _).symm
    _ = rootFirstSpecializationHom P
        (radicalPrimPart none (firstOrderRootCoordinates Q)) := by
      rw [firstOrderRootCoordinates_positiveJetFactor]
    _ = _ := rootFirstSpecializationHom_eq_eval_rootPolynomial _ _

/-- Specializing the separant of the positive-jet factor evaluates the derivative of its
ordinary-root polynomial at `P'`. -/
theorem positiveJetFactor_separant_specialization_eq
    (Q : DifferentialPolynomial F 1) (P : F[X]) :
    differentialSpecialization (separant (positiveJetFactor Q) (1 : Fin 2)) P =
      ((ordinaryRootPolynomial (firstOrderRootCoordinates Q)).map
        (remainingSpecializationHom P)).derivative.eval (P.hasseDeriv 1) := by
  rw [← rootFirstSpecializationHom_firstOrderRootCoordinates,
    firstOrderRootCoordinates_separant_positiveJetFactor,
    rootFirstSpecializationHom_eq_eval_rootPolynomial]
  rw [optionEquivLeft_pderiv_none, Polynomial.derivative_map]
  rfl

/-- The singular polynomial becomes the generic singular tail in the `Y₀` view. -/
theorem singularAsPolynomial_eq_singularTail (Q : DifferentialPolynomial F 1) :
    singularAsPolynomial Q = singularTail (contentAsPolynomial Q)
      (positiveAsPolynomial Q)
      (degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q))) := by
  unfold singularAsPolynomial singularPolynomial singularTail contentAsPolynomial
    positiveAsPolynomial
  rw [map_mul]
  congr 1
  change remainingPolynomialEquiv.toRingHom
      (resultant (ordinaryRootPolynomial (firstOrderRootCoordinates Q))
        (ordinaryRootPolynomial (firstOrderRootCoordinates Q)).derivative _ _) = _
  rw [← Polynomial.resultant_map_map]
  congr 2
  exact (Polynomial.derivative_map _ remainingPolynomialEquiv.toRingHom).symm

/-- The content coefficient polynomial has degree at most the jet degree of the content factor.
-/
theorem contentAsPolynomial_natDegree_le (Q : DifferentialPolynomial F 1) :
    (contentAsPolynomial Q).natDegree ≤
      jetTotalDegree
        (fromFirstOrderRootCoordinates
          (radicalContent none (firstOrderRootCoordinates Q))) := by
  rw [contentAsPolynomial, remainingPolynomialEquiv_natDegree, contentCoefficient]
  change degreeOf (0 : Fin 2)
      ((optionEquivLeft F (Fin 2)
        (radicalContent none (firstOrderRootCoordinates Q))).coeff 0) ≤ _
  have hcoeff := degreeOf_coeff_optionEquivLeft_add_le_rootJetWeight
    (radicalContent none (firstOrderRootCoordinates Q)) 0 0 le_rfl
    (degreeOf_radicalContent _ _)
  calc
    _ ≤ (radicalContent none (firstOrderRootCoordinates Q)).weightedTotalDegree
          rootJetWeight := by simpa using hcoeff
    _ = jetTotalDegree
          (fromFirstOrderRootCoordinates
            (radicalContent none (firstOrderRootCoordinates Q))) :=
      fromFirstOrderRootCoordinates_weightedTotalDegree
        (radicalContent none (firstOrderRootCoordinates Q))

/-- The constructed order-zero singular equation. -/
def singularEquation (Q : DifferentialPolynomial F 1) : DifferentialPolynomial F 0 :=
  orderZeroOfPolynomial (singularAsPolynomial Q)

/-- A root of the input outside the regular positive-factor locus makes the singular equation
vanish after specialization. -/
theorem singularEquation_routes_nonregular
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) (P : F[X])
    (hroot : differentialSpecialization Q P = 0)
    (hnonregular : differentialSpecialization (positiveJetFactor Q) P ≠ 0 ∨
      differentialSpecialization
        (separant (positiveJetFactor Q) (1 : Fin 2)) P = 0) :
    differentialSpecialization (singularEquation Q) P = 0 := by
  have hsplit := (map_radicalContent_mul_radicalPrimPart_eq_zero_iff
    (rootFirstSpecializationHom P) none (by
      exact fun h ↦ hQ ((renameEquiv F firstOrderRootEquiv).injective h))).mpr (by
        calc
          rootFirstSpecializationHom P (firstOrderRootCoordinates Q) =
              differentialSpecialization Q P :=
            rootFirstSpecializationHom_firstOrderRootCoordinates Q P
          _ = 0 := hroot)
  rw [map_mul, mul_eq_zero] at hsplit
  change rootFirstSpecializationHom P
      (radicalContent none (firstOrderRootCoordinates Q)) = 0 ∨
    rootFirstSpecializationHom P
      (radicalPrimPart none (firstOrderRootCoordinates Q)) = 0 at hsplit
  rw [← orderZeroAsPolynomial_eval, singularEquation,
    orderZeroAsPolynomial_orderZeroOfPolynomial]
  change (remainingPolynomialEquiv (singularPolynomial Q)).eval P = 0
  rw [remainingSpecializationHom_eq_eval P (singularPolynomial Q)]
  rcases hsplit with hcontent | hpositive
  · rw [singularPolynomial, map_mul, remainingSpecializationHom_contentCoefficient,
      hcontent, zero_mul]
  · have hpositive' : differentialSpecialization (positiveJetFactor Q) P = 0 := by
      change differentialSpecialization
        (fromFirstOrderRootCoordinates
          (radicalPrimPart none (firstOrderRootCoordinates Q))) P = 0
      rw [← rootFirstSpecializationHom_fromFirstOrderRootCoordinates]
      exact hpositive
    rcases hnonregular with hnot | hseparant
    · exact (hnot hpositive').elim
    · let r := degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q))
      by_cases hrzero : r = 0
      · have hone := radicalPrimPart_eq_one_of_degreeOf_eq_zero none
          (firstOrderRootCoordinates Q) hrzero
        have hrootOne : differentialSpecialization (positiveJetFactor Q) P = 1 := by
          simp [positiveJetFactor, hone, fromFirstOrderRootCoordinates,
            differentialSpecialization, differentialSpecializationHom]
        rw [hrootOne] at hpositive'
        exact (one_ne_zero hpositive').elim
      · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
        have hdegree : (positiveAsPolynomial Q).natDegree ≤ r := by
          rw [positiveAsPolynomial_natDegree]
        have hhom :
            (Polynomial.evalRingHom P).comp remainingPolynomialEquiv.toRingHom =
              remainingSpecializationHom P := by
          apply RingHom.ext
          intro R
          exact remainingSpecializationHom_eq_eval P R
        have hmap :
            (positiveAsPolynomial Q).map (Polynomial.evalRingHom P) =
              (ordinaryRootPolynomial (firstOrderRootCoordinates Q)).map
                (remainingSpecializationHom P) := by
          unfold positiveAsPolynomial
          rw [Polynomial.map_map, hhom]
        have hrootA :
            ((positiveAsPolynomial Q).map (Polynomial.evalRingHom P)).eval
                (P.hasseDeriv 1) = 0 := by
          rw [hmap]
          rw [positiveJetFactor_specialization_eq] at hpositive'
          exact hpositive'
        have hderivativeA :
            (((positiveAsPolynomial Q).map (Polynomial.evalRingHom P)).derivative).eval
                (P.hasseDeriv 1) = 0 := by
          rw [hmap]
          rw [positiveJetFactor_separant_specialization_eq] at hseparant
          exact hseparant
        have htail := singularTail_map_eq_zero_of_common_root
          (contentAsPolynomial Q) (positiveAsPolynomial Q) hr hdegree
          (Polynomial.evalRingHom P) (P.hasseDeriv 1) hrootA hderivativeA
        change (singularTail (contentAsPolynomial Q) (positiveAsPolynomial Q) r).eval P = 0
          at htail
        rw [← singularAsPolynomial_eq_singularTail] at htail
        change (remainingPolynomialEquiv (singularPolynomial Q)).eval P = 0 at htail
        rw [remainingSpecializationHom_eq_eval P (singularPolynomial Q)] at htail
        exact htail

/-- The content-resultant polynomial has degree at most the ordinary-degree envelope. -/
theorem singularEquation_degree_le (Q : DifferentialPolynomial F 1)
    {B M : ℕ} (hjet : jetTotalDegree Q ≤ B)
    (hderiv : jetDegree Q 1 ≤ M) (hMB : M ≤ B) :
    jetTotalDegree (singularEquation Q) ≤ ordinaryDegreeEnvelope B M := by
  rw [singularEquation, orderZeroOfPolynomial_jetTotalDegree]
  let r := degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q))
  have hrj : r ≤ jetTotalDegree (positiveJetFactor Q) := by
    calc
      r = jetDegree (positiveJetFactor Q) 1 := by
        simpa only [firstOrderRootCoordinates_positiveJetFactor] using
          firstOrderRootCoordinates_rootDegree (positiveJetFactor Q)
      _ ≤ jetTotalDegree (positiveJetFactor Q) := jetDegree_le_total _ 1
  have hrM : r ≤ M := by
    calc
      r = jetDegree (positiveJetFactor Q) 1 := by
        simpa only [firstOrderRootCoordinates_positiveJetFactor] using
          firstOrderRootCoordinates_rootDegree (positiveJetFactor Q)
      _ ≤ jetDegree Q 1 := positiveJetFactor_yOneDegree_le Q
      _ ≤ M := hderiv
  have hcontentDegree : (contentAsPolynomial Q).natDegree ≤
      (radicalContent none (firstOrderRootCoordinates Q)).weightedTotalDegree rootJetWeight := by
    calc
      _ ≤ jetTotalDegree (fromFirstOrderRootCoordinates
            (radicalContent none (firstOrderRootCoordinates Q))) :=
        contentAsPolynomial_natDegree_le Q
      _ = _ := (fromFirstOrderRootCoordinates_weightedTotalDegree _).symm
  have hsplit := map_radicalContent_add_map_radicalPrimPart_le
    (d := fun R ↦ R.weightedTotalDegree rootJetWeight)
    (fun p q hp hq ↦ weightedTotalDegree_mul rootJetWeight p q hp hq)
    none (firstOrderRootCoordinates Q)
  have hbudget : (contentAsPolynomial Q).natDegree +
      jetTotalDegree (positiveJetFactor Q) ≤ B := by
    calc
      _ ≤ (radicalContent none (firstOrderRootCoordinates Q)).weightedTotalDegree
            rootJetWeight +
          (radicalPrimPart none (firstOrderRootCoordinates Q)).weightedTotalDegree
            rootJetWeight := by
        apply Nat.add_le_add hcontentDegree
        simpa only [positiveJetFactor, firstOrderRootCoordinates_fromFirstOrderRootCoordinates]
          using (fromFirstOrderRootCoordinates_weightedTotalDegree
            (radicalPrimPart none (firstOrderRootCoordinates Q))).symm.le
      _ ≤ (firstOrderRootCoordinates Q).weightedTotalDegree rootJetWeight := hsplit
      _ = jetTotalDegree Q := firstOrderRootCoordinates_weightedTotalDegree Q
      _ ≤ B := hjet
  have htail := natDegree_singularTail_le (contentAsPolynomial Q)
    (positiveAsPolynomial Q) hrM hMB le_rfl hbudget
    (positiveAsPolynomial_coeff_triangle Q)
  simpa [singularAsPolynomial_eq_singularTail, r, singularEquation] using htail

/-- The singular equation is nonzero when the derivative resultant is protected by the
characteristic bound. -/
theorem singularEquation_ne_zero (Q : DifferentialPolynomial F 1)
    {M : ℕ} (hdegree : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ M < ringChar F) : singularEquation Q ≠ 0 := by
  let A := ordinaryRootPolynomial (firstOrderRootCoordinates Q)
  let r := degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q))
  have hrootChar : ringChar F = 0 ∨
      degreeOf none (firstOrderRootCoordinates Q) < ringChar F := by
    rcases hchar with hzero | hpositive
    · exact Or.inl hzero
    · exact Or.inr ((firstOrderRootCoordinates_rootDegree Q).trans_le hdegree |>.trans_lt
        hpositive)
  have hresultant := resultant_derivative_ne_zero_ordinaryRootPolynomial
    (firstOrderRootCoordinates Q) hrootChar
  have hres : resultant A A.derivative r (r - 1) ≠ 0 := by
    have hr : A.natDegree = r := by
      dsimp [A]
      exact natDegree_ordinaryRootPolynomial _
    have hres' : resultant A A.derivative A.natDegree (A.natDegree - 1) ≠ 0 := by
      simpa only [A] using hresultant
    simpa only [hr] using hres'
  have hproduct : singularPolynomial Q ≠ 0 := by
    rw [singularPolynomial]
    exact mul_ne_zero (contentCoefficient_ne_zero Q) hres
  intro hzero
  apply hproduct
  have heq : singularAsPolynomial Q = 0 := by
    rw [← orderZeroAsPolynomial_orderZeroOfPolynomial (singularAsPolynomial Q)]
    rw [show orderZeroOfPolynomial (singularAsPolynomial Q) = singularEquation Q by rfl,
      hzero]
    simp [orderZeroAsPolynomial]
  exact remainingPolynomialEquiv.injective (by
    simpa [singularAsPolynomial] using heq)

/-- Construct tail data from degree bounds on the input equation. -/
def fixedWordSingularTailOfBounds (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (B M : ℕ) (hjet : jetTotalDegree Q ≤ B) (hderiv : jetDegree Q 1 ≤ M)
    (hMB : M ≤ B) (hchar : ringChar F = 0 ∨ M < ringChar F) :
  FixedWordRegularTail Q (positiveJetFactor Q) B M where
  regular_degree_zero := by
    intro hdegree
    have hrootDegree :
        degreeOf none (radicalPrimPart none (firstOrderRootCoordinates Q)) = 0 := by
      rw [← firstOrderRootCoordinates_positiveJetFactor]
      exact (firstOrderRootCoordinates_rootDegree (positiveJetFactor Q)).trans hdegree
    unfold positiveJetFactor fromFirstOrderRootCoordinates
    rw [radicalPrimPart_eq_one_of_degreeOf_eq_zero none _ hrootDegree]
    simp
  equation := singularEquation Q
  nonzero := singularEquation_ne_zero Q hderiv hchar
  degree_le := singularEquation_degree_le Q hjet hderiv hMB
  routes_nonregular := singularEquation_routes_nonregular Q hQ

open Classical in
/-- The fixed-word squarefree agreement list bound from an automatically constructed singular
tail. -/
theorem finite_squarefree_agreement_solutions_card_le
    {n D A B M : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hkA : D + 1 ≤ A) (hAn : A ≤ n)
    (hMB : M ≤ B)
    (hjet : jetTotalDegree Q ≤ B) (hderiv : jetDegree Q 1 ≤ M)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, P.degree < D + 1 ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) *
          ((n - D : ℕ) : ℝ) / (A - D : ℕ) + ordinaryDegreeEnvelope B M := by
  have htailChar : ringChar F = 0 ∨ M < ringChar F := by
    rcases hchar with hzero | hpositive
    · exact Or.inl hzero
    · exact Or.inr ((Nat.le_max_right D M).trans_lt hpositive)
  exact finite_factorwise_agreement_solutions_card_le_of_regular_equation
    domain received Q (positiveJetFactor Q) hD hkA hAn hMB
    (positiveJetFactor_jetTotalDegree_le Q |>.trans hjet)
    (positiveJetFactor_yOneDegree_le Q |>.trans hderiv) hchar
    (fixedWordSingularTailOfBounds Q hQ B M hjet hderiv hMB htailChar)
    S hsol haccept

end

end ReedSolomon.FirstOrder.Squarefree
