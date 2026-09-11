/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.PositiveProduct
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Factorization
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FirstOrder.FirstOrderList

/-!
# Semantic presentations of the squarefree first-order split

This file transports the retained content and the distinct positive-`Y₁` product back from
root-first factorization coordinates to ordinary differential-polynomial coordinates.  The
transport preserves differential specialization exactly, so the algebraic factorization can be
used by the existing regular-solution counting theorems.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F]

/-- Undo the root-first coordinate change. -/
def fromRootFirst (R : MvPolynomial (Option (Fin 2)) F) :
    DifferentialPolynomial F 1 :=
  renameEquiv F (rootFirstEquiv.symm) R

/-- The retained `Y₁`-independent factor as a first-order equation. -/
def contentEquation (Q : DifferentialPolynomial F 1) : DifferentialPolynomial F 1 :=
  fromRootFirst (content Q)

/-- The distinct positive-`Y₁` factor product as a first-order equation. -/
def positiveEquation (Q : DifferentialPolynomial F 1) : DifferentialPolynomial F 1 :=
  fromRootFirst (positiveRootProduct Q)

@[simp]
theorem rootFirst_fromRootFirst (R : MvPolynomial (Option (Fin 2)) F) :
    rootFirst (fromRootFirst R) = R := by
  simp [rootFirst, fromRootFirst]

@[simp]
theorem fromRootFirst_rootFirst (Q : DifferentialPolynomial F 1) :
    fromRootFirst (rootFirst Q) = Q := by
  simp [rootFirst, fromRootFirst]

theorem contentEquation_ne_zero (Q : DifferentialPolynomial F 1) :
    contentEquation Q ≠ 0 := by
  intro hzero
  apply content_ne_zero Q
  have := congrArg rootFirst hzero
  rw [contentEquation, rootFirst_fromRootFirst] at this
  simpa [rootFirst] using this

theorem positiveEquation_ne_zero (Q : DifferentialPolynomial F 1) :
    positiveEquation Q ≠ 0 := by
  intro hzero
  apply positiveRootProduct_ne_zero Q
  have := congrArg rootFirst hzero
  rw [positiveEquation, rootFirst_fromRootFirst] at this
  simpa [rootFirst] using this

theorem contentEquation_yOneDegree (Q : DifferentialPolynomial F 1) :
    jetDegree (contentEquation Q) (1 : Fin 2) = 0 := by
  change degreeOf (some (1 : Fin 2)) (contentEquation Q) = 0
  calc
    _ = degreeOf none (rootFirst (contentEquation Q)) := (rootDegree_rootFirst _).symm
    _ = degreeOf none (content Q) := by rw [contentEquation, rootFirst_fromRootFirst]
    _ = 0 := content_rootDegree Q

theorem positiveEquation_totalDegree_le
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    (positiveEquation Q).totalDegree ≤ Q.totalDegree := by
  calc
    _ = (rootFirst (positiveEquation Q)).totalDegree := (totalDegree_rootFirst _).symm
    _ = (positiveRootProduct Q).totalDegree := by rw [positiveEquation, rootFirst_fromRootFirst]
    _ ≤ Q.totalDegree := positiveRootProduct_totalDegree_le Q hQ

theorem positiveEquation_yOneDegree_le
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    jetDegree (positiveEquation Q) (1 : Fin 2) ≤ jetDegree Q (1 : Fin 2) := by
  change degreeOf (some (1 : Fin 2)) (positiveEquation Q) ≤
    degreeOf (some (1 : Fin 2)) Q
  calc
    _ = degreeOf none (rootFirst (positiveEquation Q)) := (rootDegree_rootFirst _).symm
    _ = degreeOf none (positiveRootProduct Q) := by rw [positiveEquation, rootFirst_fromRootFirst]
    _ = ∑ a ∈ ordinaryRootFactorClasses (rootFirst Q),
          degreeOf none (ordinaryFactorRepresentative a) := by
      rw [positiveRootProduct, ordinaryRootProduct, degreeOf_prod_eq]
      intro a ha
      exact (ordinaryRootFactorClasses_spec (rootFirst Q) ha).1.ne_zero
    _ ≤ degreeOf (some (1 : Fin 2)) Q := factorRootDegrees_le Q hQ

/-- Differential specialization in root-first coordinates. -/
def rootFirstSpecializationHom (P : F[X]) :
    MvPolynomial (Option (Fin 2)) F →+* F[X] :=
  eval₂Hom Polynomial.C fun v ↦
    match rootFirstEquiv.symm v with
    | none => Polynomial.X
    | some j => P.hasseDeriv j

theorem rootFirstSpecializationHom_rootFirst (Q : DifferentialPolynomial F 1) (P : F[X]) :
    rootFirstSpecializationHom P (rootFirst Q) = differentialSpecialization Q P := by
  rw [rootFirstSpecializationHom, rootFirst, differentialSpecialization,
    renameEquiv_apply, eval₂Hom_rename]
  apply eval₂Hom_congr
  · rfl
  · funext v
    rcases v with _ | j
    · rfl
    · simp only [Function.comp_apply, Equiv.symm_apply_apply]
  · rfl

theorem rootFirstSpecializationHom_fromRootFirst
    (R : MvPolynomial (Option (Fin 2)) F) (P : F[X]) :
    rootFirstSpecializationHom P R = differentialSpecialization (fromRootFirst R) P := by
  rw [← rootFirstSpecializationHom_rootFirst]
  simp

/-- Every root of the source equation is a root of the retained content or of the distinct
positive-`Y₁` product. -/
theorem root_content_or_positive
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) (P : F[X])
    (hroot : differentialSpecialization Q P = 0) :
    differentialSpecialization (contentEquation Q) P = 0 ∨
      differentialSpecialization (positiveEquation Q) P = 0 := by
  have hsplit := (split_zero_iff Q hQ (rootFirstSpecializationHom P)).mpr
    (by simpa only [rootFirstSpecializationHom_rootFirst] using hroot)
  rw [map_mul, mul_eq_zero] at hsplit
  simpa only [rootFirstSpecializationHom_fromRootFirst, contentEquation,
    positiveEquation] using hsplit

end

end ReedSolomon.FirstOrder.Squarefree
