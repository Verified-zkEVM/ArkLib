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
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree

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

@[simp]
theorem fromRootFirst_mul (R S : MvPolynomial (Option (Fin 2)) F) :
    fromRootFirst (R * S) = fromRootFirst R * fromRootFirst S := by
  simp [fromRootFirst]

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

/-- The transported squarefree positive-`Y₁` product divides the original equation. -/
theorem positiveEquation_dvd (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    positiveEquation Q ∣ Q := by
  have hroot : positiveRootProduct Q ∣ rootFirst Q := by
    change ordinaryRootProduct (rootFirst Q) ∣ rootFirst Q
    apply dvd_trans (show positiveRootProduct Q ∣ content Q * positiveRootProduct Q from
      ⟨content Q, by ac_rfl⟩)
    change ordinaryContent (rootFirst Q) * ordinaryRootProduct (rootFirst Q) ∣ rootFirst Q
    rw [ordinary_split_product]
    exact ordinarySquarefreeProduct_dvd (rootFirst Q) (rootFirst_ne_zero_iff Q |>.mpr hQ)
  obtain ⟨R, hR⟩ := hroot
  refine ⟨fromRootFirst R, ?_⟩
  have hmapped := congrArg fromRootFirst hR
  simpa only [positiveEquation, fromRootFirst_rootFirst, fromRootFirst_mul] using hmapped

/-- The retained content times the transported positive product divides the original equation. -/
theorem contentEquation_mul_positiveEquation_dvd
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    contentEquation Q * positiveEquation Q ∣ Q := by
  have hsquare := ordinarySquarefreeProduct_dvd
    (rootFirst Q) (rootFirst_ne_zero_iff Q |>.mpr hQ)
  obtain ⟨R, hR⟩ := hsquare
  refine ⟨fromRootFirst R, ?_⟩
  calc
    Q = fromRootFirst (rootFirst Q) := (fromRootFirst_rootFirst Q).symm
    _ = fromRootFirst (ordinarySquarefreeProduct (rootFirst Q) * R) :=
      congrArg fromRootFirst hR
    _ = contentEquation Q * positiveEquation Q * fromRootFirst R := by
      rw [← ordinary_split_product, fromRootFirst_mul, fromRootFirst_mul]
      rfl

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

/-- Retained content and the distinct positive factors share the original total jet-degree
budget.  The independent variable has weight zero, so its potentially large degree does not
weaken this bound. -/
theorem contentEquation_jetTotalDegree_add_positiveEquation_le
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    jetTotalDegree (contentEquation Q) + jetTotalDegree (positiveEquation Q) ≤
      jetTotalDegree Q := by
  have hcontent := contentEquation_ne_zero Q
  have hpositive := positiveEquation_ne_zero Q
  have hproduct : contentEquation Q * positiveEquation Q ≠ 0 := mul_ne_zero hcontent hpositive
  have hle := weightedTotalDegree_option_zero_one_le_of_dvd
    (contentEquation Q * positiveEquation Q) Q hproduct hQ
      (contentEquation_mul_positiveEquation_dvd Q hQ)
  rw [weightedTotalDegree_option_zero_one_mul
    (contentEquation Q) (positiveEquation Q) hcontent hpositive] at hle
  simpa only [jetTotalDegree_eq_weightedTotalDegree_elim] using hle

/-- The squarefree positive factor product alone stays within the source total jet-degree
budget. -/
theorem positiveEquation_jetTotalDegree_le
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    jetTotalDegree (positiveEquation Q) ≤ jetTotalDegree Q :=
  (Nat.le_add_left _ _).trans
    (contentEquation_jetTotalDegree_add_positiveEquation_le Q hQ)

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
