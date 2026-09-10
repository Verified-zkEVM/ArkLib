/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToCompPoly.Multivariate.Eval
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Base change for concrete multivariate systems

Evaluation of a concrete polynomial commutes with a field embedding. Consequently, a square
Jacobian that is nonsingular over the coefficient field remains nonsingular after extending
scalars and mapping its evaluation point. These lemmas let executable polynomial systems stay
over their construction field while root solvers and coverage theorems work over an extension.
-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {F L : Type*} [Field F] [Field L] [BEq F] [LawfulBEq F]

omit [BEq F] [LawfulBEq F] in
/-- Evaluation commutes with mapping both coefficients and point coordinates to an extension. -/
theorem eval₂_map_point {n : ℕ} (ι : F →+* L) (point : Fin n → F)
    (polynomial : CMvPolynomial n F) :
    polynomial.eval₂ ι (fun i => ι (point i)) = ι (polynomial.eval point) := by
  rw [CPoly.eval₂_equiv, CPoly.eval_equiv]
  have hmap := MvPolynomial.map_eval₂Hom
    (f := RingHom.id F) (g := point) (φ := ι)
    (p := fromCMvPolynomial polynomial)
  change (MvPolynomial.eval₂Hom ι (fun i => ι (point i)))
      (fromCMvPolynomial polynomial) =
    ι ((MvPolynomial.eval₂Hom (RingHom.id F) point) (fromCMvPolynomial polynomial))
  simpa only [RingHom.comp_id] using hmap.symm

omit [BEq F] [LawfulBEq F] in
/-- Vanishing at a base-field point is equivalent to vanishing at its image in an extension. -/
theorem eval₂_map_point_eq_zero_iff {n : ℕ} (ι : F →+* L) (point : Fin n → F)
    (polynomial : CMvPolynomial n F) :
    polynomial.eval₂ ι (fun i => ι (point i)) = 0 ↔ polynomial.eval point = 0 := by
  rw [eval₂_map_point]
  exact map_eq_zero_iff ι ι.injective

/-- A nonzero concrete Jacobian determinant stays nonzero after scalar extension.

Rows are equations and columns are partial-derivative coordinates, matching the matrices passed
to the affine square-system solver. -/
theorem jacobian_det_ne_zero_map {s : ℕ} (ι : F →+* L) (point : Fin s → F)
    (system : Fin s → CMvPolynomial s F)
    (hdet : (Matrix.det fun row column =>
      (partialDerivative column (system row)).eval₂ (RingHom.id F) point) ≠ 0) :
    (Matrix.det fun row column =>
      (partialDerivative column (system row)).eval₂ ι (fun i => ι (point i))) ≠ 0 := by
  let baseJacobian : Matrix (Fin s) (Fin s) F := fun row column =>
    (partialDerivative column (system row)).eval₂ (RingHom.id F) point
  let extendedJacobian : Matrix (Fin s) (Fin s) L := fun row column =>
    (partialDerivative column (system row)).eval₂ ι (fun i => ι (point i))
  have hdetBase : baseJacobian.det ≠ 0 := hdet
  have hmatrix : extendedJacobian = baseJacobian.map ι := by
    ext row column
    exact eval₂_map_point ι point (partialDerivative column (system row))
  change extendedJacobian.det ≠ 0
  rw [hmatrix]
  have hmapMatrix : baseJacobian.map ι = ι.mapMatrix baseJacobian := by
    ext row column
    rfl
  rw [hmapMatrix, ← ι.map_det]
  intro hzero
  apply hdetBase
  apply ι.injective
  exact hzero.trans ι.map_zero.symm

end CPoly.CMvPolynomial
