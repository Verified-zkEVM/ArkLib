/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Determinant of a block matrix with commuting lower blocks

## Main statements

* `Matrix.det_fromBlocks_of_commute`: if `C` and `D` commute, then
  `det (fromBlocks A B C D) = det (A * D - B * C)`.

This file mirrors Mathlib's `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`, whose
`Matrix.det_fromBlocks₂₂` gives the same reduction through the Schur complement, which needs `D`
invertible. The commuting form needs no invertibility: it is proved over `R[X]` for the
perturbation `D + X • 1`, whose determinant is monic and hence cancellable, and then evaluated at
`X = 0`.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

@[expose] public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The determinant of a block matrix whose lower blocks commute: if `Commute C D`, then
`det (fromBlocks A B C D) = det (A * D - B * C)`. No block needs to be invertible. -/
theorem det_fromBlocks_of_commute (A B C D : Matrix n n R) (hCD : Commute C D) :
    (fromBlocks A B C D).det = (A * D - B * C).det := by
  let φ : R →+* Polynomial R := Polynomial.C
  let ev : Polynomial R →+* R := Polynomial.evalRingHom 0
  have hev : ∀ M : Matrix n n R, (M.map φ).map ev = M := fun M => by
    ext i j; simp [φ, ev]
  -- The perturbation `D + X • 1`, which commutes with the lifted `C`.
  let Xi : Matrix n n (Polynomial R) := (Polynomial.X : Polynomial R) • 1
  let Dx : Matrix n n (Polynomial R) := D.map φ + Xi
  have hCDx : C.map φ * Dx = Dx * C.map φ := by
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, hCD.eq]
  have hmonic : Dx.det.Monic := by
    have hDx : Dx = charmatrix (-D) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Dx, Xi, φ, charmatrix_apply_eq, add_comm]
      · simp [Dx, Xi, φ, hij]
    rw [hDx]
    exact charpoly_monic (-D)
  -- Right-multiplying by `fromBlocks Dx 0 (-C) 1` makes the lower-left block vanish.
  have hmul : fromBlocks (A.map φ) (B.map φ) (C.map φ) Dx * fromBlocks Dx 0 (-C.map φ) 1 =
      fromBlocks (A.map φ * Dx - B.map φ * C.map φ) (B.map φ) 0 Dx := by
    rw [fromBlocks_multiply]
    congr 1 <;> simp [sub_eq_add_neg, hCDx]
  have hcancel : (fromBlocks (A.map φ) (B.map φ) (C.map φ) Dx).det =
      (A.map φ * Dx - B.map φ * C.map φ).det := by
    have h := congrArg det hmul
    rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, mul_one] at h
    exact hmonic.isRegular.right h
  have hX : Xi.map ev = 0 := by
    ext i j; by_cases hij : i = j <;> simp [Xi, ev, hij]
  have hDev : Dx.map ev = D := by
    rw [show Dx.map ev = (D.map φ).map ev + Xi.map ev from Matrix.map_add _ (map_add ev) _ _, hX,
      add_zero, hev]
  have h := congrArg ev hcancel
  rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    fromBlocks_map, hev, hev, hev, hDev, Matrix.map_sub _ (map_sub ev), Matrix.map_mul,
    Matrix.map_mul, hev, hev, hev, hDev] at h
  exact h

end Matrix
