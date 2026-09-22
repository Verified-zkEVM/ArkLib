/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Tensor actions in ring-switching coordinates

The row and column decompositions use opposite tensor factors for scalar multiplication.
These tests check their pure-tensor formulas and distinguish the decompositions on the
proper field extension `ℂ/ℝ`.
-/

open Module RingSwitching
open scoped TensorProduct

namespace ArkLibTest.RingSwitchingTensorActions

section Coordinates

variable {K L : Type} {ι : Type*} [CommRing K] [CommRing L] [Algebra K L]

example : algebraMap L (L ⊗[K] L) = Algebra.TensorProduct.includeLeftRingHom := rfl

example (β : Basis ι K L) (x y : L) (i : ι) :
    decompose_tensor_algebra_columns (L := L) (K := K) β (x ⊗ₜ[K] y) i =
      β.repr y i • x := by
  exact Basis.baseChange_repr_tmul L β x y i

example (β : Basis ι K L) (x y : L) (i : ι) :
    decompose_tensor_algebra_rows (L := L) (K := K) β (x ⊗ₜ[K] y) i =
      β.repr x i • y := by
  let rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := L)
  let rightModule := rightAlgebra.toModule
  exact Basis.baseChangeRight_repr_tmul β x y i

end Coordinates

-- Row and column coordinates differ on a proper extension, despite equal tensor factors.
example :
    decompose_tensor_algebra_columns (L := ℂ) (K := ℝ) Complex.basisOneI
        (Complex.I ⊗ₜ[ℝ] (1 : ℂ)) ≠
      decompose_tensor_algebra_rows (L := ℂ) (K := ℝ) Complex.basisOneI
        (Complex.I ⊗ₜ[ℝ] (1 : ℂ)) := by
  intro h
  have h01 := congrFun h 1
  simp [decompose_tensor_algebra_columns, decompose_tensor_algebra_rows,
    Basis.baseChange_repr_tmul, Basis.baseChangeRight_repr_tmul,
    Complex.coe_basisOneI_repr] at h01

end ArkLibTest.RingSwitchingTensorActions
