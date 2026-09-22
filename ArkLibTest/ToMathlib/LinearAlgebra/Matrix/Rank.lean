/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank

/-!
# Coordinate-matrix rank acceptance tests

* The coordinate matrix of the identity of `Fin 2 → ℚ` in the standard basis has rank `2`, and the
  coordinate matrix of the zero map has rank `0`, both computed by `Matrix.rank_of_basis`.
* The coordinate matrix of the evaluation-style map `(a, b) ↦ (n ↦ a + n * b)` has the infinite row
  type `ℕ` and rank `2`.
* The source shape `Matrix.rank_map_algebraMap_le` for a field extension, derived from
  `Matrix.rank_map_le`.
-/

open Module

/-- The identity map has coordinate matrix of rank `2`. -/
example : (Matrix.of fun i j => (LinearMap.id : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ))
    (Pi.basisFun ℚ (Fin 2) j) i).rank = 2 := by
  rw [Matrix.rank_of_basis, LinearMap.range_id, finrank_top, Module.finrank_fin_fun]

/-- The zero map has coordinate matrix of rank `0`. -/
example : (Matrix.of fun i j => (0 : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ))
    (Pi.basisFun ℚ (Fin 2) j) i).rank = 0 := by
  rw [Matrix.rank_of_basis, LinearMap.range_zero, finrank_bot]

/-- A map into sequences, with infinitely many rows, has rank `2`: it is injective since the
values at `0` and `1` recover `a` and `b`. -/
example : let f : (Fin 2 → ℚ) →ₗ[ℚ] (ℕ → ℚ) :=
      { toFun := fun v n => v 0 + n * v 1
        map_add' := fun v w => by ext n; simp; ring
        map_smul' := fun c v => by ext n; simp; ring }
    (Matrix.of fun i j => f (Pi.basisFun ℚ (Fin 2) j) i).rank = 2 := by
  intro f
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0 h1
    ext i
    fin_cases i <;> simp <;> push_cast at h0 h1 <;> linarith
  rw [Matrix.rank_of_basis, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

/-- Source shape `Matrix.rank_map_algebraMap_le`: base change to an extension field does not
increase the rank, for any row type. -/
example {F E ι κ : Type*} [Field F] [Field E] [Algebra F E] [Fintype κ] (A : Matrix ι κ F) :
    (A.map (algebraMap F E)).rank ≤ A.rank :=
  Matrix.rank_map_le _ A
