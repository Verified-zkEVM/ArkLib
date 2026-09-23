/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Symbolic
import Mathlib.Algebra.Field.ZMod

/-!
# First-order symbolic assembly acceptance tests

These examples check coefficient-height preservation and first-order support for a constant
source column over a small finite field.
-/

open PolynomialDifferential Polynomial ReedSolomon.HiddenDerivative

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def constantSourceColumns : Fin 1 → SourceColumn 1 := fun _ => ⟨0, 0, fun _ => 0⟩

/-- The coefficient of an assembled constant column retains its degree bound. -/
example :
    ∀ u, ((SourceColumn.interpolant constantSourceColumns
      (fun _ ↦ (1 : (ZMod 5)[X]))).coeff u).natDegree ≤ 0 := by
  exact coeff_interpolant_natDegree_le constantSourceColumns
    (by intro i j _; exact Subsingleton.elim _ _) (fun _ ↦ (1 : (ZMod 5)[X]))
    (by intro j; norm_num)

/-- A constant source column assembles to a polynomial in the finite first-order support. -/
example :
    SourceColumn.interpolant constantSourceColumns
      (fun _ ↦ (1 : (ZMod 5)[X])) ∈ firstOrderSpace (ZMod 5)[X] 1 1 1 0 0 := by
  apply interpolant_mem_firstOrderSpace
  · intro j
    rw [mem_firstOrderExponents_iff_coordinates]
    simp [constantSourceColumns, SourceColumn.exponent]
