/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.TriangularInjective
import Mathlib.Algebra.BigOperators.Fin

/-!
# Block-triangular injectivity acceptance tests

A two-block instance over `ℚ`, and the failure of injectivity when the off-diagonal hypothesis
`hlow` is dropped.
-/

open LinearMap

/-- The blocks `x ↦ (x, x)` and `y ↦ (0, y)` with the coordinate projections: the second block is
invisible to the first coordinate, so `(x, y) ↦ (x, x + y)` is injective. -/
example : Function.Injective
    (∑ i : Fin 2, (![LinearMap.pi ![LinearMap.id, LinearMap.id],
        LinearMap.pi ![0, LinearMap.id]] i).comp
      (LinearMap.proj i : (Fin 2 → ℚ) →ₗ[ℚ] ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] Fin 2 → ℚ) := by
  refine injective_sum_comp_proj_of_triangular _ (fun i => LinearMap.proj i)
    (fun i j hij x => ?_) (fun i => ?_)
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> intro x y h <;> simpa using h

/-- Without `hlow` the conclusion fails: two identity blocks on `ℚ` have injective diagonal but
their sum `(x, y) ↦ x + y` is not injective. -/
example : ¬ Function.Injective
    (∑ i : Fin 2, (LinearMap.id : ℚ →ₗ[ℚ] ℚ).comp
      (LinearMap.proj i : (Fin 2 → ℚ) →ₗ[ℚ] ℚ) : (Fin 2 → ℚ) →ₗ[ℚ] ℚ) := by
  intro h
  have := congrFun (h (a₁ := ![1, -1]) (a₂ := 0) (by simp [Fin.sum_univ_two])) 0
  simp at this
