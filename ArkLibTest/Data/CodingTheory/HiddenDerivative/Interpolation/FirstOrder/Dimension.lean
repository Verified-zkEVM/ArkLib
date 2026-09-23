/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Dimension

/-!
# First-order dimension acceptance tests

Concrete dimensions computed by `finrank_firstOrderSpace_eq_firstOrderDimensionCount`, including
`D = 1`, and cases at `D = 0` where the residual form of the weight condition and the count
formula both fail.
-/

open ReedSolomon.HiddenDerivative

/-- `D = 2`, `A = 3`, `m = 1`, `M = 0`, `μ = 1`: the monomials are `1, X, X², Y₀`. -/
example : Module.finrank ℚ (firstOrderSpace ℚ 2 3 1 0 1) = 4 := by
  rw [finrank_firstOrderSpace_eq_firstOrderDimensionCount ℚ (by norm_num)]
  decide

/-- `D = 1`, `A = 3`, `m = 1`, `M = 1`, `μ = 1`: the monomials `1, X, X²`, then `Y₀, X Y₀` of
weight `1 + x`, then `Y₁, X Y₁, X² Y₁` of weight `x`. -/
example : Module.finrank ℚ (firstOrderSpace ℚ 1 3 1 1 1) = 8 := by
  rw [finrank_firstOrderSpace_eq_firstOrderDimensionCount ℚ (by norm_num)]
  decide

/-- The count is the number of its coordinate triples. -/
example : (firstOrderDimensionCoordinates 2 3 1 0 1).card = 4 := by
  rw [card_firstOrderDimensionCoordinates]
  decide

/-- The count adds `b` before subtracting `D t`: at `D = 3`, `m A = 2`, `t = b = 1` the residual
is `2 + 1 - 3 = 0`, while `2 - 3 + 1` would be `1`. -/
example : firstOrderDimensionCount 3 2 1 1 1 = 2 := by decide

/-- At `D = 0`, `m A = 1`, `x = 1`, `a = 0`, `b = 1`, the weight condition `1 < 1` fails but the
residual condition `1 < 2` holds: `firstOrderWeight_lt_iff_lt_residual` needs `0 < D`. -/
example : ¬ (1 + 0 * 0 + (0 - 1) * 1 < 1 * 1) ∧ 1 < 1 * 1 + 1 - 0 * (0 + 1) := by decide

/-- At `D = 0` and `m A = 0` no exponent is eligible, but the count is `1`:
`card_firstOrderExponents` needs `0 < D`. -/
example : (firstOrderExponents 0 0 1 1 1).card = 0 ∧ firstOrderDimensionCount 0 0 1 1 1 = 1 := by
  refine ⟨?_, by decide⟩
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro u hu
  simpa using (mem_firstOrderExponents.mp hu).2.2
