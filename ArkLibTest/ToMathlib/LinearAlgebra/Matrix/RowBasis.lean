/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis

/-!
# Acceptance client for actual-row bases

This ordinary-import client checks that the selector supports non-`Fin` row and column types and
that its span equality has the useful orientation for recovering every row.
-/

namespace Matrix

/-- Every row belongs to the span of the selected actual rows for arbitrary finite indices. -/
example (A : Matrix Bool (Fin 3) ℚ) :
    ∃ rows : Fin A.rank → Bool,
      LinearIndependent ℚ (fun i ↦ A.row (rows i)) ∧
        ∀ i, A.row i ∈ Submodule.span ℚ (Set.range fun j ↦ A.row (rows j)) := by
  obtain ⟨rows, hlinearIndependent, hspan⟩ := A.exists_rows_linearIndependent_span_eq
  refine ⟨rows, hlinearIndependent, fun i ↦ ?_⟩
  rw [hspan]
  exact Submodule.subset_span ⟨i, rfl⟩

end Matrix

/--
info: 'Matrix.exists_rows_linearIndependent_span_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_rows_linearIndependent_span_eq
