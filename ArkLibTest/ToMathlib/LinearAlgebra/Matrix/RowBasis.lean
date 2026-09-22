/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis

/-!
# Acceptance client for actual-row bases

This ordinary-import client checks that the selector supports non-`Fin` row and column types and
that its span equality has the useful orientation for recovering every row. It also checks the
kernel transfer in the field case, where the identity embedding makes the selector domain
`Fin A.rank`, and in a ring case, where a rank-zero integer matrix annihilates every vector.
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

/-- Over a field, `A.rank` actual rows cut out the same right kernel as all rows. With
`φ := RingHom.id K`, the selector domain `Fin (A.map φ).rank` is `Fin A.rank` by definition. -/
example {K m n : Type*} [Field K] [Finite m] [Fintype n] (A : Matrix m n K) :
    ∃ rows : Fin A.rank → m, ∀ v : n → K, A.submatrix rows id *ᵥ v = 0 ↔ A *ᵥ v = 0 :=
  A.exists_rows_submatrix_mulVec_eq_zero_iff (RingHom.id K) Function.injective_id

/-- An integer matrix whose rank over `ℚ` is zero annihilates every integer vector: the selected
submatrix has no rows, so its kernel condition holds for every vector. -/
example (M : Matrix Bool (Fin 3) ℤ) (hrank : (M.map (Int.castRingHom ℚ)).rank = 0)
    (v : Fin 3 → ℤ) : M *ᵥ v = 0 := by
  obtain ⟨rows, hrows⟩ :=
    M.exists_rows_submatrix_mulVec_eq_zero_iff (Int.castRingHom ℚ) Int.cast_injective
  apply (hrows v).mp
  funext i
  exact absurd (i.isLt.trans_eq hrank) (Nat.not_lt_zero _)

end Matrix

/--
info: 'Matrix.exists_rows_linearIndependent_span_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_rows_linearIndependent_span_eq

/--
info: 'Matrix.exists_rows_submatrix_mulVec_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_rows_submatrix_mulVec_eq_zero_iff
