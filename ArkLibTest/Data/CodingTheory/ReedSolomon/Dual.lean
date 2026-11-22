/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Dual
import Mathlib.Tactic.NormNum

/-!
# Reed–Solomon duality tests

On the points `0, 1, 2` of `ℚ`, `checkMatrix domain 2` is the single row `(1/2, -1, 1/2)`. It
accepts the evaluations `![1, 2, 3]` of `X + 1` and rejects `![1, 2, 5]`. At `k = 3 = n` the
matrix has no rows, so every word is a codeword.

The column multipliers `Lagrange.nodalWeight univ domain` are `(1/2, -1, 1/2)`, so the dual of
`code domain 2` is the line spanned by `(1, -2, 1)`: every word orthogonal to `code domain 2` is a
multiple of `(1, -2, 1)`, and `(1, -2, 1)` lies in the orthogonal complement of `code domain 2`.
The word `![1, 2, 5]` is not in the orthogonal complement of that generalized Reed–Solomon code.
-/

open ReedSolomon Polynomial

namespace ArkLibTest.ReedSolomonDual

/-- The points `0, 1, 2` of `ℚ`. -/
def domain : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

private lemma domain_apply (i : Fin 3) : domain i = ((i : ℕ) : ℚ) := rfl

/-- `checkMatrix domain 2` is the row `(1/2, -1, 1/2)`. -/
example : checkMatrix domain 2 ⟨0, by simp⟩ = ![1 / 2, -1, 1 / 2] := by
  ext j
  fin_cases j <;> norm_num [checkMatrix, domain_apply, Fin.prod_univ_three]

/-- The evaluations `![1, 2, 3]` of `X + 1` pass the check. -/
example : ![1, 2, 3] ∈ code domain 2 := by
  rw [mem_code_iff_checkMatrix_mulVec_eq_zero]
  ext i
  fin_cases i
  norm_num [checkMatrix, domain_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Fin.prod_univ_three]

/-- `![1, 2, 5]` fails the check: `1/2 - 2 + 5/2 = 1`. -/
example : ![1, 2, 5] ∉ code domain 2 := by
  rw [mem_code_iff_checkMatrix_mulVec_eq_zero]
  intro h
  have := congrFun h ⟨0, by simp⟩
  norm_num [checkMatrix, domain_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Fin.prod_univ_three] at this

/-- At `k = 3 = n` the parity-check matrix has no rows, so every word is a codeword. -/
example (f : Fin 3 → ℚ) : f ∈ code domain 3 :=
  (mem_code_iff_checkMatrix_mulVec_eq_zero domain).2 (funext fun i ↦ absurd i.2 (by simp))

/-- The column multipliers on the points `0, 1, 2` are `(1/2, -1, 1/2)`. -/
private lemma nodalWeight_domain :
    Lagrange.nodalWeight Finset.univ domain = ![1 / 2, -1, 1 / 2] := by
  ext i
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i)]
  fin_cases i <;> norm_num [Lagrange.nodal, domain_apply, Fin.prod_univ_three]

/-- A word orthogonal to `code domain 2` is a multiple of `(1, -2, 1)`. -/
example (u : Fin 3 → ℚ) (hu : ∀ f ∈ code domain 2, u ⬝ᵥ f = 0) :
    u = u 0 • ![1, -2, 1] := by
  obtain ⟨g, hg, rfl⟩ := (forall_mem_code_dotProduct_eq_zero_iff domain).1 hu
  rw [mem_degreeLT, show Fintype.card (Fin 3) - 2 = 1 from rfl] at hg
  rw [eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.1 hg)]
  ext i
  fin_cases i <;> norm_num [nodalWeight_domain, mul_right_comm _ _ (2 : ℚ)]

/-- `(1, -2, 1)` is orthogonal to every codeword of `code domain 2`. -/
example : ∀ f ∈ code domain 2, ![1, -2, 1] ⬝ᵥ f = 0 := by
  refine (forall_mem_code_dotProduct_eq_zero_iff domain).2 ⟨C 2, mem_degreeLT.2 ?_, ?_⟩
  · exact (degree_C_le).trans_lt (by decide)
  · ext i
    fin_cases i <;> norm_num [nodalWeight_domain]

/-- The same vector lies in the orthogonal complement of `code domain 2`, through the submodule
equality `orthogonal_code`. -/
example : ![1, -2, 1] ∈ LinearMap.BilinForm.orthogonal (dotProductBilin ℚ ℚ)
    (code domain 2) := by
  rw [orthogonal_code, mem_grsCode_iff]
  refine ⟨C 2, mem_degreeLT.2 ((degree_C_le).trans_lt (by decide)), ?_⟩
  ext i
  fin_cases i <;> norm_num [nodalWeight_domain]

/-- `![1, 2, 5]` is not in the orthogonal complement of `grsCode domain 1 w`, through the
submodule equality `orthogonal_grsCode` and the parity check. -/
example : ![1, 2, 5] ∉ LinearMap.BilinForm.orthogonal (dotProductBilin ℚ ℚ)
    (grsCode domain 1 (Lagrange.nodalWeight Finset.univ domain)) := by
  rw [show (1 : ℕ) = Fintype.card (Fin 3) - 2 from rfl, orthogonal_grsCode,
    mem_code_iff_checkMatrix_mulVec_eq_zero]
  intro h
  have := congrFun h ⟨0, by simp⟩
  norm_num [checkMatrix, domain_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Fin.prod_univ_three] at this

end ArkLibTest.ReedSolomonDual
