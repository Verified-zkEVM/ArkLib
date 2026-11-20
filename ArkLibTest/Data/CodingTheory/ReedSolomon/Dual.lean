/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Dual
import Mathlib.Tactic.NormNum

/-!
# Reed–Solomon parity-check matrix tests

On the points `0, 1, 2` of `ℚ`, `checkMatrix domain 2` is the single row `(1/2, -1, 1/2)`. It
accepts the evaluations `![1, 2, 3]` of `X + 1` and rejects `![1, 2, 5]`. At `k = 3 = n` the
matrix has no rows, so every word is a codeword.
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

end ArkLibTest.ReedSolomonDual
