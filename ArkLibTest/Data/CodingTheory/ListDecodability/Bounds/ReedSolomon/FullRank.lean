/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.FullRank
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs

/-! # Full column rank acceptance tests

The triangle on three vertices, with its three edges as the coordinates, is `1`-weakly
partition-connected, so its intersection matrix for degree `1` has a nonzero `2 × 2` minor, over `ℚ`
and over `ZMod 2`. Over `ℚ`, some Reed–Solomon code of length `4` and dimension `2` has lists of
size at most `2` at relative radius `2 / 3 * (1 - 2 / 4) = 1 / 3`, and so does every such code on
evaluation points off the zero set of some nonzero polynomial, also over `ZMod 5`.
-/

open Finset ReedSolomon Code

private def triangle : Fin 3 → Finset (Fin 3) := ![{0, 1}, {1, 2}, {0, 2}]

/-- The triangle is `1`-weakly partition-connected: its weight is `3 ≥ 1 * 2`, and every
two-vertex set carries exactly one edge, of weight `1 ≤ 1 * 1`. -/
private theorem triangle_isWeaklyPartitionConnected :
    IsWeaklyPartitionConnected triangle (1 : ℕ) := by
  refine isWeaklyPartitionConnected_of_forall_ssubset ?_ fun U hU hU2 ↦ ?_
  · exact_mod_cast (by decide : 1 * (Fintype.card (Fin 3) - 1) ≤ ∑ i, (#(triangle i) - 1))
  · have key : ∀ U : Finset (Fin 3), U ≠ univ → 2 ≤ #U →
        ∑ i, (#(triangle i ∩ U) - 1) ≤ #U - 1 := by
      decide
    rw [Nat.cast_one, one_mul]
    exact_mod_cast key U hU.ne hU2

example : ∃ α : Fin 3 → ℚ, IsRigid triangle 1 α :=
  exists_isRigid_of_isWeaklyPartitionConnected ℚ triangle_isWeaklyPartitionConnected

example : ∃ ρ : Fin 2 × Fin 1 → IntersectionRow triangle,
    ((intersectionMatrix ℚ triangle 1).submatrix ρ id).det ≠ 0 :=
  exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected ℚ triangle_isWeaklyPartitionConnected

-- The coefficient field may be finite.
example : ∃ ρ : Fin 2 × Fin 1 → IntersectionRow triangle,
    ((intersectionMatrix (ZMod 2) triangle 1).submatrix ρ id).det ≠ 0 :=
  exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected (ZMod 2)
    triangle_isWeaklyPartitionConnected

example : ∃ P : MvPolynomial (Fin 4) ℚ, P ≠ 0 ∧ ∀ α : Fin 4 ↪ ℚ, MvPolynomial.eval (⇑α) P ≠ 0 →
    Lambda (code α 2 : Set (Fin 4 → ℚ)) (1 / 3) ≤ 2 := by
  obtain ⟨P, hP, h⟩ := exists_ne_zero_Lambda_le_of_eval_ne_zero (ι := Fin 4) ℚ 2 (ℓ := 2) two_pos
  refine ⟨P, hP, fun α hα ↦ ?_⟩
  convert h α hα using 2
  norm_num

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

-- The field may be finite.
example : ∃ P : MvPolynomial (Fin 4) (ZMod 5), P ≠ 0 ∧ ∀ α : Fin 4 ↪ ZMod 5,
    MvPolynomial.eval (⇑α) P ≠ 0 → Lambda (code α 2 : Set (Fin 4 → ZMod 5)) (1 / 3) ≤ 2 := by
  obtain ⟨P, hP, h⟩ :=
    exists_ne_zero_Lambda_le_of_eval_ne_zero (ι := Fin 4) (ZMod 5) 2 (ℓ := 2) two_pos
  refine ⟨P, hP, fun α hα ↦ ?_⟩
  convert h α hα using 2
  norm_num

-- Over an infinite field, points off the zero set of the polynomial exist.
example : ∃ α : Fin 4 ↪ ℚ, Lambda (code α 2 : Set (Fin 4 → ℚ)) (1 / 3) ≤ 2 := by
  obtain ⟨P, hP, h⟩ := exists_ne_zero_Lambda_le_of_eval_ne_zero (ι := Fin 4) ℚ 2 (ℓ := 2) two_pos
  obtain ⟨x, hx, hPx⟩ := MvPolynomial.exists_injective_eval_ne_zero hP
  refine ⟨⟨x, hx⟩, ?_⟩
  convert h ⟨x, hx⟩ hPx using 2
  norm_num
