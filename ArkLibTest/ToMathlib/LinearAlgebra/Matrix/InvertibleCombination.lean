/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.InvertibleCombination

/-!
# Acceptance tests for recovering a family from invertible combinations

The examples recover `x 1 = 0` from `x 0 + x 1 = 0` and `x 0 - x 1 = 0`, derive the subalgebra
form of interpolation, and show that both hypotheses are needed: the singular matrix with all
entries `1`, and the Vandermonde matrix at the repeated point `1`, send `x = (1, -1)` to zero
although `x 0 ∉ ⊥`.
-/

namespace InvertibleCombinationTest

/-- From `x 0 + x 1 = 0` and `x 0 - x 1 = 0` over `ℚ`, the matrix `!![1, 1; 1, -1]` of
determinant `-2` recovers `x 1 = 0`. -/
example (x : Fin 2 → ℚ) (h0 : x 0 + x 1 = 0) (h1 : x 0 - x 1 = 0) : x 1 = 0 := by
  have h := Submodule.mem_of_forall_sum_smul_mem (p := (⊥ : Submodule ℚ ℚ)) !![1, 1; 1, -1]
    (by rw [Matrix.det_fin_two_of]; norm_num) (x := x) (fun i ↦ by
      fin_cases i <;> simp [Fin.sum_univ_two, h0, ← sub_eq_add_neg, h1]) 1
  simpa using h

/-- Interpolation in a subalgebra: if the values `∑ j, α i ^ j * a j` at `c` distinct points lie
in `B`, then so does every coefficient `a j`. -/
example {F A : Type*} [Field F] [CommRing A] [Algebra F A] (B : Subalgebra F A) {c : ℕ}
    (α : Fin c ↪ F) (a : Fin c → A)
    (heval : ∀ i, ∑ j : Fin c, algebraMap F A (α i ^ (j : ℕ)) * a j ∈ B) (j : Fin c) : a j ∈ B :=
  Submodule.mem_of_forall_sum_pow_smul_mem (p := Subalgebra.toSubmodule B) α.injective
    (fun i ↦ by simpa only [Algebra.smul_def, Subalgebra.mem_toSubmodule] using heval i) j

/-- The determinant hypothesis is needed: the matrix with all entries `1` sends `(1, -1)` to
zero. -/
example : ∃ x : Fin 2 → ℚ, (∀ i, ∑ j, (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j • x j ∈
    (⊥ : Submodule ℚ ℚ)) ∧ x 0 ∉ (⊥ : Submodule ℚ ℚ) :=
  ⟨![1, -1], fun i ↦ by fin_cases i <;> simp [Fin.sum_univ_two], by simp⟩

/-- Distinct points are needed: evaluating at the point `1` twice sends `(1, -1)` to zero. -/
example : ∃ x : Fin 2 → ℚ, (∀ i : Fin 2, ∑ j : Fin 2, (fun _ ↦ (1 : ℚ)) i ^ (j : ℕ) • x j ∈
    (⊥ : Submodule ℚ ℚ)) ∧ x 0 ∉ (⊥ : Submodule ℚ ℚ) :=
  ⟨![1, -1], fun i ↦ by simp [Fin.sum_univ_two], by simp⟩

end InvertibleCombinationTest
