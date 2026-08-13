/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Additional determinant lemmas

## Main statements

* `Matrix.pow_dvd_det_of_forall_mem_col_dvd` — a common divisor of `k` whole columns divides
  the determinant to the `k`-th power.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

namespace Matrix

/-- If every entry of each column indexed by `t` is divisible by `d`, then
`d ^ t.card` divides the determinant. -/
lemma pow_dvd_det_of_forall_mem_col_dvd {R : Type*} [CommRing R] {n : Type*}
    [DecidableEq n] [Fintype n] (M : Matrix n n R) (d : R) (t : Finset n)
    (h : ∀ j ∈ t, ∀ i, d ∣ M i j) :
    d ^ t.card ∣ M.det := by
  classical
  induction t using Finset.induction generalizing M with
  | empty => simp
  | insert j₀ t hj₀ ih =>
    choose v hv using fun i => h j₀ (Finset.mem_insert_self j₀ t) i
    have hM : M = Matrix.updateCol M j₀ (fun i => d * v i) := by
      ext i j
      by_cases hj : j = j₀
      · subst hj; rw [Matrix.updateCol_apply, if_pos rfl, hv i]
      · rw [Matrix.updateCol_apply, if_neg hj]
    rw [Finset.card_insert_of_notMem hj₀, hM]
    have hsmul : (Matrix.updateCol M j₀ fun i => d * v i) =
        Matrix.updateCol M j₀ (d • v) := by
      congr 1
    rw [hsmul, Matrix.det_updateCol_smul]
    have hrec : d ^ t.card ∣ (Matrix.updateCol M j₀ v).det := by
      refine ih (Matrix.updateCol M j₀ v) fun j hj i => ?_
      have hne : j ≠ j₀ := fun hcontra => hj₀ (hcontra ▸ hj)
      rw [Matrix.updateCol_apply, if_neg hne]
      exact h j (Finset.mem_insert_of_mem hj) i
    rw [pow_succ']
    exact mul_dvd_mul_left d hrec

end Matrix
