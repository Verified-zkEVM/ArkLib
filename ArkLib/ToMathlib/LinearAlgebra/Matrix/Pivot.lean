/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Pivot form of a matrix with independent rows

`Matrix.exists_mul_eq_pivot`: a matrix `A` with linearly independent rows has an invertible `B`
and a column embedding `S` with `(B * A) r (S r') = if r = r' then 1 else 0`: choose `s`
independent columns of `A` and let `B` be the inverse of that `s × s` submatrix.
-/

@[expose] public section

namespace Matrix

/-- Pivot form `B A = [I | W]` up to a column embedding `S`: `B` inverts `s` independent columns. -/
theorem exists_mul_eq_pivot {F : Type*} [Field F] {s L : ℕ} (A : Matrix (Fin s) (Fin L) F)
    (hA : LinearIndependent F A) :
    ∃ (S : Fin s ↪ Fin L) (B : Matrix (Fin s) (Fin s) F), IsUnit B.det ∧
      ∀ r r', (B * A) r (S r') = if r = r' then 1 else 0 := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F A.col
  have hrank : A.rank = s := by simpa using hA.rank_matrix
  have h1 : Module.finrank F (Submodule.span F (Set.range A.col)) = s := by
    rw [← Matrix.rank_eq_finrank_span_cols]; exact hrank
  have : Fintype κ := Fintype.ofInjective a ha
  have h2 := finrank_span_eq_card hli
  rw [hsp, h1] at h2
  let e : Fin s ≃ κ := (Fintype.equivFinOfCardEq h2.symm).symm
  let S : Fin s ↪ Fin L := ⟨a ∘ e, ha.comp e.injective⟩
  let N : Matrix (Fin s) (Fin s) F := A.submatrix id S
  have hN : IsUnit N := by
    rw [← Matrix.linearIndependent_col_iff_isUnit]
    exact hli.comp e e.injective
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).1 hN
  refine ⟨S, N⁻¹, Matrix.isUnit_nonsing_inv_det _ hdet, fun r r' => ?_⟩
  have : (N⁻¹ * A) r (S r') = (N⁻¹ * N) r r' := by simp [Matrix.mul_apply, N]
  rw [this, Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]

end Matrix
