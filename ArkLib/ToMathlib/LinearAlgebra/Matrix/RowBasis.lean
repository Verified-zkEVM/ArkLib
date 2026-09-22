/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Bases selected from matrix rows

This file asks when a basis of a matrix row space can be chosen from the rows themselves. For a
matrix over a field with finitely many rows, `Matrix.exists_rows_linearIndependent_span_eq`
selects exactly `A.rank` actual rows which are linearly independent and span the full row space.
The row and column index types may be any finite types.

The proof applies `Module.Basis.ofSpan` to the rows regarded as elements of their span, then
reindexes the resulting basis by `Fin A.rank`. Polynomial kernel-height arguments use this result
to replace a matrix by a full-row-rank submatrix without changing its row space.

`Matrix.exists_rows_submatrix_mulVec_eq_zero_iff` transfers the selection to a matrix `M` over a
ring `R` that embeds into a field `K` by an injective ring homomorphism `φ`. It selects
`(M.map φ).rank` rows of `M` whose right kernel over `R` equals the right kernel of `M`. The proof
maps a vector `v` to `φ ∘ v`, which reduces both kernel conditions to kernel conditions over `K`.
Over `K`, the vectors orthogonal to `φ ∘ v` form a subspace, so if they contain the selected rows
they contain their span, which is the full row space.
-/

@[expose] public section

namespace Matrix

variable {K : Type*} [Field K]

/-- A matrix with finitely many rows has a row-space basis consisting of actual rows.

The selector is indexed by `Fin A.rank`, so its domain records the exact size of the basis. The
selected rows are linearly independent and their span equals the span of every row of `A`. -/
theorem exists_rows_linearIndependent_span_eq {m n : Type*} [Finite m] [Fintype n]
    (A : Matrix m n K) :
    ∃ rows : Fin A.rank → m,
      LinearIndependent K (fun i ↦ A.row (rows i)) ∧
        Submodule.span K (Set.range fun i ↦ A.row (rows i)) =
          Submodule.span K (Set.range A.row) := by
  classical
  let W := Submodule.span K (Set.range A.row)
  let rowW : m → W := fun i ↦ ⟨A.row i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hspanW : Submodule.span K (Set.range rowW) = ⊤ := by
    apply (Submodule.span_range_subtype_eq_top_iff W _).2
    rfl
  let basisW0 := Module.Basis.ofSpan hspanW.ge
  let basisW := basisW0.reindexRange
  let indexFintype : Fintype (Set.range basisW0) :=
    FiniteDimensional.fintypeBasisIndex basisW
  let _ := indexFintype
  have hb_mem (x : Set.range basisW0) : basisW x ∈ Set.range rowW := by
    rw [show basisW x = (x : W) by exact basisW0.reindexRange_apply x]
    exact Module.Basis.ofSpan_subset hspanW.ge x.property
  let pickRow (x) : m := Classical.choose (hb_mem x)
  have hpick (x) : rowW (pickRow x) = basisW x := Classical.choose_spec (hb_mem x)
  have hfinrankW : Module.finrank K W = A.rank := by
    rw [A.rank_eq_finrank_span_row]
  have hcard : Fintype.card (Set.range basisW0) = A.rank := by
    rw [← Module.finrank_eq_card_basis basisW, hfinrankW]
  let e : Fin A.rank ≃ Set.range basisW0 := (Fintype.equivFinOfCardEq hcard).symm
  let rows : Fin A.rank → m := fun i ↦ pickRow (e i)
  have hrows (i) : A.row (rows i) = basisW (e i) := by
    exact congrArg Subtype.val (hpick (e i))
  refine ⟨rows, ?_, ?_⟩
  · rw [show (fun i ↦ A.row (rows i)) = fun i ↦ (basisW (e i) : n → K) by
      funext i
      exact hrows i]
    exact (basisW.linearIndependent.map' W.subtype W.ker_subtype).comp _ e.injective
  · rw [show (fun i ↦ A.row (rows i)) = fun i ↦ (basisW (e i) : n → K) by
      funext i
      exact hrows i]
    have hrange :
        Set.range (fun i ↦ (basisW (e i) : n → K)) =
          Set.range (fun i ↦ (basisW i : n → K)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, by simp⟩
    rw [hrange]
    change Submodule.span K (Set.range (W.subtype ∘ basisW)) = W
    rw [Set.range_comp, ← Submodule.map_span, basisW.span_eq, Submodule.map_top,
      Submodule.range_subtype]

/-- A matrix over a ring that embeds into a field has a rank-sized set of rows with the same
right kernel.

Let `φ : R →+* K` be an injective ring homomorphism into a field and let `r` be the rank of
`M.map φ` over `K`. There are row indices `rows : Fin r → m` such that, for every vector `v` over
`R`, the selected rows annihilate `v` exactly when every row of `M` does. The selector is indexed
by `Fin r`, so the submatrix `M.submatrix rows id` has exactly `r` rows. A kernel bound that
depends on the number of rows can therefore be applied with the rank in place of the row count.

The injectivity of `φ` is what lets a kernel condition over `R` be checked over `K`: an entry of
`M *ᵥ v` vanishes exactly when its image under `φ` does. The rank is measured over `K` because
the row selection uses a basis of the row space, which requires a field. With `φ := RingHom.id K`
this is the field case, with `A.rank` selected rows. If the rank is zero, the selected submatrix
has no rows, so the theorem says that `M *ᵥ v = 0` for every `v`. -/
theorem exists_rows_submatrix_mulVec_eq_zero_iff {R m n : Type*} [Semiring R] [Finite m]
    [Fintype n] (M : Matrix m n R) (φ : R →+* K) (hφ : Function.Injective φ) :
    ∃ rows : Fin (M.map φ).rank → m,
      ∀ v : n → R, M.submatrix rows id *ᵥ v = 0 ↔ M *ᵥ v = 0 := by
  obtain ⟨rows, -, hspan⟩ := (M.map φ).exists_rows_linearIndependent_span_eq
  refine ⟨rows, fun v ↦ ?_⟩
  have hselected :
      M.submatrix rows id *ᵥ v = 0 ↔ (M.map φ).submatrix rows id *ᵥ (φ ∘ v) = 0 := by
    simp only [funext_iff, Pi.zero_apply, submatrix_map, ← RingHom.map_mulVec,
      map_eq_zero_iff φ hφ]
  have hall : M *ᵥ v = 0 ↔ M.map φ *ᵥ (φ ∘ v) = 0 := by
    simp only [funext_iff, Pi.zero_apply, ← RingHom.map_mulVec, map_eq_zero_iff φ hφ]
  rw [hselected, hall]
  constructor
  · intro h
    have hrowSpace : Submodule.span K (Set.range (M.map φ).row) ≤
        LinearMap.ker ((dotProductBilin K K).flip (φ ∘ v)) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact congrFun h i
    funext i
    exact hrowSpace (Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    funext i
    exact congrFun h (rows i)

end Matrix
