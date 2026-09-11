/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.LinearAlgebra.ShiftedDegreeKernel

/-!
# Polynomial kernel vectors with individual column-degree budgets

Let a polynomial matrix have `rows` rows, and let every entry in column `j` have
degree at most `weight j`. To find a kernel vector whose products have degree at
most `h`, allow its `j`th coordinate exactly `h + 1 - weight j` scalar coefficients.
A column of weight greater than `h` is inactive: its coordinate must be zero.

If the sum of these coefficient counts exceeds `rows * (h + 1)`, the resulting
homogeneous linear system has a nonzero solution. This is the column-sensitive
height test used in the finite Reed–Solomon interpolation certificate of [DKTZ26].
Unlike a uniform bound on all matrix entries, it retains the smaller degrees of
individual columns.

## Reading the statement

* `M` is a matrix over `F[X]`, with any field `F`; `X` is the symbolic challenge.
* `weight` bounds matrix entries, not the unknown kernel coordinates.
* Membership in `Polynomial.degreeLT F c` means degree strictly less than `c`.
  For `c = 0` this forces the zero polynomial, so inactive columns need no exception.
* Subtraction in the coefficient count is natural subtraction, hence truncated at zero.
* The conclusion supplies an actual polynomial vector with `M *ᵥ v = 0`.
  The dimension inequality is sufficient, not a claim of optimal kernel height.

The proof decodes bounded coefficient arrays into polynomials, extracts the first
`h+1` coefficients of each matrix product, and applies rank--nullity. Higher
coefficients vanish by the column-degree bounds.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Section 6.1.3, Proposition 6.3 (finite first-order
  certificate).
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace Matrix

variable {F : Type*} [Field F]

/-- A strict column-sensitive coefficient surplus gives a nonzero polynomial kernel vector.
Its coordinate in column `j` has degree below `h+1-weight j`; inactive coordinates are zero. -/
theorem exists_ne_zero_mulVec_eq_zero_column_degreeLT {rows cols : ℕ}
    (M : Matrix (Fin rows) (Fin cols) F[X]) (weight : Fin cols → ℕ) (h : ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ weight j)
    (hsurplus : rows * (h + 1) < ∑ j, (h + 1 - weight j)) :
    ∃ v : Fin cols → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      ∀ j, v j ∈ Polynomial.degreeLT F (h + 1 - weight j) := by
  have hshifted : Finset.univ.sum (fun _i : Fin rows ↦ h + 1 - 0) <
      Finset.univ.sum (fun j : Fin cols ↦ h + 1 - weight j) := by
    simpa using hsurplus
  exact exists_ne_zero_mulVec_eq_zero_shifted_degreeLT M (fun _ ↦ 0) weight h
    (fun i j _ ↦ by simpa using hdeg i j)
    (fun _i _j hnegative ↦ by omega) hshifted

/-- The column-sensitive height test needs only the rank over `F(X)`, not the number of
original rows. Selecting a basis of original rows preserves their column-degree bounds. -/
theorem exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank
    {rows cols : ℕ} (M : Matrix (Fin rows) (Fin cols) F[X])
    (weight : Fin cols → ℕ) (h : ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ weight j)
    (hsurplus : (M.map (algebraMap F[X] (RatFunc F))).rank * (h + 1) <
      ∑ j, (h + 1 - weight j)) :
    ∃ v : Fin cols → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      ∀ j, v j ∈ Polynomial.degreeLT F (h + 1 - weight j) := by
  classical
  let A := M.map (algebraMap F[X] (RatFunc F))
  obtain ⟨rows, _, hspan⟩ := exists_rows_fin_rank A
  let B : Matrix (Fin A.rank) (Fin cols) F[X] := M.submatrix rows id
  obtain ⟨v, hvne, hB, hvdeg⟩ :=
    exists_ne_zero_mulVec_eq_zero_column_degreeLT B weight h
      (fun i j ↦ by simpa [B] using hdeg (rows i) j) hsurplus
  let w : Fin cols → RatFunc F := fun j ↦ algebraMap F[X] (RatFunc F) (v j)
  have hselected (i : Fin A.rank) : dotProduct (A.row (rows i)) w = 0 := by
    have hi := congrFun hB i
    have hi_map := congrArg (algebraMap F[X] (RatFunc F)) hi
    simpa [B, A, w, Matrix.mulVec, dotProduct] using hi_map
  have hA : A *ᵥ w = 0 := by
    funext i
    change dotProduct (A.row i) w = 0
    have hi : A.row i ∈ Submodule.span (RatFunc F)
        (Set.range fun j ↦ A.row (rows j)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hzero_of_mem {x : Fin cols → RatFunc F}
        (hx : x ∈ Submodule.span (RatFunc F) (Set.range fun j ↦ A.row (rows j))) :
        dotProduct x w = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          exact hselected j
      | zero => simp
      | add x y _ _ hx hy => simp [add_dotProduct, hx, hy]
      | smul a x _ hx => simp [smul_dotProduct, hx]
    exact hzero_of_mem hi
  have hM : M *ᵥ v = 0 := by
    funext i
    apply RatFunc.algebraMap_injective
    have hi := congrFun hA i
    simpa [A, w, Matrix.mulVec, dotProduct] using hi
  exact ⟨v, hvne, hM, hvdeg⟩


/-- Primitive normalization turns the column-height certificate into a kernel vector that
stays nonzero after every challenge specialization over every extension field. The uniform
height `h` is preserved; the individual column budgets are used in the construction above. -/
theorem exists_primitive_mulVec_eq_zero_of_column_surplus
    {rows cols : ℕ} (M : Matrix (Fin rows) (Fin cols) F[X])
    (weight : Fin cols → ℕ) (h : ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ weight j)
    (hsurplus : (M.map (algebraMap F[X] (RatFunc F))).rank * (h + 1) <
      ∑ j, (h + 1 - weight j)) :
    ∃ v : Fin cols → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      (∀ j, (v j).natDegree ≤ h) ∧ Ideal.span (Set.range v) = ⊤ ∧
      ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        (fun j ↦ (v j).eval₂ ι z) ≠ 0 := by
  obtain ⟨v, hv, hMv, hvdeg⟩ :=
    exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank M weight h hdeg hsurplus
  have hvheight (j : Fin cols) : (v j).natDegree ≤ h := by
    have hlt := Polynomial.mem_degreeLT.mp (hvdeg j)
    have hle : ((h + 1 - weight j : ℕ) : WithBot ℕ) ≤ (h + 1 : ℕ) := by
      exact_mod_cast Nat.sub_le (h + 1) (weight j)
    have hmem : v j ∈ Polynomial.degreeLT F (h + 1) :=
      Polynomial.mem_degreeLT.mpr (hlt.trans_le hle)
    rw [Polynomial.degreeLT_succ_eq_degreeLE] at hmem
    exact Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp hmem)
  obtain ⟨u, hu, hMu, hudeg, hspan, hnonzero⟩ :=
    exists_primitive_kernel_vector M v hv hMv
  exact ⟨u, hu, hMu, fun j ↦ (hudeg j).trans (hvheight j), hspan, hnonzero⟩

end Matrix
