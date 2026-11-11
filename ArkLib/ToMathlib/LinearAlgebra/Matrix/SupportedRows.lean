/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Restricting a matrix to rows that contain its nonzero entries

Let `r : m' → m` be a family of rows of a matrix `M` whose range contains every row with a
nonzero entry. The rows outside the range are zero, so the submatrix `M.submatrix r id` has the
same kernel as `M`, and over a field the same rank. This reduces a matrix with an infinite row
type but finitely many nonzero rows to a matrix with finitely many rows.

## Main statements

* `Matrix.submatrix_mulVec_eq_zero_iff_of_ne_zero_mem_range`: the two kernels agree.
* `Matrix.rank_submatrix_eq_of_ne_zero_mem_range`: over a field the two ranks agree.
-/

@[expose] public section

namespace Matrix

variable {m m' n R : Type*} [Fintype n]

/-- If every row of `M` with a nonzero entry is in the range of `r`, then `M.submatrix r id` and
`M` have the same kernel. -/
theorem submatrix_mulVec_eq_zero_iff_of_ne_zero_mem_range [NonUnitalNonAssocSemiring R]
    (M : Matrix m n R) (r : m' → m) (hr : ∀ i j, M i j ≠ 0 → i ∈ Set.range r) (v : n → R) :
    M.submatrix r id *ᵥ v = 0 ↔ M *ᵥ v = 0 := by
  constructor
  · intro h
    funext i
    by_cases hi : i ∈ Set.range r
    · obtain ⟨i', rfl⟩ := hi
      simpa [mulVec, dotProduct] using congrFun h i'
    · have hzero : ∀ j, M i j = 0 := fun j => by
        by_contra hne
        exact hi (hr i j hne)
      simp [mulVec, dotProduct, hzero]
  · intro h
    funext i'
    simpa [mulVec, dotProduct] using congrFun h (r i')

/-- Over a field, if every row of `M` with a nonzero entry is in the range of `r`, then
`M.submatrix r id` and `M` have the same rank. -/
theorem rank_submatrix_eq_of_ne_zero_mem_range {K : Type*} [Field K] (M : Matrix m n K)
    (r : m' → m) (hr : ∀ i j, M i j ≠ 0 → i ∈ Set.range r) :
    (M.submatrix r id).rank = M.rank := by
  have hker : LinearMap.ker (M.submatrix r id).mulVecLin = LinearMap.ker M.mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, mulVecLin_apply]
    exact submatrix_mulVec_eq_zero_iff_of_ne_zero_mem_range M r hr v
  have h₁ := LinearMap.finrank_range_add_finrank_ker (M.submatrix r id).mulVecLin
  have h₂ := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [hker] at h₁
  rw [rank, rank]
  omega

end Matrix
