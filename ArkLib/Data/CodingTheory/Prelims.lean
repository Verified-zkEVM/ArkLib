/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.AffineSpace.Pointwise


noncomputable section

variable {F : Type*}
         {ι : Type*} [Fintype ι]
         {ι' : Type*} [Fintype ι']
         {m n : ℕ}

namespace Matrix

/-- The set of column indices where two matrices differ. -/
def neqCols [DecidableEq F] (U V : Matrix ι ι' F) : Finset ι' :=
  {j | ∃ i : ι, V i j ≠ U i j}

section

variable [Semiring F] (U : Matrix ι ι' F)

/-- The submodule spanned by the rows of a matrix. -/
def rowSpan : Submodule F (ι' → F) :=
  Submodule.span F {U i | i : ι}

/-- The row rank of a matrix (dimension of the row span). -/
def rowRank : ℕ :=
  Module.finrank F (rowSpan U)

/-- The submodule spanned by the columns of a matrix. -/
def colSpan : Submodule F (ι → F) :=
  Submodule.span F {Matrix.transpose U i | i : ι'}

/-- The column rank of a matrix (dimension of the column span). -/
def colRank : ℕ :=
  Module.finrank F (colSpan U)


end

section

/-- Extract an n×n submatrix from an m×n matrix by selecting n rows. -/
def subUpFull (U : Matrix (Fin m) (Fin n) F) (r_reindex : Fin n → Fin m) :
  Matrix (Fin n) (Fin n) F := Matrix.submatrix U r_reindex id

/-- Extract an m×m submatrix from an m×n matrix by selecting m columns. -/
def subLeftFull (U : Matrix (Fin m) (Fin n) F) (c_reindex : Fin m → Fin n) :
  Matrix (Fin m) (Fin m) F := Matrix.submatrix U id c_reindex

variable [CommRing F] [Nontrivial F]
         {U : Matrix (Fin m) (Fin n) F}

/-- The rank of a matrix equals the minimum of its row rank and column rank. -/
lemma rank_eq_min_row_col_rank : U.rank = min (rowRank U) (colRank U) := by sorry

/-- A square matrix has full rank if and only if its determinant is nonzero. -/
lemma rank_eq_iff_det_ne_zero {U : Matrix (Fin n) (Fin n) F} :
  U.rank = n ↔ Matrix.det U ≠ 0 := by sorry

/-- An m×n matrix has rank n if and only if some n×n row submatrix has rank n. -/
lemma rank_eq_iff_subUpFull_eq (h : n ≤ m) :
  U.rank = n ↔ (subUpFull U (Fin.castLE h)).rank = n := sorry

/-- An m×n matrix has full rank if the submatrix consisting of rows 1 through n has rank n. -/
lemma rank_eq_if_subUpFull_eq (h : n ≤ m) :
   (subUpFull U (Fin.castLE h)).rank = n  → U.rank = n  := by
   intro h_sub_mat_rank
   apply le_antisymm
   ·  exact Matrix.rank_le_width U
   ·  calc n = (subUpFull U (Fin.castLE h)).rank := by rw[h_sub_mat_rank]
           _ ≤ U.rank := by exact Matrix.rank_submatrix_le (Fin.castLE h) (Equiv.refl (Fin n)) U

/-- cRank and Rank agree for a finite matirx -/
lemma cRank_rank_conversion :
  ↑(U.rank) = U.cRank := by
  rw[
    Matrix.rank_eq_finrank_span_cols,
    ← Matrix.cRank_toNat_eq_finrank,
    Cardinal.cast_toNat_of_lt_aleph0
  ]
  calc U.cRank ≤ ↑(Fintype.card (Fin n)) := by exact Matrix.cRank_le_card_width U
         _ = ↑n := by rw[Fintype.card_fin]
  exact Cardinal.nat_lt_aleph0 n

/-- An m×n matrix has full rank if the submatrix consisting of columns 1 through m has rank m. -/
lemma full_row_rank_via_rank_subLeftFull (h : m ≤ n) :
   (subLeftFull U (Fin.castLE h)).rank = m → U.rank = m := by
   intro h_sub_mat_rank
   rw[
    Matrix.rank_eq_finrank_span_cols,
    ← Matrix.cRank_toNat_eq_finrank
   ]
   have h_cRank : U.cRank = ↑m := by
    apply le_antisymm
    · calc U.cRank ≤ ↑(Fintype.card (Fin m)) := Matrix.cRank_le_card_height U
           _ = ↑m := by rw[Fintype.card_fin]
    · calc ↑m = ↑((subLeftFull U (Fin.castLE h)).rank) := by rw[h_sub_mat_rank]
           _ = (subLeftFull U (Fin.castLE h)).cRank := by exact cRank_rank_conversion
           _ ≤ U.cRank := by exact Matrix.cRank_submatrix_le U id (Fin.castLE h)
   simp [h_cRank]

/-- A square matrix over an integral domain has full rank if its determinant is nonzero. -/
lemma rank_eq_if_det_ne_zero {U : Matrix (Fin n) (Fin n) F} [IsDomain F] :
  Matrix.det U ≠ 0 → U.rank = n  := by
    intro h_det
    have h_ind : (LinearIndependent F U.col) := Matrix.linearIndependent_cols_of_det_ne_zero h_det
    rw[
      Matrix.rank_eq_finrank_span_cols,
      finrank_span_eq_card h_ind,
      Fintype.card_fin
    ]


end

section

variable [Field F]
         {U : Matrix (Fin m) (Fin n) F}

/-- The rank of a matrix equals the column rank. -/
lemma rank_eq_colRank : U.rank = colRank U :=
  Matrix.rank_eq_finrank_span_cols U

/-- The row rank of a matrix equals the column rank. -/
lemma rowRank_eq_colRank : rowRank U = colRank U := by
  rw [← rank_eq_colRank, ← rank_transpose, rank_eq_colRank]
  rfl

/-- The rank of a matrix equals the row rank. -/
lemma rank_eq_rowRank : U.rank = rowRank U := by
  rw [rank_eq_colRank, rowRank_eq_colRank]

end

end Matrix

end

namespace Affine
section
variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {k : ℕ}

/-- Affine line between two vectors with coefficients in a semiring. -/
def line [Ring F] (u v : ι → F) : AffineSubspace F (ι → F) :=
  affineSpan _ {u, v}

variable [DecidableEq F]

variable [Field F] [Fintype F]

/-- Vector addition action on affine subspaces. -/
instance : VAdd (ι → F) (AffineSubspace F (ι → F)) := AffineSubspace.pointwiseVAdd

/-- A translate of a finite affine subspace is finite. -/
noncomputable instance {v : ι → F} {s : AffineSubspace F (ι → F)} [Fintype s] :
    Fintype (v +ᵥ s) := Fintype.ofFinite ↥(v +ᵥ s)

/-- The affine span of a set is finite over a finite field. -/
noncomputable instance {s : Set (ι → F)} : Fintype (affineSpan F s) :=
  Fintype.ofFinite ↥(affineSpan F s)

/-- The image of a function `Fin k → α` over `Finset.univ` is nonempty when `k ≠ 0`. -/
instance [NeZero k] {f : Fin k → ι → F} : Nonempty (Finset.univ.image f) := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and, nonempty_subtype]
  exact ⟨f 0, 0, by simp⟩

/-- A translate of a nonempty affine subspace is nonempty. -/
noncomputable instance {v : ι → F} {s : AffineSubspace F (ι → F)} [inst : Nonempty s] :
    Nonempty (v +ᵥ s) := by
  apply nonempty_subtype.mpr
  rcases inst with ⟨p, h⟩
  exists (v +ᵥ p)
  rw [AffineSubspace.vadd_mem_pointwise_vadd_iff]
  exact h

/-- The carrier set of the affine span of the image of a function `U : Fin k → ι → F`.
  This is the set of all affine combinations of `U 0, U 1, ..., U (k-1)`. -/
abbrev AffSpanSet [NeZero k] (U : Fin k → ι → F) : Set (ι → F) :=
  (affineSpan F (Finset.univ.image U : Set (ι → F))).carrier

/-- The affine span of a finite set of vectors is finite over a finite field. -/
instance AffSpanSet.instFinite [NeZero k] (u : Fin k → ι → F) : (AffSpanSet u).Finite := by
  unfold AffSpanSet
  exact Set.toFinite _

/-- The affine span as a `Finset`, using `AffSpanFinite` to convert from the set. -/
noncomputable def AffSpanFinset [NeZero k] (U : Fin k → ι → F) : Finset (ι → F) :=
  (AffSpanSet.instFinite U).toFinset

/-- A collection of affine subspaces in `F^ι`. -/
noncomputable def AffSpanFinsetCollection {t : ℕ} [NeZero k] [NeZero t]
  (C : Fin t → (Fin k → (ι → F))) : Set (Finset (ι → F)) :=
  Set.range (fun i => AffSpanFinset (C i))

/-- The carrier set of a nonempty finset is nonempty. -/
instance {α : Type*} {s : Finset α} [inst : Nonempty s] : Nonempty (s.toSet) := by
    rcases inst with ⟨w, h⟩
    refine nonempty_subtype.mpr ?_
    exists w

end
end Affine

namespace Curve

section

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*}

/-- Let `u := {u_1, ..., u_l}` be a collection of vectors with coefficients in a semiring.
  The parameterised curve of degree `l` generated by `u` is the set of linear combinations of the
  form `{∑ i ∈ l r ^ i • u_i | r ∈ F}`. -/
def parametrisedCurve {l : ℕ} [Semiring F] (u : Fin l → ι → F) : Set (ι → F)
  := {v | ∃ r : F, v = ∑ i : Fin l, (r ^ (i : ℕ)) • u i}

/-- A parametrised curve over a finite field, as a `Finset`. Requires `DecidableEq ι` and
  `DecidableEq F` to be able to construct the `Finset`. -/
def parametrisedCurveFinite [DecidableEq ι] [Fintype F] [DecidableEq F] [Semiring F]
  {l : ℕ} (u : Fin l → ι → F) : Finset (ι → F) :=
  {v | ∃ r : F, v = ∑ i : Fin l, (r ^ (i : ℕ)) • u i}

/-- A parametrised curve over a nonempty finite field contains at least one point. -/
instance [Fintype F] [Nonempty F] [Semiring F] [DecidableEq ι] [DecidableEq F] {l : ℕ} :
  ∀ u : Fin l → ι → F, Nonempty {x // x ∈ parametrisedCurveFinite u } := by
  intro u
  unfold parametrisedCurveFinite
  simp only [mem_filter, mem_univ, true_and, nonempty_subtype]
  have ⟨r⟩ := ‹Nonempty F›
  use ∑ i : Fin l, r ^ (i : ℕ) • u i, r

end
end Curve

namespace sInf

/-- If every element of a set is bounded above by `i`, then the infimum is also bounded by `i`. -/
lemma sInf_UB_of_le_UB {S : Set ℕ} {i : ℕ} : (∀ s ∈ S, s ≤ i) → sInf S ≤ i := fun h ↦ by
  by_cases S_empty : S.Nonempty
  · classical
    rw [Nat.sInf_def S_empty, Nat.find_le_iff]
    choose s hs using S_empty
    aesop
  · aesop (add simp (show S = ∅ by aesop (add simp Set.Nonempty)))

/-- If `i` is a lower bound for all elements in a nonempty set, then `i` is at most the infimum. -/
lemma le_sInf_of_LB {S : Set ℕ} (hne : S.Nonempty) {i : ℕ}
    (hLB : ∀ s ∈ S, i ≤ s) : i ≤ sInf S := by
  rw [Nat.sInf_def hne]
  contrapose hLB
  simp at hLB ⊢
  rcases hLB with ⟨s, hsS, hsle⟩
  exact ⟨s, hsle, hsS⟩

end sInf

/-- A nonempty fintype has positive cardinality. -/
@[simp]
lemma Fintype.zero_lt_card {ι : Type*} [Fintype ι] [Nonempty ι] : 0 < Fintype.card ι := by
  have := Fintype.card_ne_zero (α := ι); omega

namespace Finset

section

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The diagonal of `s × s` has the same cardinality as `s`. -/
@[simp]
theorem card_filter_prod_self_eq :
  #({x ∈ s ×ˢ s | x.1 = x.2}) = #s := by
  rw [Finset.card_eq_of_equiv]
  simp
  exact ⟨
    fun ⟨x, _⟩ ↦ ⟨x.1, by tauto⟩,
    fun ⟨x, hx⟩ ↦ ⟨(x, x), by tauto⟩,
    by simp [Function.LeftInverse],
    by simp [Function.LeftInverse, Function.RightInverse]
  ⟩

variable [Fintype α]

/-- The number of elements different from a fixed element `e` is one less than the total. -/
@[simp]
theorem card_univ_filter_eq {e : α} :
  #{x : α | x ≠ e} = #(Finset.univ (α := α)) - 1 := by
  rw [
    Finset.filter_congr (q := (· ∉ ({e} : Finset _))) (by simp),
    ←Finset.sdiff_eq_filter, Finset.card_univ_diff
  ]
  simp

/-- The diagonal of `s × s` (intersection form) has the same cardinality as `s`. -/
@[simp]
theorem card_prod_self_eq :
  #(((s ×ˢ s : Finset _) ∩ ({x : α × α | x.1 = x.2} : Finset _)) : Finset _) = #s := by
  rw [Finset.card_eq_of_equiv]
  simp
  exact ⟨
    fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, by tauto⟩,
    (fun ⟨x, _⟩ ↦ by use ⟨x, x⟩),
    by simp [Function.LeftInverse],
    by simp [Function.RightInverse, Function.LeftInverse]
  ⟩

end

end Finset
