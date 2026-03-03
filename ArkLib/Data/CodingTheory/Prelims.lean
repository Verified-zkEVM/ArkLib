/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Chung Thai Nguyen
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import CompPoly.Data.Nat.Bitwise

section TensorCombination
variable {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]
variable {A : Type*} [AddCommMonoid A] [Module F A]
/--
The tensor product weight `⊗_{i=0}^{ϑ-1}(1 - rᵢ, rᵢ)` for a specific index `i` given randomness `r`.
Corresponds to `eq(i, r)` in multilinear polynomial literature.
-/
def multilinearWeight {ϑ : ℕ} (r : Fin ϑ → F) (i : Fin (2 ^ ϑ)) : F :=
  ∏ j : Fin ϑ,
    if i.val.testBit j.val then (r j) else (1 - r j)

omit [Fintype F] [DecidableEq F] in
lemma multilinearWeight_succ {ϑ : ℕ} (r : Fin (ϑ + 1) → F) (i : Fin (2 ^ (ϑ + 1))) :
  (multilinearWeight r i) = (multilinearWeight (r := Fin.init r) (i :=
    ⟨Nat.getLowBits (numLowBits := ϑ) (n := i), by simp [Nat.getLowBits_lt_two_pow]⟩)
  ) *
    (if i.val.testBit (ϑ) then (r (Fin.last ϑ)) else (1 - r (Fin.last ϑ))) := by
  simp only [multilinearWeight, Fin.prod_univ_castSucc]
  simp_rw [Nat.testBit_eq_getBit, Nat.getBit_of_lowBits]
  simp only [Fin.coe_castSucc, Fin.val_last, mul_ite, Fin.is_lt, ↓reduceIte]
  rfl

omit [Fintype F] [DecidableEq F] in
/-- **Lower Half Weight**:
If `i < 2^n`, the tensor weight splits into the weight of the lower bits (using the prefix of r)
multiplied by `(1 - r_n)` (since the n-th bit is 0). -/
lemma multilinearWeight_succ_lower_half {n : ℕ}
    (r : Fin (n + 1) → F) (i : Fin (2 ^ (n + 1)))
    (h_lt : i.val < 2 ^ n) :
    multilinearWeight r i =
    multilinearWeight (Fin.init r) ⟨i.val, by exact h_lt⟩ * (1 - r (Fin.last n)) := by
  -- 1. Apply the generic successor splitting lemma
  rw [multilinearWeight_succ]
  -- 2. Simplify the High Bit Term
  -- Since i < 2^n, the n-th bit is 0
  have h_bit_zero : i.val.testBit n = false := by
    rw [Nat.testBit_eq_false_of_lt]
    exact h_lt
  simp only [h_bit_zero, Bool.false_eq_true, ↓reduceIte]
  -- 3. Simplify the Low Bits Term
  -- Since i < 2^n, getting the low n bits just returns i itself
  congr 2
  apply Fin.eq_of_val_eq
  simp_rw [Nat.getLowBits_eq_mod_two_pow]
  let i_mod_2_pow_n : i.val % (2 ^ n) = i.val := by
    rw [Nat.mod_eq_of_lt (h := h_lt)]
  simp only [i_mod_2_pow_n]

omit [Fintype F] [DecidableEq F] in
/-- **Upper Half Weight**:
If `i = j + 2^n` (where `j < 2^n`), the tensor weight splits into the weight of `j`
(using the prefix of r) multiplied by `r_n` (since the n-th bit is 1).
-/
lemma multilinearWeight_succ_upper_half {n : ℕ}
    (r : Fin (n + 1) → F) (i : Fin (2 ^ (n + 1)))
    (j : Fin (2 ^ n)) (h_eq : i.val = j.val + 2 ^ n) :
    multilinearWeight r i =
    multilinearWeight (Fin.init r) j * (r (Fin.last n)) := by
  rw [multilinearWeight_succ]
  -- 2. Simplify the High Bit Term
  -- i = j + 2^n, so the n-th bit is 1 (since j < 2^n)
  have h_bit_one : i.val.testBit n = true := by
    rw [h_eq]; simp_rw [Nat.testBit_eq_getBit]
    rw [Nat.getBit_1_of_ge_two_pow_and_lt_two_pow_succ (h_ge_two_pow := by omega)
      (h_lt_two_pow_succ := by omega)]
  simp only [h_bit_one, if_true]
  -- 3. Simplify the Low Bits Term
  -- Low n bits of (j + 2^n) is just j
  congr 2
  apply Fin.eq_of_val_eq
  simp only [h_eq]
  rw [Nat.getLowBits_eq_mod_two_pow]
  let j_mod_2_pow_n : j.val % (2 ^ n) = j.val := by
    rw [Nat.mod_eq_of_lt (h := j.isLt)]
  simp only [Nat.add_mod_right]
  simp only [j_mod_2_pow_n]

/-- Linear combination of the rows of `u` according to the tensor product of `r`:
`[tensor_product r i] ·|u₀|`
                      `|u₁|`
                      `|⋮|`
                      `|u_{2^ϑ-1}|`
= `∑_{i=0}^{2^ϑ-1} (multilinearWeight r i) • u_i` -/
def multilinearCombine {ϑ : ℕ} {ι : Type*}
    (u : (Fin (2 ^ ϑ)) → ι → A) (r : Fin ϑ → F) : (ι → A) :=
  fun colIdx => ∑ rowIdx : Fin (2^ϑ), ((multilinearWeight r rowIdx) : F) • ((u rowIdx colIdx) : A)
notation:20 r " |⨂| " u => multilinearCombine (u := u) (r := r)
end TensorCombination
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
  exact Cardinal.natCast_lt_aleph0

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

/-- A square matrix has full rank iff the determinant is nonzero. -/
lemma rank_eq_iff_det_ne_zero {U : Matrix (Fin n) (Fin n) F} :
U.rank = n ↔ U.det ≠ 0 := by
  rw[
    ← isUnit_iff_ne_zero,
    ← Matrix.isUnit_iff_isUnit_det,
    ←  Matrix.linearIndependent_cols_iff_isUnit,
    Matrix.rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span,
    Set.finrank
    ]
  simp[eq_comm]

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

/-- The rank of a matrix equals the minimum of its row rank and column rank. -/
lemma rank_eq_min_row_col_rank : U.rank = min (rowRank U) (colRank U) := by
  rw [rowRank_eq_colRank, rank_eq_colRank]
  simp_all only [min_self]

end

end Matrix

end

namespace Affine
section
variable {ι : Type*} [Fintype ι]
         {F A : Type*}
         {k : ℕ}

/-- Affine line at origin `u`: `{u + α • v : α ∈ F}`, the line through `u` with direction `v`.
This definition is used in **Theorems 1.4, 4.1, 5.1, [BCIKS20]** and **Lemma 4.4, [AHIV22]**. -/
@[reducible]
def affineLineAtOrigin [Ring F] [AddCommGroup A] [Module F A] (origin direction : ι → A) :
    AffineSubspace F (ι → A) :=
    AffineSubspace.mk' (p := origin) (direction := Submodule.span F {direction})

omit [Fintype ι] in
lemma mem_affineLineAtOrigin_iff [Ring F] [AddCommGroup A] [Module F A] (origin direction : ι → A)
    (x : ι → A) : x ∈ affineLineAtOrigin (F := F) (origin := origin) (direction := direction)
    ↔ ∃ α : F, x = origin + α • direction := by
  rw [affineLineAtOrigin, AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_span_singleton]
  simp only [eq_sub_iff_add_eq, add_comm, eq_comm]

variable [DecidableEq F] [Ring F] [Fintype F]

/-- **Affine subspace from base origin and direction generators**.
Constructs the affine subspace `{origin + span{directions}}`.
Used in **Theorem 1.6, [BCIKS20]**. -/
@[reducible]
def affineSubspaceAtOrigin [AddCommGroup A] [DecidableEq A] [Module F A]
    (origin : ι → A) (directions : Fin k → ι → A) : AffineSubspace F (ι → A) :=
  AffineSubspace.mk' (p := origin) (direction := Submodule.span F (Finset.univ.image directions))

omit [DecidableEq F] [Ring F] [Fintype F] in
lemma mem_affineSubspaceFrom_iff [Ring F] [AddCommGroup A] [DecidableEq A] [Module F A]
    (origin : ι → A) (directions : Fin k → ι → A) (x : ι → A) :
    x ∈ affineSubspaceAtOrigin (F := F) (A := A) origin directions ↔
    ∃ β : Fin k → F, x = origin + ∑ i : Fin k, β i • directions i := by
  rw [affineSubspaceAtOrigin, AffineSubspace.mem_mk']
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [Submodule.mem_span_range_iff_exists_fun]
  conv_lhs => rw [vsub_eq_sub]; simp only [eq_sub_iff_add_eq]; simp only [add_comm, eq_comm]

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

/-- Affine subspace carriers are Fintype when the ambient space is Fintype -/
noncomputable instance instFintypeAffineSubspace {V : Type*} [AddCommGroup V]
    [Module F V] [Fintype V] (S : AffineSubspace F V) : Fintype S := Fintype.ofFinite S

/-- Affine subspaces constructed with mk' are always nonempty -/
instance instNonemptyAffineSubspace_mk' {V : Type*} [AddCommGroup V] [Module F V]
    (p : V) (direction : Submodule F V) : Nonempty (AffineSubspace.mk' p direction) :=
  nonempty_subtype.mpr ⟨p, AffineSubspace.self_mem_mk' p direction⟩

end
end Affine

namespace Curve

section

open Finset
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         -- For usage with linear code, we set A = F
         {F A : Type*} [Semiring F] [Fintype F]
         [AddCommMonoid A] [Module F A] [Fintype A] [DecidableEq A]

/-- **(Parameterised) polynomial curve, Thm 1.5, [BCIKS20]**:
Let `u := {u₀, ..., u_{k-1}}` be a collection of vectors with coefficients in a semiring.
The polynomial curve of degree `k-1` generated by `u` is the set of linear
combinations of the form `{∑ i ∈ k, r ^ i • u_i | r ∈ F}`. -/
@[reducible]
def polynomialCurve {k : ℕ} (u : Fin k → ι → A) : Set (ι → A)
  := {v | ∃ r : F, v = ∑ i : Fin k, (r ^ (i : ℕ)) • u i}

/-- A polynomial curve over a finite field, as a `Finset`. Requires `DecidableEq ι` and
  `DecidableEq F` to be able to construct the `Finset`. -/
def polynomialCurveFinite
  {k : ℕ} (u : Fin k → ι → A) : Finset (ι → A) :=
  {v | ∃ r : F, v = ∑ i : Fin k, (r ^ (i : ℕ)) • u i}

/-- A polynomial curve over a nonempty finite field contains at least one point. -/
instance [Nonempty F] {k : ℕ} :
  ∀ u : Fin k → ι → A, Nonempty {x // x ∈ polynomialCurveFinite (F := F) u } := by
  intro u
  unfold polynomialCurveFinite
  simp only [mem_filter, mem_univ, true_and, nonempty_subtype]
  have ⟨r⟩ := ‹Nonempty F›
  use ∑ i : Fin k, r ^ (i : ℕ) • u i, r

open Finset
instance {k : ℕ} {u : Fin k → ι → A} : Nonempty {x // x ∈ polynomialCurveFinite (F := F) u} := by
  simp [polynomialCurveFinite]

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
