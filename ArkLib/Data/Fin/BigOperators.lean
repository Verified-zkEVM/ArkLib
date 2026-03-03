/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

section FinHelpers
/-!

# More lemmas about Fin and big operators

- Fin lemmas (sum univ, equiv, reindex, etc)
- Matrix lemmas (from4Blocks, reindex, map, det, etc)
  + `Matrix.det_fromBlocks_of_commute`:
    given `Commute C D`, `(Matrix.fromBlocks A B C D).det = (A * D - B * C).det`
-/

@[simp]
def Fin.reindex {R n m : Type*} [Fintype n] [Fintype m] (e : n ≃ m) (v : n → R)
  : m → R := v ∘ e.symm

@[simp]
lemma Fin.reindex_reindex {R n m l : Type*} [Fintype n] [Fintype m] [Fintype l]
    (eₙ : n ≃ m) (eₘ : m ≃ l) (v : n → R) :
    (Fin.reindex (e := eₘ) (v := Fin.reindex eₙ v)) = Fin.reindex (e := eₙ.trans eₘ) (v := v) := by
  ext x
  simp only [reindex, Function.comp_apply, Equiv.symm_trans_apply]

@[simp]
lemma Fin.reindex_reindex_symm {R n m : Type*} [Fintype n] [Fintype m]
    (e : n ≃ m) (v : n → R) :
    (Fin.reindex (e := e.symm) (v := Fin.reindex e v)) = v := by
  rw [Fin.reindex_reindex, Equiv.self_trans_symm]; rfl

/-- The equivalence between the sum type `Fin (2^n) ⊕ Fin (2^n)`
    and `Fin (2^(n+1))`. -/
@[simp]
def finTwoPowSumEquiv (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  -- 1. Equivalence between Sum type and Fin (a + b)
  (finSumFinEquiv (m := 2 ^ n) (n := 2 ^ n)).trans
  -- 2. Cast based on the arithmetic equality 2^n + 2^n = 2^(n+1)
  (finCongr (by omega))

lemma finTwoPowSumEquiv_apply_left (n : ℕ) (x : Fin (2 ^ n)) :
  (finTwoPowSumEquiv n) (Sum.inl x) = Fin.castLT x (by omega) := by
  simp only [finTwoPowSumEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply]
  rfl

lemma finTwoPowSumEquiv_apply_right (n : ℕ) (x : Fin (2 ^ n)) :
  (finTwoPowSumEquiv n) (Sum.inr x) = ⟨x.val + 2 ^ n, by omega⟩ := by
  simp only [finTwoPowSumEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat,
    finCongr_apply]
  rfl

@[simp]
def finTwoPowAddTwoPowEquiv (n : ℕ) : Fin (2 ^ n + 2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  (finCongr (by omega))

/-- Helper to split a large vector into top/bottom halves using the equivalence. -/
@[simp]
def splitFinMap_PO2_left {L : Type*} {n : ℕ} (v : Fin (2 ^ (n + 1)) → L)
  : Fin (2 ^ n) → L := fun i => v ⟨i, by omega⟩

@[simp]
def splitFinMap_PO2_right {L : Type*} {n : ℕ} (v : Fin (2 ^ (n + 1)) → L)
  : Fin (2 ^ n) → L := fun i => v ⟨i + 2 ^ n, by omega⟩

@[simp]
def mergeFinMap_PO2_left_right {L : Type*} {n : ℕ} (left : Fin (2 ^ n) → L)
    (right : Fin (2 ^ n) → L) : Fin (2 ^ (n + 1)) → L := fun i =>
    if hi : i.val < 2 ^ n then left ⟨i, by omega⟩
    else right ⟨i - 2 ^ n, by omega⟩

lemma mergeFinMap_PO2_of_split_left_right {L : Type*} {n : ℕ} (v : Fin (2 ^ (n + 1)) → L) :
  v = mergeFinMap_PO2_left_right (left := splitFinMap_PO2_left v)
    (right := splitFinMap_PO2_right v) := by
  ext i
  simp only [mergeFinMap_PO2_left_right, splitFinMap_PO2_left, Fin.eta, splitFinMap_PO2_right,
    left_eq_dite_iff, not_lt]
  intro h
  congr 1; apply Fin.eq_of_val_eq; simp only; omega

lemma eq_split_finMap_PO2_iff_merge_finMap_PO2_eq {L : Type*} {n : ℕ} (v : Fin (2 ^ (n + 1)) → L)
  (left : Fin (2 ^ n) → L) (right : Fin (2 ^ n) → L) :
    left = splitFinMap_PO2_left v ∧ right = splitFinMap_PO2_right v
    ↔ mergeFinMap_PO2_left_right (left := left) (right := right) = v := by
  have hv_eq_merge_split : v = mergeFinMap_PO2_left_right (left := splitFinMap_PO2_left v)
    (right := splitFinMap_PO2_right v) := by
    exact mergeFinMap_PO2_of_split_left_right v
  constructor
  · intro hleft
    ext i
    simp only [mergeFinMap_PO2_left_right]
    by_cases hi : i.val < 2 ^ n
    · conv_rhs => rw [hv_eq_merge_split]; unfold mergeFinMap_PO2_left_right
      conv_lhs => rw [hleft.1]
      simp only [hi, ↓reduceDIte, splitFinMap_PO2_left, Fin.eta]
    · conv_rhs => rw [hv_eq_merge_split]; unfold mergeFinMap_PO2_left_right
      conv_lhs => rw [hleft.2]
      simp only [hi, ↓reduceDIte, splitFinMap_PO2_right]
  · intro hright
    rw [hv_eq_merge_split] at hright
    unfold mergeFinMap_PO2_left_right at hright
    simp only [splitFinMap_PO2_left, Fin.eta, splitFinMap_PO2_right] at hright
    constructor
    · -- ⊢ left = splitFinMap_PO2_left v
      ext (iLeft : Fin (2 ^ n))
      unfold splitFinMap_PO2_left
      rw [funext_iff] at hright
      let res := hright ⟨iLeft, by omega⟩
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at res
      exact res
    · -- ⊢ right = splitFinMap_PO2_right v
      ext (iRight : Fin (2 ^ n))
      unfold splitFinMap_PO2_right
      rw [funext_iff] at hright
      let res := hright ⟨iRight.val + 2 ^ n, by omega⟩
      simp only [add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, add_tsub_cancel_right,
        Fin.eta] at res
      exact res

/-- Helper to cast a vector from Sum index to Power-of-Two index. -/
@[simp]
def reindexVecTwoPowAddTwoPow {L : Type*} {n : ℕ} (v : Fin (2 ^ n + 2 ^ n) → L)
  : Fin (2 ^ (n+1)) → L := Fin.reindex (e := (finTwoPowAddTwoPowEquiv n)) (v := v)

end FinHelpers

section MatrixHelpers
/- Naming convention:
- `reindex` is used for reindexing a matrix or vector.
- `reindex_mulVec` is used for rw a mulVec between a reindexed-matrix and a vector.
- `vecMul_reindex` is used for rw a vecMul between a vector and a reindexed-matrix.
- `reindex_mul_eq_prod_of_reindex` is used for rw a reindexed matrix product
- `reindex_mulVec_reindex` is used for rw a mulVec between a reindexed-matrix and a
  reindexed-vector.
- `reindex_vecMul_reindex` is used for rw a vecMul between a reindexed-vector and a
  reindexed-matrix. -/

variable {R : Type*} [NonUnitalNonAssocSemiring R]
open Matrix

section MatrixReindexHelpers
/--
Moving reindexing from the Matrix to the Vector.
`(Reindex M) * v` is the same as `M * (v ∘ index_map)` (and then reindexing the result).
-/
@[simp]
lemma Matrix.reindex_mulVec {m n o l : Type*} [Fintype n] [Fintype l] [Fintype m] [Fintype o]
    (e_m : m ≃ o) (e_n : n ≃ l) (M : Matrix m n R) (v : l → R) :
    Matrix.reindex e_m e_n M *ᵥ v =
      Fin.reindex (e := by exact e_m) (v := (M *ᵥ (Fin.reindex (e_n.symm) v))) := by
  -- 1. Prove equality at every index `i`
  unfold Fin.reindex
  ext i
  -- 2. Unfold multiplication and reindexing definitions
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply,
             Matrix.submatrix_apply, Function.comp_apply]
  -- 3. The LHS is a sum over `l`. The RHS is a sum over `n`.
  --    Use the equivalence `e_n` to reindex the sum from `l` to `n`.
  rw [← Fintype.sum_equiv e_n]
  -- 4. Simplify `e_n.symm (e_n j)` to `j` inside the sum
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply, implies_true]

/-- Moving reindexing from the Vector to the Matrix.
`M *ᵥ (Reindex v)` is the same as `(Reindex M) *ᵥ v`. -/
@[simp]
lemma Matrix.mulVec_reindex {m n l : Type*} [Fintype n] [Fintype l]
    (e : l ≃ n) (M : Matrix m n R) (v : l → R) :
    M *ᵥ (Fin.reindex e v) = (Matrix.reindex (eₘ := Equiv.refl m) (eₙ := e.symm) M) *ᵥ v := by
  ext i
  -- 1. Unfold definitions
  simp only [mulVec, dotProduct, Fin.reindex, Function.comp_apply, reindex_apply, Equiv.refl_symm,
    Equiv.coe_refl, Equiv.symm_symm, submatrix_apply, id_eq]
  -- 2. Reindex the sum from `n` to `l` using `e`
  rw [Fintype.sum_equiv e]
  -- 3. Simplify: e.symm (e x) = x
  simp only [Equiv.symm_apply_apply, implies_true]

/--
Moving reindexing from the Matrix to the left-multiplying Vector.
`v *ᵥ (Reindex M)` is the same as `(v ∘ row_equiv) *ᵥ M` (and then reindexing the result).
-/
@[simp]
lemma Matrix.vecMul_reindex {m n o l : Type*} [Fintype m] [Fintype o] [Fintype n] [Fintype l]
    (e_m : m ≃ o) (e_n : n ≃ l) (v : o → R) (M : Matrix m n R) :
    Matrix.vecMul v (Matrix.reindex e_m e_n M) =
      Fin.reindex (e := e_n) (v := (Matrix.vecMul (Fin.reindex (e_m.symm) v) M)) := by
  -- 1. Prove equality at every column index `j` (in `l`)
  unfold Fin.reindex
  ext j
  -- 2. Unfold definitions
  simp only [Matrix.vecMul, _root_.dotProduct, Matrix.reindex_apply,
             Matrix.submatrix_apply, Function.comp_apply]
  -- 3. The sum is over `o` (the new rows). We reindex it to `m` (the old rows).
  --    We use `e_m` to map the summation domain.
  rw [← Fintype.sum_equiv e_m]
  -- 4. Simplify `e_m.symm (e_m k)` to `k`
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply, implies_true]

/-- Moving reindexing from the Vector to the Matrix (Row Vector case).
`(Reindex v) ᵥ* M` is the same as `v ᵥ* (Reindex M)`.
-/
@[simp]
lemma Matrix.reindex_vecMul {m n l : Type*} [Fintype m] [Fintype l]
    (e : l ≃ m) (v : l → R) (M : Matrix m n R) :
    (Fin.reindex e v) ᵥ* M = v ᵥ* (Matrix.reindex (eₘ := id e.symm) (eₙ := Equiv.refl n) M) := by
  ext j
  -- 1. Unfold definitions
  simp only [vecMul, dotProduct, Fin.reindex, Function.comp_apply, id_eq, reindex_apply,
    Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, submatrix_apply]
  -- 2. Reindex the sum from `m` to `l` using `e`
  rw [Fintype.sum_equiv e]
  -- 3. Simplify: e.symm (e x) = x
  simp only [Equiv.symm_apply_apply, implies_true]

@[simp]
lemma Matrix.reindex_mul_eq_prod_of_reindex {l m n o p q : Type*}
    [Fintype n] [Fintype p]
    (e_m : m ≃ o) (e_n : n ≃ p) (e_l : l ≃ q)
    (A : Matrix m n R) (B : Matrix n l R) :
    Matrix.reindex e_m e_l (A * B) =
    (Matrix.reindex e_m e_n A) * (Matrix.reindex e_n e_l B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [Fintype.sum_equiv e_n]
  simp only [Equiv.symm_apply_apply, implies_true]

/--
Cancellation: Multiplying a reindexed matrix by a reindexed vector.
The inner equivalence `e_n` cancels out, leaving a clean `M *ᵥ v` inside.
-/
@[simp]
lemma Matrix.reindex_mulVec_reindex {m n o l : Type*} [Fintype n] [Fintype l] [Fintype m]
    [Fintype o] (e_m : m ≃ o) (e_n : n ≃ l) (M : Matrix m n R) (v : n → R) :
    (Matrix.reindex e_m e_n M) *ᵥ (Fin.reindex (e_n) v) = Fin.reindex (e_m) (M *ᵥ v) := by
  rw [Matrix.reindex_mulVec]; unfold Fin.reindex
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]

/-- Cancellation: Multiplying two reindexed matrices cancels the inner equivalence.
(Reindex A) * (Reindex B) = Reindex (A * B) -/
@[simp]
lemma Matrix.reindex_mul_reindex {l m n o p q : Type*} [Fintype n] [Fintype p]
    (e_m : m ≃ o) (e_n : n ≃ p) (e_l : l ≃ q) (A : Matrix m n R) (B : Matrix n l R) :
    (Matrix.reindex e_m e_n A) * (Matrix.reindex e_n e_l B) = Matrix.reindex e_m e_l (A * B) := by
  exact Eq.symm (reindex_mul_eq_prod_of_reindex e_m e_n e_l A B)

/--
Cancellation: Multiplying a reindexed row vector by a reindexed matrix.
The inner equivalence `e_m` cancels out.
-/
@[simp]
lemma Matrix.reindex_vecMul_reindex {m n o l : Type*} [Fintype n] [Fintype l] [Fintype m]
    [Fintype o] (e_m : m ≃ o) (e_n : n ≃ l)
    (w : m → R) (M : Matrix m n R) :
    (Fin.reindex (e_m) w) ᵥ* (Matrix.reindex e_m e_n M) = Fin.reindex (e_n) (w ᵥ* M) := by
  rw [Matrix.vecMul_reindex]; unfold Fin.reindex
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]

end MatrixReindexHelpers
section MatrixFrom4BlocksHelpers
/-- Construct a matrix from 4 blocks [A B; C D] -/
def Matrix.from4Blocks {mTop nLeft mBot nRight : ℕ} {α : Type*}
  (A : Matrix (Fin mTop) (Fin nLeft) α) (B : Matrix (Fin mTop) (Fin nRight) α)
  (C : Matrix (Fin mBot) (Fin nLeft) α) (D : Matrix (Fin mBot) (Fin nRight) α) :
  Matrix (Fin (mTop + mBot)) (Fin (nLeft + nRight)) α := fun i j => by
  have isTop := i.val < mTop
  have isLeft := j.val < nLeft
  by_cases isTop : i.val < mTop
  · by_cases isLeft : j.val < nLeft
    · exact A ⟨i, by omega⟩ ⟨j, by omega⟩ -- top left block
    · exact B ⟨i, by omega⟩ ⟨j - nLeft, by omega⟩ -- top right block
  · by_cases isLeft : j.val < nLeft
    · exact C ⟨i - mTop, by omega⟩ ⟨j, by omega⟩ -- bottom left block
    · exact D ⟨i - mTop, by omega⟩ ⟨j - nLeft, by omega⟩ -- bottom right block

/-- Matrix.from4Blocks Matrix Multiplication Rule:
`[A B] * [E F] = [AE+BG  AF+BH]`
`[C D]   [G H]   [CE+DG  CF+DH]` -/
lemma Matrix.from4Blocks_mul_from4Blocks {mTop mBot pLeft pRight nLeft nRight : ℕ} {α : Type*}
    [NonUnitalNonAssocSemiring α]
    (A : Matrix (Fin mTop) (Fin pLeft) α) (B : Matrix (Fin mTop) (Fin pRight) α)
    (C : Matrix (Fin mBot) (Fin pLeft) α) (D : Matrix (Fin mBot) (Fin pRight) α)
    (E : Matrix (Fin pLeft) (Fin nLeft) α) (F : Matrix (Fin pLeft) (Fin nRight) α)
    (G : Matrix (Fin pRight) (Fin nLeft) α) (H : Matrix (Fin pRight) (Fin nRight) α) :
    (Matrix.from4Blocks A B C D) * (Matrix.from4Blocks E F G H) =
    Matrix.from4Blocks (A * E + B * G) (A * F + B * H)
                       (C * E + D * G) (C * F + D * H) := by
  -- 1. Prove equality at every index i, j
  ext i j
  -- 2. Unfold definitions
  simp only [Matrix.mul_apply, Matrix.from4Blocks, Matrix.add_apply]
  -- 3. Handle the splitting of the Summation index `k`
  -- The dot product sums over `Fin (pLeft + pRight)`. We split this into
  -- `0..pLeft-1` and `pLeft..pLeft+pRight-1`.
  conv_lhs => rw [Fin.sum_univ_add]
  -- 4. Split cases on Row `i` (Top vs Bottom)
  split_ifs with h_i_lt_mTop h_j_lt_nLeft
  · -- CASE: Top Row (i < mTop) and Left Column (j < nLeft)
    -- Simplify indices for A and B
    simp only [Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.val_natAdd,
      add_lt_iff_neg_left, not_lt_zero, add_tsub_cancel_left]
  · -- CASE: Bottom Row (i >= mTop) and Right Column (j ≥ nLeft)
    -- Logic is symmetric to above
    simp only [Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.val_natAdd,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left]
  · -- CASE: Bottom Row (i >= mTop) and Left Column (j < nLeft)
    simp only [Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.val_natAdd,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left]
  · -- CASE: Bottom Row (i >= mTop) and Right Column (j ≥ nLeft)
    simp only [Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.val_natAdd,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left]

/-- Helper: Link manual `from4Blocks` to Mathlib's `fromBlocks` via `finSumFinEquiv`.
    This allows us to reuse Mathlib's determinant theorems. -/
lemma Matrix.from4Blocks_eq_fromBlocks {m n : ℕ} {α : Type*}
    (A : Matrix (Fin m) (Fin m) α) (B : Matrix (Fin m) (Fin n) α)
    (C : Matrix (Fin n) (Fin m) α) (D : Matrix (Fin n) (Fin n) α) :
    Matrix.from4Blocks A B C D =
    Matrix.reindex (eₘ := finSumFinEquiv) (eₙ := finSumFinEquiv) (Matrix.fromBlocks A B C D) := by
  ext i j
  simp only [reindex_apply, submatrix_apply]
  -- Use the equivalence explicitly to simplify the goal state before cases
  let e := finSumFinEquiv (m := m) (n := n)
  -- Case analysis on the source indices in Sum (Fin m) (Fin n)
  -- We equate i to e(inl/inr) to resolve the from4Blocks if-statements
  cases hi : e.symm i with
  | inl i_top =>
    have h_e_itop: e (Sum.inl i_top) = ⟨i_top, by omega⟩ := by
      simp only [finSumFinEquiv_apply_left, Fin.castAdd, e, Fin.castLE]
    cases hj : e.symm j with
    | inl j_left =>
      have h_e_jleft: e (Sum.inl j_left) = ⟨j_left, by omega⟩ := by
        simp only [finSumFinEquiv_apply_left, Fin.castAdd, e, Fin.castLE]
      -- Case: Top-Left (A)
      -- Substitute i = e(inl i_top) and j = e(inl j_left)
      rw [← Equiv.eq_symm_apply] at hi hj
      rw [hi, hj]
      -- Simplify from4Blocks logic:
      -- 1. finSumFinEquiv (inl x) = castAdd x
      -- 2. castAdd x < m is true
      -- 3. fromBlocks (inl) (inl) = A
      simp only [from4Blocks, Equiv.symm_symm, fromBlocks, of_apply, Sum.elim_inl]
      simp only [h_e_itop, Fin.is_lt, ↓reduceDIte, h_e_jleft, Fin.eta]
    | inr j_right =>
      have h_e_jright: e (Sum.inr j_right) = ⟨j_right + m, by omega⟩ := by
        simp only [finSumFinEquiv_apply_right, Fin.natAdd, add_comm, e]
      -- Case: Top-Right (B)
      rw [← Equiv.eq_symm_apply] at hi hj
      rw [hi, hj]
      -- Simplify from4Blocks logic:
      -- 1. finSumFinEquiv (inr x) = natAdd m x
      -- 2. natAdd m x < m is false (it is ≥ m)
      -- 3. (m + x) - m = x
      simp only [from4Blocks, Equiv.symm_symm, fromBlocks, of_apply, Sum.elim_inl, Sum.elim_inr]
      simp only [h_e_itop, Fin.is_lt, ↓reduceDIte, h_e_jright, add_lt_iff_neg_right, not_lt_zero',
        Fin.eta, add_tsub_cancel_right]
  | inr i_bot =>
    have h_e_ibot: e (Sum.inr i_bot) = ⟨i_bot + m, by omega⟩ := by
      simp only [finSumFinEquiv_apply_right, Fin.natAdd, add_comm, e]
    cases hj : e.symm j with
    | inl j_left =>
      have h_e_jleft: e (Sum.inl j_left) = ⟨j_left, by omega⟩ := by
        simp only [finSumFinEquiv_apply_left, Fin.castAdd, e, Fin.castLE]
      -- Case: Bottom-Left (C)
      rw [← Equiv.eq_symm_apply] at hi hj
      rw [hi, hj]
      simp only [from4Blocks, Equiv.symm_symm, fromBlocks, of_apply, Sum.elim_inr, Sum.elim_inl]
      simp only [h_e_ibot, add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, h_e_jleft, Fin.is_lt,
        add_tsub_cancel_right, Fin.eta]
    | inr j_right =>
      have h_e_jright: e (Sum.inr j_right) = ⟨j_right + m, by omega⟩ := by
        simp only [finSumFinEquiv_apply_right, Fin.natAdd, add_comm, e]
      -- Case: Bottom-Right (D)
      rw [← Equiv.eq_symm_apply] at hi hj
      rw [hi, hj]
      simp only [from4Blocks, Equiv.symm_symm, fromBlocks, of_apply, Sum.elim_inr]
      simp only [h_e_ibot, add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, h_e_jright,
        add_tsub_cancel_right, Fin.eta]

/-- Determinant commutes with Ring Homomorphisms (avoids clash with Mathlib `Matrix.det_map`). -/
lemma Matrix.det_map_ringHom {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix n n R) :
    (M.map f).det = f M.det := by
  -- The determinant is a sum of products. Homomorphisms preserve sums and products.
  simp only [det_apply', map_apply, map_sum, map_mul, map_intCast, map_prod]

/-- Mapping a Ring Homomorphism over a negated matrix is the negation of the mapped matrix. -/
lemma Matrix.map_neg {m n : Type*} {R S : Type*} [Ring R] [Ring S]
    (M : Matrix m n R) (f : R →+* S) :
    (-M).map f = -(M.map f) := by
  ext i j
  -- definition of matrix negation and map
  simp only [Matrix.map_apply, Matrix.neg_apply]
  simp only [_root_.map_neg]

/-- The determinant of a 2x2 block matrix [A B; C D] where C and D commute is det(AD - BC).
    General version: Does NOT assume Invertible D. -/
lemma Matrix.det_fromBlocks_of_squareSubblocks_commute {n : ℕ} {R : Type*} [CommRing R]
    (A B C D : Matrix (Fin n) (Fin n) R) (h_comm : Commute C D) :
    (Matrix.fromBlocks A B C D).det = (A * D - B * C).det := by
  -- Define the polynomial ring P = R[X]
  let P := Polynomial R
  let X : P := Polynomial.X
  -- Lift matrices to P
  let A' := A.map (Polynomial.C : R →+* P)
  let B' := B.map (Polynomial.C : R →+* P)
  let C' := C.map (Polynomial.C : R →+* P)
  let D' := D.map (Polynomial.C : R →+* P)
  have h_mat_map_map_eq_self : ∀ (m n :ℕ) (a : Matrix (Fin m) (Fin n) R),
    (a.map ⇑Polynomial.C).map ⇑(Polynomial.evalRingHom 0) = a := by
    intro m n a
    ext i j
    simp only [Polynomial.coe_evalRingHom, map_apply, Polynomial.eval_C]
  -- Define the perturbed matrix D(X) = D + X•I
  let D_poly : Matrix (Fin n) (Fin n) P :=
    D' + X • (1 : Matrix (Fin n) (Fin n) P)
  -- 1. Establish that C' and D_poly commute
  have h_comm_poly : Commute C' D_poly := by
    -- C' commutes with D' (lifted from R) and with X•I (scalar matrix)
    apply Commute.add_right
    · -- ⊢ Commute C' D'
      unfold Commute SemiconjBy
      -- Move the map outside: A.map f * B.map f = (A * B).map f
      rw [← Matrix.map_mul, h_comm.eq, Matrix.map_mul]
    · -- ⊢ Commute C' (X • 1)
      -- Scalar matrices commute with everything.
      -- We prove it by simplifying M * (s • 1) -> s • M and (s • 1) * M -> s • M
      rw [Commute, SemiconjBy]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  -- 2. Construct the "Right-Multiplication" identity in P
  let M_poly := Matrix.fromBlocks A' B' C' D_poly
  let R_mat := Matrix.fromBlocks D_poly 0 (-C') (1 : Matrix (Fin n) (Fin n) P)
  let Res_mat := Matrix.fromBlocks (A' * D_poly - B' * C') B' 0 D_poly
  have h_mul : M_poly * R_mat = Res_mat := by
    -- 1. Apply our custom block multiplication rule
    rw [Matrix.fromBlocks_multiply]; unfold Res_mat
    simp only [mul_neg, mul_zero, mul_one, zero_add, fromBlocks_inj, and_true, true_and]
    -- 2. Simplify the block arithmetic
    -- ⊢ A' * D_poly + -(B' * C') = A' * D_poly - B' * C' ∧ C' * D_poly + -(D_poly * C') = 0
    constructor
    · congr
    · rw [← sub_eq_add_neg];
      rw [sub_eq_zero]
      exact h_comm_poly.eq
  -- 3. Take determinants
  apply_fun Matrix.det at h_mul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] at h_mul
  simp only [Matrix.det_one, mul_one] at h_mul
  -- 4. Cancel det(D_poly). It is a monic polynomial (up to sign), so not a zero divisor.
  have h_monic : (Matrix.det D_poly).Monic := by
  -- 1. Show D_poly is actually the characteristic matrix of (-D)
    --    Recall: charmatrix M = (X • I) - (M.map C)
    --    And D_poly = D' + X • I = (D.map C) + X • I
    have h_eq : D_poly = Matrix.charmatrix (-D) := by
      -- Unfold definitions to expose the arithmetic
      dsimp only [charmatrix, scalar_apply, RingHom.mapMatrix_apply]
      -- Simplify (-D).map C to -(D.map C)
      -- Now it matches D' + X • I
      rw [sub_eq_add_neg, add_comm]
      unfold D_poly
      congr
      · -- ⊢ D' = -(-D).map ⇑Polynomial.C
        rw [Matrix.map_neg (M := D) (f := Polynomial.C)]
        simp only [neg_neg]; rfl
      · rw [Matrix.smul_one_eq_diagonal]
    -- 2. Substitute and apply the standard theorem
    rw [h_eq]
    -- The determinant of the charmatrix IS the charpoly (by definition)
    -- So we just need to prove the charpoly is Monic.
    change (Matrix.charpoly (-D)).Monic
    exact Matrix.charpoly_monic (-D)
  have h_cancel : Matrix.det M_poly = Matrix.det (A' * D_poly - B' * C') := by
    -- Apply right-cancellation for Monic polynomials
    refine h_monic.isRegular.right ?_
    exact h_mul
  -- 5. Evaluate at X = 0 using the Ring Homomorphism explicitly
  --    Using 'evalRingHom' ensures the syntax matches 'Matrix.det_map'
  apply_fun (Polynomial.evalRingHom 0) at h_cancel
  -- Now use the helper (or RingHom.map_det) to move eval inside
  -- This turns `evalRingHom 0 (det M)` into `det (M.map (evalRingHom 0))`
  rw [← Matrix.det_map_ringHom (M := M_poly) (f := Polynomial.evalRingHom 0)] at h_cancel
  rw [← Matrix.det_map_ringHom (M := A' * D_poly - B' * C')
    (f := Polynomial.evalRingHom 0)] at h_cancel
  have h_X_smul_1_map : ((X : P) • (1 : Matrix (Fin n) (Fin n) P)).map
    ⇑(Polynomial.evalRingHom 0) = 0 := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (h := by
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_zero]),
      Polynomial.coe_evalRingHom, Polynomial.eval_X, diagonal_zero]
  -- 6. Prove the mapping equalities
  have h_eval_M : M_poly.map (Polynomial.evalRingHom 0) = Matrix.fromBlocks A B C D := by
    rw [Matrix.fromBlocks_map]
    unfold A' B' C' D_poly D'
    rw [Matrix.map_add (α := Polynomial R) (β := R) (hf := fun x y => by
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add])]
    rw [h_X_smul_1_map]
    simp_rw [h_mat_map_map_eq_self] -- A'.map (Polynomial.evalRingHom 0) = A
    rw [add_zero]
  have h_eval_Res : (A' * D_poly - B' * C').map (Polynomial.evalRingHom 0) = (A * D - B * C) := by
    -- Distribute eval over sub, mul, add
    simp only [A', B', C', D', D_poly]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_sub, implies_true, Matrix.map_sub]
      --   ⊢ (A.map ⇑Polynomial.C * (D.map ⇑Polynomial.C + X • 1)).map (Polynomial.eval 0) -
      --   (B.map ⇑Polynomial.C * C.map ⇑Polynomial.C).map (Polynomial.eval 0) =
      -- A * D - B * C
    rw [← Polynomial.coe_evalRingHom] -- `Bring back to RingHom for using Matrix.map_...`
    -- set f_polyR_to_R : Polynomial R →+* R := Polynomial.eval 0
    conv_lhs =>
      rw [Matrix.map_mul (α := Polynomial R) (β := R)]
      rw [Matrix.map_mul (α := Polynomial R) (β := R)]
      rw [Matrix.map_add (α := Polynomial R) (β := R) (hf := fun x y => by
        simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add])]
      rw [h_X_smul_1_map]
      rw [mul_add]
      simp only [h_mat_map_map_eq_self]
    simp only [mul_zero, add_zero]
  -- 7. Substitute and finish
  rw [h_eval_M, h_eval_Res] at h_cancel
  exact h_cancel

/-- The determinant of a 2x2 block matrix [A B; C D] where C and D commute is det(AD - BC). -/
lemma Matrix.det_from4Blocks_of_squareSubblocks_commute {n : ℕ} {R : Type*}
    [CommRing R] (A B C D : Matrix (Fin n) (Fin n) R) (h_comm : Commute C D) :
    Matrix.det (M := Matrix.from4Blocks A B C D) = Matrix.det (A * D - B * C) := by
  rw [Matrix.from4Blocks_eq_fromBlocks]
  rw [Matrix.det_reindex_self]
  exact Matrix.det_fromBlocks_of_squareSubblocks_commute A B C D h_comm

-- TODO: Matrix.from4Blocks_mulVec_finMap_PO2_left_right

end MatrixFrom4BlocksHelpers

end MatrixHelpers
