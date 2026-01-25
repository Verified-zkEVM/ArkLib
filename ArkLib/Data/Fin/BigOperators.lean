/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import ArkLib.Data.Fin.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!

# More lemmas about Fin and big operators

- Fin lemmas (sum univ, equiv, reindex, etc)
- Matrix lemmas (from4Blocks, reindex, map, det, etc)
  + `Matrix.det_fromBlocks_of_commute`:
    given `Commute C D`, `(Matrix.fromBlocks A B C D).det = (A * D - B * C).det`
-/

section NatHelpers

theorem mul_two_add_bit_lt_two_pow (a b c : ℕ) (i : Fin 2)
    (h_a : a < 2 ^ b) (h_b : b < c) :
    a * 2 + i.val < 2^c := by
  if h_b_eq_0: b = 0 then
    rw [h_b_eq_0, pow_zero] at h_a
    interval_cases a
    · simp only [zero_mul, zero_add];
      have h_c_gt_0: c > 0 := by omega
      have h_i_lt_2_pow_c: i.val < 2^c := by
        calc
          _ ≤ 2^1 := by omega
          _ ≤ 2^c := by apply pow_le_pow_right' (by omega) (by omega)
      exact h_i_lt_2_pow_c
  else
    have h_le: 2^(b+1) ≤ 2^c := by
      rw [pow_le_pow_iff_right₀ (a:=2) (n:=b+1) (m:=c) (by omega)]
      omega
    have h_a_mul_2_add_i_lt_2_pow_c: a * 2 + i ≤ 2^c - 1 := by
      calc
        _ ≤ 2^(b+1) - 1 := by omega
        _ ≤ 2^c - 1 := by omega
    exact Nat.lt_of_le_sub_one (n:=a * 2 + i) (m:=2^c) (by omega) (h_a_mul_2_add_i_lt_2_pow_c)

theorem div_two_pow_lt_two_pow (x i j : ℕ) (h_x_lt_2_pow_i : x < 2 ^ (i + j)): x / 2^j < 2^(i) := by
  by_cases h_i_eq_0: i = 0
  · simp only [h_i_eq_0, zero_add, pow_zero, Nat.lt_one_iff, Nat.div_eq_zero_iff, Nat.pow_eq_zero,
    OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at *;
    omega
  · push_neg at h_i_eq_0
    apply Nat.div_lt_of_lt_mul (m:=x) (n:=2^j) (k:=2^i) (by
      have h_rhs_eq : 2^(i+j) = 2^j * 2^i := by
        rw [pow_add (a:=2) (m:=i) (n:=j), mul_comm]
      rw [h_rhs_eq.symm]
      omega
    )

lemma lt_two_pow_of_lt_two_pow_exp_le (x i j: ℕ)
    (h_x_lt_2_pow_i: x < 2^i) (h_i_le_j: i ≤ j): x < 2^j := by
  calc
    _ < 2^i := by omega
    _ ≤ 2^j := by apply pow_le_pow_right' (by omega) (by omega)
end NatHelpers

section FinHelpers
variable {r : ℕ} [NeZero r]

lemma Fin.val_add_one' (a : Fin r) (h_a_add_1 : a + 1 < r) : (a + 1).val = a.val + 1 := by
  rw [←Nat.mod_eq_of_lt (a := 1) (b := r) (by omega)] -- ⊢ ↑(b + 1) = ↑b + 1 % r
  apply Fin.val_add_eq_of_add_lt -- ⊢ ↑b + ↑1 < r
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  exact h_a_add_1

@[simp]
theorem Fin.cast_val_eq_val {n m : ℕ} [NeZero n] (a : Fin n) (h_eq : n = m):
  (Fin.cast (h_eq) a).val = a.val := by
  subst h_eq
  rfl

lemma Fin.val_sub_one (a : Fin r) (h_a_sub_1 : a > 0) : (a - 1).val = a.val - 1 := by
  rw [Fin.val_sub_one_of_ne_zero (by omega)] -- can use Fin.sub_val_of_le

lemma Fin.lt_iff_le_pred (a b : Fin r) (h_b : b > 0) : a < b ↔ a ≤ b - 1 := by
  have h_b_sub_1 : (b - 1).val = b.val - 1 := Fin.val_sub_one (a := b) (h_a_sub_1 := h_b)
  constructor
  · intro h
    apply Fin.mk_le_of_le_val
    omega
  · intro h
    apply Fin.mk_lt_of_lt_val
    omega

lemma Fin.le_iff_lt_succ (a b : Fin r) (h_b : b + 1 < r) : a ≤ b ↔ a < b + 1 := by
  have h_b_add_1 := Fin.val_add_one' (a := b) (h_a_add_1 := h_b)
  constructor
  · intro h
    apply Fin.mk_lt_of_lt_val
    omega
  · intro h
    apply Fin.mk_le_of_le_val
    omega

lemma Fin.lt_succ' (a : Fin r) (h_a_add_1 : a + 1 < r) : a < a + 1 := by
  apply Fin.mk_lt_of_lt_val
  rw [Fin.val_add_one' (a := a) (h_a_add_1 := h_a_add_1)]
  exact Nat.lt_succ_self a.val

lemma Fin.le_succ (a : Fin r) (h_a_add_1 : a + 1 < r) : a ≤ a + 1 := by
  apply Fin.le_of_lt
  exact Fin.lt_succ' (a := a) (h_a_add_1 := h_a_add_1)

@[elab_as_elim] def Fin.succRecOnSameFinType {motive : Fin r → Sort _}
    (zero : motive (0 : Fin r))
    (succ : ∀ i : Fin r, i + 1 < r → motive i → motive (i + 1)) : ∀ (i : Fin r), motive i
  | ⟨0, _⟩ => by exact zero
  | ⟨Nat.succ i_val, h⟩ => by -- ⊢ motive ⟨i_val.succ, h⟩
    simp only [Nat.succ_eq_add_one] at h
    set i : Fin r := ⟨i_val, by omega⟩
    set i_succ : Fin r := ⟨i_val.succ, by omega⟩
    have i_succ_val_eq : i_succ.val = i_val.succ := by rfl
    if h_i_add_1 : i + 1 < r then -- ⊢ motive ⟨i.succ, h⟩
      have motive_prev : motive i := Fin.succRecOnSameFinType zero succ i
      have res := succ (i := i) h_i_add_1 motive_prev
      have h_i_succ_eq : i_succ = i + 1 := by
        rw [Fin.eq_mk_iff_val_eq]
        rw [i_succ_val_eq]
        rw [Fin.val_add_one']
        omega
      rw [h_i_succ_eq]
      exact res
    else
      by_contra h_i_add_1
      simp only at h_i_add_1
      contradiction

@[elab_as_elim] def Fin.predRecOnSameFinType {motive : Fin r → Sort _}
    (last : motive (⟨r - 1, by
      have h_r_ne_0: r ≠ 0 := by exact NeZero.ne r
      omega
    ⟩ : Fin r))
    (succ : ∀ i : Fin r, i.val > 0 → motive i → motive (⟨i.val - 1, by omega⟩ : Fin r))
    (i : Fin r): motive i := by
  have h_r_ne_0: r ≠ 0 := by exact NeZero.ne r
  if h_i_eq_last: i = ⟨r - 1, by omega⟩ then
    subst h_i_eq_last
    exact last
  else
    have h_i_ne_last: i < ⟨r - 1, by omega⟩ := by
      have h := Fin.lt_last_iff_ne_last (n:=r - 1) (a:=⟨i, by omega⟩)
      simp only [Fin.last, mk_lt_mk, ne_eq, mk.injEq] at h
      have h_i_val_ne_eq: (i.val ≠ r - 1) := by
        push_neg at h_i_eq_last
        exact Fin.val_ne_of_ne h_i_eq_last
      apply Fin.mk_lt_of_lt_val
      apply h.mpr
      exact h_i_val_ne_eq
    -- succ : (i : Fin r) → ↑i - 1 ≥ 0 → motive i → motive ⟨↑i - 1, ⋯⟩
    let i_next := i.val + 1
    have h_i_next_gt_0 : i_next > 0 := by omega
    have h_i_next_sub_one: i_next - 1 = i.val := by omega
    have motive_next := Fin.predRecOnSameFinType last succ ⟨i_next, by omega⟩
    have motive_next_ind := succ (i := ⟨i_next, by omega⟩) (by omega) (motive_next)
    convert motive_next_ind
termination_by (r - 1 - i.val)

-- The theorem statement and its proof.
-- TODO: state a more generalized and reusable version of this, where f is from Fin r → M
theorem Fin.sum_univ_odd_even {n : ℕ} {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ i : Fin (2 ^ n), f (2 * i)) + (∑ i : Fin (2 ^ n), f (2 * i + 1))
    = ∑ i: Fin (2 ^ (n+1)), f i := by
  set f_even := fun i => f (2 * i)
  set f_odd := fun i => f (2 * i + 1)
  conv_lhs =>
    enter [1, 2, i]
    change f_even i
  conv_lhs =>
    enter [2, 2, i]
    change f_odd i
  simp only [Fin.sum_univ_eq_sum_range]

  -- Let's define the sets of even and odd numbers.
  let evens: Finset ℕ := Finset.image (fun i ↦ 2 * i) (Finset.range (2^n))
  let odds: Finset ℕ := Finset.image (fun i ↦ 2 * i + 1) (Finset.range (2^n))

  conv_lhs =>
    enter [1];
    rw [←Finset.sum_image (g:=fun i => 2 * i) (by simp)]

  conv_lhs =>
    enter [2];
    rw [← Finset.sum_image (g:=fun i => 2 * i + 1) (by simp)]

  -- First, we prove that the set on the RHS is the disjoint union of evens and odds.
  have h_disjoint : Disjoint evens odds := by
    apply Finset.disjoint_iff_ne.mpr
  -- Assume for contradiction that an element `x` is in both sets.
    rintro x hx y hy hxy
    -- Unpack the definitions of `evens` and `odds`.
    rcases Finset.mem_image.mp hx with ⟨k₁, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨k₂, _, rfl⟩
    omega

  have h_union : evens ∪ odds = Finset.range (2 ^ (n + 1)) := by
    apply Finset.ext; intro x
    simp only [Finset.mem_union, Finset.mem_range]
    -- ⊢ x ∈ evens ∨ x ∈ odds ↔ x < 2 ^ (n + 1)
    constructor
    · -- First direction: `x ∈ evens ∪ odds → x < 2^(n+1)`
      -- This follows from the bounds of the original range `Finset.range (2^n)`.
      intro h
      rcases h with (h_even | h_odd)
      · rcases Finset.mem_image.mp h_even with ⟨k₁, hk₁, rfl⟩
        simp at hk₁
        omega
      · rcases Finset.mem_image.mp h_odd with ⟨k₂, hk₂, rfl⟩
        simp at hk₂
        omega
    · -- Second direction: `x < 2^(n+1) → x ∈ evens ∪ odds`
      intro hx
      obtain (⟨k, rfl⟩ | ⟨k, rfl⟩) := Nat.even_or_odd x
      · left;
        unfold evens
        simp only [Finset.mem_image, Finset.mem_range]
        use k;
        omega
      · right;
        unfold odds
        simp only [Finset.mem_image, Finset.mem_range]
        use k;
        omega
  -- Now, rewrite the RHS using this partition.
  rw [←h_union, Finset.sum_union h_disjoint]

theorem sum_Icc_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b c : ℕ)
    (h₁ : a ≤ b) (h₂ : b ≤ c) :
    ∑ i ∈ Finset.Icc a c, f i = ∑ i ∈ Finset.Icc a b, f i + ∑ i ∈ Finset.Icc (b+1) c, f i := by
  have h_disjoint: Disjoint (Finset.Icc a b) (Finset.Icc (b+1) c) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    -- main theorem for converting disjoint condition into intersection = ∅ condition
    ext i
    simp only [Finset.mem_inter, Finset.mem_Icc]
    constructor
    · intro h
      -- Alternatively, we can use a single line: linarith [h.1.2, h.2.1]
      have h_le_b : i ≤ b := h.1.2
      have h_ge_b_plus_1 : b + 1 ≤ i := h.2.1
      have h_contradiction : b + 1 ≤ b := le_trans h_ge_b_plus_1 h_le_b
      have h_false : b < b := Nat.lt_of_succ_le h_contradiction
      exact absurd h_false (lt_irrefl b)
    · intro h -- h : i ∈ ∅
      exact absurd h (Finset.notMem_empty i)

  rw [←Finset.sum_union h_disjoint]
  · congr
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · intro h
      -- h : a ≤ j ∧ j ≤ c
      cases Nat.lt_or_ge j (b+1) with
      | inl h_lt => -- j < (b+1)
        left -- pick the left branch, for OR statement
        exact ⟨h.1, Nat.le_of_lt_succ h_lt⟩
      | inr h_ge => -- b + 1 ≤ j
        right
        exact ⟨h_ge, h.2⟩
    · intro h
      -- h : a ≤ j ∧ j ≤ b ∨ b + 1 ≤ j ∧ j ≤ c
      cases h with
      | inl h_left =>
        -- h_left : a ≤ j ∧ j ≤ b
        exact ⟨h_left.1, Nat.le_trans h_left.2 h₂⟩
      | inr h_right =>
        -- h_right : b + 1 ≤ j ∧ j ≤ c
        exact ⟨Nat.le_trans h₁ (Nat.le_of_succ_le h_right.1), h_right.2⟩

def equivFinFunSplitLast {F : Type*} [Fintype F] [Nonempty F] {ϑ : ℕ} :
    (Fin (ϑ + 1) → F) ≃ (F × (Fin ϑ → F)) where
  toFun := fun r => (r (Fin.last ϑ), Fin.init r)
  invFun := fun (r_last, r_init) => Fin.snoc r_init r_last
  left_inv := by
    simp only
    intro r
    ext i
    simp only [Fin.snoc_init_self]
  right_inv := by
    simp only
    intro (r_last, r_init)
    ext i
    · simp only [Fin.snoc_last]
    · simp only [Fin.init_snoc]

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
    if hi: i.val < 2 ^ n then left ⟨i, by omega⟩
    else right ⟨i - 2 ^ n, by omega⟩

lemma mergeFinMap_PO2_of_split_left_right {L : Type*} {n : ℕ} (v : Fin (2 ^ (n + 1)) → L) :
  v = mergeFinMap_PO2_left_right (left := splitFinMap_PO2_left v)
    (right := splitFinMap_PO2_right v) := by
  ext i
  simp only [mergeFinMap_PO2_left_right, splitFinMap_PO2_left, Fin.eta, splitFinMap_PO2_right,
    left_eq_dite_iff, not_lt]
  intro h
  rw! [Nat.sub_add_cancel]
  exact h

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
      Fin.reindex (e := by exact e_m) (v := (M *ᵥ (Fin.reindex (e_n.symm) v))):= by
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

/--
Moving reindexing from the Vector to the Matrix.
`M *ᵥ (Reindex v)` is the same as `(Reindex M) *ᵥ v`.
-/
@[simp]
lemma Matrix.mulVec_reindex {m n l : Type*} [Fintype n] [Fintype l] [Fintype m]
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

/--
Moving reindexing from the Vector to the Matrix (Row Vector case).
`(Reindex v) ᵥ* M` is the same as `v ᵥ* (Reindex M)`.
-/
@[simp]
lemma Matrix.reindex_vecMul {m n l : Type*} [Fintype m] [Fintype l] [Fintype n]
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
    simp only [Fin.coe_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.coe_natAdd,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left]
  · -- CASE: Bottom Row (i >= mTop) and Right Column (j ≥ nLeft)
    -- Logic is symmetric to above
    simp only [Fin.coe_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.coe_natAdd,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left]
  · -- CASE: Bottom Row (i >= mTop) and Left Column (j < nLeft)
    simp only [Fin.coe_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.coe_natAdd,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left]
  · -- CASE: Bottom Row (i >= mTop) and Right Column (j ≥ nLeft)
    simp only [Fin.coe_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.coe_natAdd,
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

/-- Helper: Determinant commutes with Ring Homomorphisms -/
lemma Matrix.det_map {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*}
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
  rw [← Matrix.det_map (M := M_poly) (f := Polynomial.evalRingHom 0)] at h_cancel
  rw [← Matrix.det_map (M := A' * D_poly - B' * C') (f := Polynomial.evalRingHom 0)] at h_cancel

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
