/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Matrix.Mul
import ToMathlib.General

/-!
# Definitions and lemmas for `Vector`
-/

universe u

namespace Vector

-- TODO: deprecate `nil` and `cons`, and use existing `Vector` definitions (like `insertIdx`)

def nil {α} : Vector α 0 := ⟨#[], rfl⟩ -- Vector.emptyWithCapacity 0

def cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : Vector α (n + 1) :=
  tl.insertIdx 0 hd

@[simp]
theorem head_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : (cons hd tl).head = hd := by
  simp only [head, cons, insertIdx_zero, getElem_cast, zero_lt_one, getElem_append_left, getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero]

lemma cons_get_eq {α} {n : ℕ} (hd : α) (tl : Vector α n) (i : Fin (n + 1)) :
    (cons hd tl).get i =
      if hi: i.val == 0 then hd else tl.get (⟨i.val - 1, by
        simp only [beq_iff_eq, Fin.val_eq_zero_iff] at hi
        apply Nat.sub_lt_left_of_lt_add
        · by_contra hi_ne_gt_1
          simp only [not_le, Nat.lt_one_iff, Fin.val_eq_zero_iff] at hi_ne_gt_1
          contradiction
        · have hi_lt:= i.isLt; omega
      ⟩) := by
  if h_i_val: i.val = 0 then
    have h_i: i = 0 := by exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h_i_val)))
    subst h_i
    simp only [h_i_val, beq_iff_eq, ↓reduceDIte]
    simp only [cons, get, insertIdx] -- unfold everything
    simp only [Array.insertIdx_zero, Fin.coe_cast, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      List.size_toArray, List.length_cons, List.length_nil, _root_.zero_add, zero_lt_one,
      Array.getElem_append_left, List.getElem_toArray]
    rfl
  else
    simp only [h_i_val, beq_iff_eq, ↓reduceDIte]
    simp only [cons, get, insertIdx] -- unfold everything
    simp only [Array.insertIdx_zero, Fin.coe_cast, Fin.cast_mk, getElem_toArray]
    apply Array.getElem_append_right -- key counterpart for cons_get_eq in `Array` realm
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]
    omega

@[simp]
lemma cons_empty_tail_eq_nil {α} (hd : α) (tl : Vector α 0) :
    cons hd tl = ⟨#[hd], rfl⟩ := by
  apply Vector.toArray_inj.mp
  simp only [Nat.reduceAdd]
  rw [cons]
  simp only [insertIdx_size_self, toArray_push]
  have hl_toArray: tl.toArray = #[] := by
    simp only [toArray_eq_empty_iff]
  rw [hl_toArray]
  simp only [Array.push_empty]

@[simp]
theorem tail_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) : (cons hd tl).tail = tl := by
  rw [cons, Vector.insertIdx]
  simp only [Nat.add_one_sub_one, Array.insertIdx_zero, tail_eq_cast_extract, extract_mk,
    Array.extract_append, List.extract_toArray, List.extract_eq_drop_take, add_tsub_cancel_right,
    List.drop_succ_cons, List.drop_nil, List.take_nil, List.size_toArray, List.length_cons,
    List.length_nil, zero_add, tsub_self, Array.take_eq_extract, Array.empty_append, cast_mk, mk_eq,
    Array.extract_eq_self_iff, size_toArray, le_refl, and_self, or_true]

@[simp]
theorem cons_toList_eq_List_cons {α} {n : ℕ} (hd : α) (tl : Vector α n) :
    (cons hd tl).toList = hd :: tl.toList := by
  simp only [toList, cons, insertIdx]
  rw [Array.toList_insertIdx]
  simp only [List.insertIdx_zero]

-- TODO: this theorem should not be so hard...
theorem foldl_succ
 {α β} {n : ℕ} [NeZero n] (f : β → α → β) (init : β) (v : Vector α n) :
  v.foldl (f:=f) (b:=init) = v.tail.foldl (f:=f) (b:=f init v.head) := by
  simp_rw [Vector.foldl] -- get
  simp only [size_toArray]
  have hl_foldl_eq_toList_foldl := Array.foldl_toList (f:=f) (init:=init) (xs:=v.toArray)
  have hl_foldl_eq: Array.foldl f init v.toArray 0 n = Array.foldl f init v.toArray := by
    simp only [size_toArray]
  conv_lhs =>
    rw [hl_foldl_eq, hl_foldl_eq_toList_foldl.symm]
  have hr_foldl_eq_toList_foldl_tail := Array.foldl_toList (f:=f) (init:=f init v.head)
    (xs:=(v.tail.toArray))
  have hr_foldl_eq: Array.foldl f (f init v.head) v.tail.toArray 0 (n - 1)
    = Array.foldl f (f init v.head) v.tail.toArray := by
    simp only [size_toArray] -- Array.foldl_congr
  conv_rhs =>
    rw [hr_foldl_eq, hr_foldl_eq_toList_foldl_tail.symm]
  rw [Vector.head]
  have h_v_toList_length: 0 < v.toList.length := by
    simp only [length_toList]
    exact Nat.pos_of_neZero n
  rw [←Vector.getElem_toList (h:=h_v_toList_length)]
  have h_toList_eq: v.toArray.toList = v.toList := rfl
  rw [Vector.tail]
  simp only [toArray_cast, toArray_extract, Array.toList_extract, List.extract_eq_drop_take,
    List.drop_one]
  simp_rw [h_toList_eq]
  -- ⊢ List.foldl f init v.toList
  -- = List.foldl f (f init v.toList[0]) (List.take (n - 1) v.toList.tail)
  have hTakeTail: List.take (n - 1) v.toList.tail = v.toList.tail := by
    simp only [List.take_eq_self_iff, List.length_tail, length_toList, le_refl]
  rw [hTakeTail]
  have h_v_eq_cons: v.toList = v.head :: (v.toList.tail) := by
    cases h_list : v.toList with
    | nil =>
      have h_len : v.toList.length = 0 := by rw [h_list, List.length_nil]
      omega
    | cons hd tl =>
      have h_v_head: v.head = v.toList[0] := rfl
      simp_rw [h_v_head]
      have h_hd: hd = v.toList[0] := by simp only [h_list, List.getElem_cons_zero]
      simp only [List.tail_cons, List.cons.injEq, and_true]
      simp_rw [h_hd]
  conv_lhs => rw [h_v_eq_cons]
  rw [List.foldl_cons]
  rfl

theorem foldl_eq_toList_foldl {α β} {n : ℕ} (f : β → α → β) (init : β) (v : Vector α n) :
  v.foldl (f:=f) (b:=init) = v.toList.foldl (f:=f) (init:=init) := by
  rw [Vector.foldl]
  rw [←Array.foldl_toList]
  rfl

-- #eval cons (hd:=6) (tl:=⟨#[2, 3], rfl⟩)

theorem zipWith_cons {α β γ} {n : ℕ} (f : α → β → γ)
    (a : α) (b : Vector α n) (c : β) (d : Vector β n) :
    zipWith f (cons a b) (cons c d) = cons (f a c) (zipWith f b d) := by
  apply Vector.toList_inj.mp
  conv_lhs => simp only [toList_zipWith]
  simp_rw [cons_toList_eq_List_cons]
  rw [List.zipWith_cons_cons]
  conv_rhs => rw [toList_zipWith]

variable {R : Type*} {n : ℕ}

/-- Inner product between two vectors of the same size. Should be faster than `_root_.dotProduct`
    due to efficient operations on `Vector`s. -/
def dotProduct [Zero R] [Add R] [Mul R] (a b : Vector R n) : R :=
  a.zipWith (· * ·) b |>.foldl (· + ·) 0

@[inherit_doc]
scoped notation:80 a " *ᵥ " b => dotProduct a b

@[simp]
lemma dotProduct_cons [AddCommMonoid R] [Mul R] (a : R) (b : Vector R n) (c : R) (d : Vector R n) :
  dotProduct (cons a b) (cons c d) = a * c + dotProduct b d := by
  unfold dotProduct
  rw [zipWith_cons]
  simp_rw [foldl_eq_toList_foldl]
  rw [cons_toList_eq_List_cons]
  rw [List.foldl_eq_of_comm' (hf:=by exact fun a b c ↦ add_right_comm a b c)]
  rw [_root_.add_comm]

/-- A matrix represented as iterated vectors in row-major order.
`m` is the number of rows, and `n` is the number of columns -/
def Matrix (α : Type*) (m n : ℕ) := Vector (Vector α n) m

namespace Matrix

variable {α : Type*}

/- Note `Vector.flatten` converts a `Vector (m * n)` into a `Matrix α m n` -/

/-- Matrix-vector multiplication over `α`.
`M` is given as a vector of row-vectors. -/
def mulVec [Zero α] [Add α] [Mul α] {numRows numCols : Nat}
    (M : Vector (Vector α numCols) numRows)
    (x : Vector α numCols) : Vector α numRows :=
  M.map (fun row => row *ᵥ x)

/-- Convert a flat row-major vector of length `m*n` into an `m × n` row-major matrix
represented as `Vector (Vector α n) m`. -/
def ofFlatten {m n : ℕ} (v : Vector α (m * n)) : Matrix α m n :=
  (Vector.finRange m).map (fun i => (v.extract (i.val * n) (i.val * n + n)).cast
    (by
    -- Why can't `omega`, `aesop`, `grind`, etc. solve this?
      rcases i with ⟨i, h⟩
      have : i * n + n ≤ m * n := by
        calc
        _ = (i + 1) * n := by ring
        _ ≤ m * n := by gcongr; exact h
      simp [this]))

/-- Convert to a `Fin`-indexed matrix (the definition in Mathlib): `Fin m → Fin n → α` -/
def toFinMatrix {m n : ℕ} (matrix : Matrix α m n) : _root_.Matrix (Fin m) (Fin n) α :=
  fun i j => (matrix.get i).get j

/-- Convert from a `Fin`-indexed matrix (the definition in Mathlib): `Fin m → Fin n → α` -/
def ofFinMatrix {m n : ℕ} (matrix : _root_.Matrix (Fin m) (Fin n) α) : Matrix α m n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => matrix i j))

/-- Transpose a matrix by swapping rows and columns. -/
@[simp]
def transpose {m n : ℕ} (matrix : Matrix α m n) : Matrix α n m :=
  ofFn (fun j => ofFn (fun i => (matrix.get i).get j))

end Matrix

end Vector

section RootDotProduct

open Vector

variable {R : Type*} [AddCommMonoid R] [Mul R] {n : ℕ}

@[simp]
lemma dotProduct_cons (a : R) (b : Vector R n) (c : R) (d : Vector R n) :
    _root_.dotProduct (cons a b).get (cons c d).get = a * c + _root_.dotProduct b.get d.get := by
  unfold _root_.dotProduct
  if h_n: n = 0 then
    subst h_n
    simp only [cons_empty_tail_eq_nil]
    simp only [Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty, _root_.add_zero]
    rfl
  else
    -- ⊢ ∑ i, (cons a b).get i * (cons c d).get i = a * c + ∑ i, b.get i * d.get i
    rw [Fin.sum_univ_succ]
    rw [cons_get_eq, cons_get_eq]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, BEq.rfl, ↓reduceDIte]
    congr
    funext i
    simp_rw [cons_get_eq]
    simp only [Fin.val_succ, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceDIte,
      add_tsub_cancel_right, Fin.eta]

end RootDotProduct

namespace Vector

variable {R : Type*} [AddCommMonoid R] [Mul R] {n : ℕ}

theorem dotProduct_eq_root_dotProduct (a b : Vector R n) :
    dotProduct a b = _root_.dotProduct a.get b.get := by
  refine induction₂ ?_ (fun hd tl hd' tl' ih => ?_) a b
  · simp [dotProduct, _root_.dotProduct]
  · simp [Vector.cast]
    sorry
    -- suffices h : ((#v[hd] ++ tl) *ᵥ (#v[hd'] ++ tl')) =
    --   (_root_.dotProduct (#v[hd] ++ tl).get (#v[hd'] ++ tl').get) by
    --   simp at h
    --   sorry
    -- rw [dotProduct_cons]

end Vector
