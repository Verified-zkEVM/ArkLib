/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Tuple.Notation
import Mathlib.Data.List.DropRight

/-!
# Lemmas for Take and Drop for `Fin` tuples

This file contains some properties of `Fin.{r}take` and `Fin.{r}drop`, which are already defined in
`ArkLib.Data.Fin.Tuple.Defs` (except `Fin.take` which is already in mathlib).
-/

universe u v

lemma eqRec_fun_eq_eqRec_sort {α : Sort*} {β : α → Sort u} {a a' : α}
    (h : a = a') (h' : β a = β a') (b : β a) :
  h ▸ b = h' ▸ b := by
  subst h; rfl

lemma eqRec_fun_eqRec_sort_eq_self {α : Sort*} {β : α → Sort u} {a a' : α}
    (h : a = a') (h' : β a = β a') (b : β a) :
  b = h ▸ h' ▸ b := by
  subst h; rfl

lemma eqRec_sort_eqRec_fun_eq_self {α : Sort*} {β : α → Sort u} {a a' : α}
    (h : a = a') (h' : β a = β a') (b : β a) :
  b = h' ▸ h ▸ b := by
  subst h; rfl

open Function

namespace Fin

variable {n : ℕ} {α : Fin n → Sort u}

theorem take_addCases'_left {n' : ℕ} {β : Fin n' → Sort u} (m : ℕ) (h : m ≤ n)
    (u : (i : Fin n) → α i) (v : (j : Fin n') → β j) (i : Fin m) :
    take m (Nat.le_add_right_of_le h) (addCases' u v) i =
      (append_left α β (castLE h i)) ▸ (take m h u i) := by
  have : i < n := Nat.lt_of_lt_of_le i.isLt h
  simp [take_apply, addCases', addCases, this, cast_eq_iff_heq, castLE]

-- theorem take_addCases'_right {n' : ℕ} {β : Fin n' → Sort u} (m : ℕ) (h : m ≤ n')
--     (u : (i : Fin n) → α i) (v : (j : Fin n') → β j) (i : Fin (n + m)) :
--       take (n + m) (Nat.add_le_add_left h n) (addCases' u v) i =
--         addCases' u (take m h v) i := by
--   have : i < n := Nat.lt_of_lt_of_le i.isLt h
--   simp [take_apply, addCases', addCases, this, cast_eq_iff_heq, castLT, castLE]
--   have {i : Fin m} : castLE (Nat.le_add_right_of_le h) i = natAdd n (castLE h i) := by congr
--   refine (Fin.heq_fun_iff' rfl (fun i => ?_)).mpr (fun i => ?_)
--   · sorry
--     simp only [append_right, cast_eq_self]
--   · rw [take, this]
--     simp [addCases_right]

@[simp]
theorem rtake_apply (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n)
    (i : Fin m) : rtake m h v i = v (Fin.cast (Nat.sub_add_cancel h) (natAdd (n - m) i)) := rfl

@[simp]
theorem rtake_zero (v : (i : Fin n) → α i) :
    rtake 0 (by omega) v = fun i => Fin.elim0 i := by ext i; exact Fin.elim0 i

@[simp]
theorem rtake_self (v : (i : Fin n) → α i) :
    rtake n (by omega) v = fun i : Fin n => dcast (by simp [Fin.cast]) (v i) := by
  ext i
  simp [rtake, Fin.natAdd, dcast, cast]
  rw! [Nat.sub_self, Nat.zero_add]

@[simp]
theorem rtake_self' {α : Sort*} (v : Fin n → α) : rtake n (by omega) v = v :=
  rtake_self v

-- @[simp]
-- theorem rtake_succ_eq_cons (m : ℕ) (h : m < n) (v : (i : Fin n) → α i) :
--     rtake (m + 1) (Nat.le_add_right_of_le h) v =
--       cons (v ⟨m, by omega⟩) (rtake m h v) := by
--   ext i <;> simp [rtake, Fin.natAdd, cons]
--   · unfold rtake
--     simp [Fin.cast]

/-- Taking `m` elements from the end of a tuple is the same as taking the first `m` elements of the
tuple in reverse, and then reversing the result. -/
theorem rtake_eq_take_rev {α : Sort*} (m : ℕ) (h : m ≤ n) (v : Fin n → α) :
    rtake m h v = (take m h (v ∘ Fin.rev)) ∘ Fin.rev := by
  ext i
  simp only [rtake, Fin.cast, natAdd, comp_apply, take, rev, castLE_mk]
  congr; omega

/-- Taking `m` elements from the end of a tuple and then reversing the result is the same as taking
the first `m` elements of the tuple in reverse. -/
theorem rtake_rev_eq_take_of_rev {α : Sort*} (m : ℕ) (h : m ≤ n) (v : Fin n → α) :
    rtake m h v ∘ Fin.rev = (take m h (v ∘ Fin.rev)) := by
  ext i
  simp only [rtake, Fin.cast, natAdd, comp_apply, take, rev, castLE]
  congr; omega

/-- The concatenation of the first `m` elements and the last `n - m` elements of a tuple is the
same as the original tuple. -/
@[simp]
theorem take_rtake_append {α : Sort*} (m : ℕ) (h : m ≤ n) (v : Fin n → α) :
    Fin.append (take m h v) (rtake (n - m) (by omega) v) = fun i => v (i.cast (by omega))  := by
  ext i
  simp [append, addCases, Fin.cast, castLE]
  split
  · simp
  · have : n - (n - m) + (i.val - m) = i.val := by omega
    simp [this]

/-- `Fin.rtake` intertwines with `List.rtake` via `List.ofFn`. -/
theorem ofFn_rtake_eq_rtake_ofFn {α : Type*} {m : ℕ} (h : m ≤ n) (v : Fin n → α) :
    List.ofFn (rtake m h v) = (List.ofFn v).rtake m := by
  ext i a
  simp [List.rtake, natAdd, Fin.cast]
  constructor <;> intro ⟨hi, ha⟩ <;> refine ⟨by omega, ?_⟩ <;> rw! [ha]

/-- Alternative version of `ofFn_rtake_eq_rtake_ofFn` with `l : List α` instead of `v : Fin n → α`.
-/
theorem ofFn_rtake_get {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    List.ofFn (rtake m h l.get) = l.rtake m := by
  ext i a
  simp [List.rtake, natAdd, Fin.cast, List.getElem?_eq_some_iff]
  constructor <;> intro ⟨hi, ha⟩ <;> refine ⟨by omega, ?_⟩ <;> rw! [ha]

/-- `Fin.rtake` intertwines with `List.rtake` via `List.get`. -/
theorem get_rtake_eq_rtake_get_comp_cast {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    (l.rtake m).get = rtake m h l.get ∘ Fin.cast (by simp [List.rtake]; omega) := by
  ext i
  simp [List.rtake, natAdd, Fin.cast]

/-- Alternative version with `v : Fin n → α` instead of `l : List α`. -/
theorem get_rtake_ofFn_eq_rtake_comp_cast {α : Type*} {m : ℕ} (v : Fin n → α) (h : m ≤ n) :
    ((List.ofFn v).rtake m).get =
      rtake m h v ∘ Fin.cast (by simp [List.rtake]; omega) := by
  ext i
  simp [List.rtake, natAdd, Fin.cast]

/-
* `Fin.drop`: Given `h : m ≤ n`, `Fin.drop m h v` for a `n`-tuple `v = (v 0, ..., v (n - 1))` is the
  `(n - m)`-tuple `(v m, ..., v (n - 1))`.
-/
section Drop

@[simp]
theorem drop_apply (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin (n - m)) :
    (drop m h v) i = v (Fin.cast (Nat.sub_add_cancel h) (addNat i m)) := rfl

@[simp]
theorem drop_zero (v : (i : Fin n) → α i) : drop 0 n.zero_le v = v := by
  ext i
  simp only [Nat.sub_zero, Nat.add_zero, addNat, Fin.eta, cast_eq_self, drop_apply]

@[simp]
theorem drop_one {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    drop 1 (Nat.le_add_left 1 n) v = tail v := by
  ext i
  simp only [drop, tail]
  congr

@[simp]
theorem drop_of_succ {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    drop n n.le_succ v = fun i => v (Fin.cast (Nat.sub_add_cancel n.le_succ) (addNat i n)) := by
  ext i
  simp only [drop]

@[simp]
theorem drop_all (v : (i : Fin n) → α i) :
    drop n n.le_refl v = fun i => Fin.elim0 (i.cast (Nat.sub_self n)) := by
  ext i
  simp at i
  exact Fin.elim0 i

theorem drop_tail {α : Fin (n + 1) → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin (n + 1)) → α i) :
    (drop m h (tail v)) =
      fun i => dcast (by simp [Fin.cast, add_assoc])
        (drop m.succ (Nat.succ_le_succ h) v (i.cast (by omega))) := by
  ext i
  simp [tail, Fin.cast]
  rw! [add_assoc]

theorem drop_repeat {α : Type*} {n' : ℕ} (m : ℕ) (h : m ≤ n) (a : Fin n' → α) :
    drop (m * n') (Nat.mul_le_mul_right n' h) (Fin.repeat n a) =
      fun i : Fin (n * n' - m * n') =>
          (Fin.repeat (n - m) a (i.cast (Nat.sub_mul n m n').symm)) := by
  ext i
  simp [Fin.cast, modNat]

/-- Dropping twice equals drop once with the sum, up to casting -/
@[simp]
theorem drop_drop {m m' : ℕ} (h : m ≤ n - m') (h' : m' ≤ n) (v : (i : Fin n) → α i) :
    drop m h (drop m' h' v) =
      (fun i =>
        letI := drop (m + m') (Nat.add_le_of_le_sub h' h) v (i.cast (by omega))
        dcast (by simp [Fin.cast, add_assoc]) this) := by
  ext i
  simp only [Fin.cast, coe_addNat, addNat_mk, cast_mk, drop_apply]
  rw! [add_assoc]; simp

/-- `drop` is unchanged after `update` for indices before the drop point. -/
@[simp]
theorem drop_update_of_lt (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin n)
    (hi : i < m) (x : α i) : drop m h (update v i x) = drop m h v := by
  ext j
  simp only [Fin.cast, coe_addNat, drop_apply, update, dite_eq_right_iff]
  intro h'
  subst h'
  simp_all only [add_lt_iff_neg_right, not_lt_zero']

/-- `drop` commutes with `update` for indices at or after the drop point. -/
@[simp]
theorem drop_update_of_ge (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin n) (hi : i ≥ m)
    (x : α i) : drop m h (update v i x) =
      update (drop m h v) ⟨i - m, by omega⟩
        (dcast (by simp; ext; simp; rw [Nat.sub_add_cancel hi]) x) := by
  ext j
  simp [update, Fin.cast]
  split
  next h_1 =>
    subst h_1
    simp_all only [add_tsub_cancel_right, Fin.eta, ↓reduceDIte]
    simp [dcast, cast]
    sorry
  next h_1 =>
    simp_all only [right_eq_dite_iff]
    intro h_2
    subst h_2
    simp_all only [Nat.sub_add_cancel, Fin.eta, not_true_eq_false]

-- /-- Dropping the first `m ≤ n` elements of an `addCases u v`, where `u` is a `n`-tuple,
-- is the same as dropping the first `m` elements of `u` and then adding `v` to the result. -/
-- theorem drop_addCases_left {n' : ℕ} {motive : Fin (n + n') → Sort*} (m : ℕ) (h : m ≤ n)
--     (u : (i : Fin n) → motive (castAdd n' i)) (v : (i : Fin n') → motive (natAdd n i)) :
--       drop m (Nat.le_add_right_of_le h) (addCases u v) =
--         fun i : Fin (n + n' - m) =>
--           dcast (by simp)
--             (addCases (m := n - m) (n := n') (drop m h u) v (i.cast (by omega))) := sorry

/-- Version of `drop_addCases_left` that specializes `addCases` to `append`. -/
theorem drop_append_left {n' : ℕ} {α : Sort*} (m : ℕ) (h : m ≤ n) (u : (i : Fin n) → α)
    (v : (i : Fin n') → α) :
      drop m (Nat.le_add_right_of_le h) (append u v) =
          append (drop m h u) v ∘ Fin.cast (by omega) := by
  ext i
  simp [append, addCases, Fin.cast]
  split <;> rename_i h'
  · simp_all
  · simp at h'
    have h1 : ¬ i.val < n - m := by omega
    have h2 : i.val + m - n = i.val - (n - m) := by omega
    simp [h1, h2]

/-- Dropping the first `n + m` elements of an `addCases u v`, where `v` is a `n'`-tuple and `m ≤
n'`, is the same as dropping the first `m` elements of `v`. -/
theorem drop_addCases_right {n' : ℕ} {motive : Fin (n + n') → Sort*} (m : ℕ) (h : m ≤ n')
    (u : (i : Fin n) → motive (castAdd n' i)) (v : (i : Fin n') → motive (natAdd n i)) :
      drop (n + m) (Nat.add_le_add_left h n) (addCases u v) =
        fun i => dcast (by simp [natAdd, Fin.cast]; omega) (drop m h v (i.cast (by omega))) := by
  ext i
  simp [Fin.cast, addCases]
  split <;> rename_i h'
  · omega
  · have : i.val + (n + m) - n = i.val + m := by omega
    rw! [this]
    simp [dcast, cast,]
    rw [eqRec_fun_eq_eqRec_sort]

/-- Version of `drop_addCases_right` that specializes `addCases` to `append`. -/
theorem drop_append_right {n' : ℕ} {α : Sort*} (m : ℕ) (h : m ≤ n') (u : (i : Fin n) → α)
    (v : (i : Fin n') → α) :
      drop (n + m) (Nat.add_le_add_left h n) (append u v) =
        fun i => (drop m h v (i.cast (by omega))) := by
  ext i
  simp [Fin.cast, append, addCases]
  split <;> rename_i h'
  · omega
  · have : i.val + (n + m) - n = i.val + m := by omega
    simp [this]

/-- `Fin.drop` intertwines with `List.drop` via `List.ofFn`. -/
theorem ofFn_drop_eq_drop_ofFn {α : Type*} {m : ℕ} (h : m ≤ n) (v : Fin n → α) :
    List.ofFn (drop m h v) = (List.ofFn v).drop m := by
  ext i a
  simp
  constructor <;> intro ⟨h, h'⟩ <;> refine ⟨by omega, ?_⟩ <;> rw! [add_comm, h']

/-- Alternative version of `ofFn_drop_eq_drop_ofFn` with `l : List α` instead of `v : Fin n → α`. -/
theorem ofFn_drop_get {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    List.ofFn (drop m h l.get) = l.drop m := by
  ext i a
  simp [List.getElem?_eq_some_iff]
  constructor <;> intro ⟨h, h'⟩ <;> refine ⟨by omega, ?_⟩ <;> rw! [add_comm, h']

/-- `Fin.drop` intertwines with `List.drop` via `List.get`. -/
theorem get_drop_eq_drop_get_comp_cast {α : Type*} {m : ℕ} (l : List α) (h : m ≤ l.length) :
    (l.drop m).get = drop m h l.get ∘ Fin.cast (List.length_drop) := by
  ext i
  simp [add_comm]

/-- Alternative version with `v : Fin n → α` instead of `l : List α`. -/
theorem get_drop_ofFn_eq_drop_comp_cast {α : Type*} {m : ℕ} (v : Fin n → α) (h : m ≤ n) :
    ((List.ofFn v).drop m).get =
      drop m h v ∘ Fin.cast (by simp only [List.length_drop, List.length_ofFn]) := by
  ext i
  simp [Fin.cast, add_comm]

/-- Dropping the first `m` elements of a tuple is the same as taking the last `n - m` elements of
the tuple. -/
theorem drop_eq_rtake (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    drop m h v = fun i => dcast (by simp [Fin.cast]; omega) (rtake (n - m) (by omega) v i) := by
  ext i
  simp only [Fin.cast, coe_addNat, drop, dcast, cast, coe_natAdd, rtake]
  have : n - (n - m) + i.val = i.val + m := by omega
  rw! [this]

/-- Version of `drop_eq_rtake` for uniform tuples `v : Fin n → α` -/
theorem drop_eq_rtake' {α : Sort*} (m : ℕ) (h : m ≤ n) (v : Fin n → α) :
    drop m h v = rtake (n - m) (by omega) v := by
  ext i
  have : i.val + m = n - (n - m) + i.val := by omega
  simp [Fin.cast, this]

/-- The concatenation of the first `m` elements and the last `n - m` elements of a tuple is the
same as the original tuple. -/
theorem take_drop_addCases' (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    Fin.addCases' (take m h v) (drop m h v) =
      fun i =>
        cast (by simp [append, addCases, castLE, Fin.cast]; intro hi; rw! [Nat.sub_add_cancel hi])
          (v (i.cast (by omega))) := by
  ext i
  simp [addCases', addCases, Fin.cast, castLE, cast]
  split
  · simp
  · have : i.val - m + m = i.val := by omega
    rw! [this]
    sorry

/-- The concatenation of the first `m` elements and the last `n - m` elements of a tuple is the
same as the original tuple. -/
theorem take_drop_append {α : Sort*} (m : ℕ) (h : m ≤ n) (v : Fin n → α) :
    Fin.append (take m h v) (drop m h v) = fun i => v (i.cast (by omega)) := by
  ext i
  simp [append, addCases, Fin.cast, castLE]
  split
  · simp
  · have : i.val - m + m = i.val := by omega
    simp [this]

/-- Taking the first `m₂ - m₁` elements of the last `m₂` elements of a tuple is the same as taking
the first `m₂ - m₁` elements of the original tuple. -/
theorem take_drop_eq_drop_take (m₁ m₂ : ℕ) (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ n) (v : (i : Fin n) → α i) :
    take (m₂ - m₁) (by omega) (drop m₁ (by omega) v) =
      drop m₁ (by omega) (take m₂ h₂ v) := by
  ext i
  rfl

/-- Dropping the last `m` elements of a tuple is the same as taking the first `n - m` elements of
the tuple. -/
@[simp]
theorem rdrop_eq_take (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    rdrop m h v = take (n - m) (by omega) v := rfl

end Drop

end Fin
