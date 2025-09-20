/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib

/-! # Find index of first matching element in a list -/

namespace List

variable {α : Type*}

/-- `findIdx` but with better definitional equality -/
def findIdx' (p : α → Bool) (l : List α) : ℕ :=
  match l with
  | [] => 0
  | x :: xs => bif p x then 0 else findIdx' p xs + 1

@[simp] theorem findIdx'_nil {p : α → Bool} : findIdx' p [] = 0 := rfl

@[grind =] theorem findIdx'_cons {p : α → Bool} {x : α} {xs : List α} :
    findIdx' p (x :: xs) = bif p x then 0 else findIdx' p xs + 1 := rfl

@[csimp, grind =]
theorem findIdx'_eq_findIdx : @findIdx' = @findIdx := by
  funext α p l
  induction l with | nil => rfl | cons _ _ _ => grind

/-- `idxOf` but with better definitional equality -/
def idxOf' [BEq α] (a : α) (l : List α) : ℕ := findIdx' (· == a) l

@[simp] theorem idxOf'_nil [BEq α] {a : α} : idxOf' a [] = 0 := rfl

@[grind =] theorem idxOf'_cons [BEq α] {a : α} {x : α} {xs : List α} :
    idxOf' a (x :: xs) = bif x == a then 0 else idxOf' a xs + 1 := rfl

@[csimp, grind =]
theorem idxOf'_eq_idxOf : @idxOf' = @idxOf := by
  funext α inst a l
  induction l with | nil => rfl | cons _ _ _ => grind

def findFinIdx (p : α → Bool) (l : List α) : Fin (l.length + 1) :=
  ⟨List.findIdx' p l,
    Nat.lt_succ_of_le (by rw [List.findIdx'_eq_findIdx]; exact List.findIdx_le_length)⟩

def findFinIdxIfTrue (p : α → Bool) (l : List α) (h : ∃ x ∈ l, p x) : Fin l.length :=
  ⟨List.findIdx' p l, by rw [List.findIdx'_eq_findIdx]; exact List.findIdx_lt_length.mpr h⟩

def finIdxOf [BEq α] [LawfulBEq α] (a : α) (l : List α) : Fin (l.length + 1) :=
  ⟨List.idxOf' a l, Nat.lt_succ_of_le (by rw [List.idxOf'_eq_idxOf]; exact List.idxOf_le_length)⟩

def finIdxOfIfTrue [BEq α] [LawfulBEq α] (a : α) (l : List α) (h : a ∈ l) : Fin l.length :=
  ⟨List.idxOf' a l, by rw [List.idxOf'_eq_idxOf]; exact List.idxOf_lt_length_iff.mpr h⟩

end List
