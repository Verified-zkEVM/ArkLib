/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Batteries.Data.List.Basic
-- Unfolds Batteries' unexposed `List.takeList` only to prove its public bridge law.
import all Batteries.Data.List.Basic
public import Mathlib.Data.List.SplitLengths

/-!
# Consecutive blocks with repeated sizes

`List.takeList` has an existing theorem-backed tail-recursive compiler implementation. Its first
component agrees with `List.splitLengths`, allowing executable chunking to reuse the latter's
coverage and size theorems. Repeating one requested size gives the usual consecutive blocks.
-/

@[expose] public section

namespace List

/-- The executable extraction operation produces the same blocks as `List.splitLengths`. -/
theorem takeList_fst_eq_splitLengths {α : Type*} (xs : List α) (sizes : List ℕ) :
    (xs.takeList sizes).1 = sizes.splitLengths xs := by
  induction sizes generalizing xs with
  | nil => rfl
  | cons ell sizes ih => simp [takeList, splitLengths_cons, splitAt_eq, ih]

/-- Repeating a requested size selects consecutive take/drop blocks. -/
theorem getElem_splitLengths_replicate {α : Type*} (xs : List α) (K ell g : ℕ)
    (hg : g < K) :
    ((replicate K ell).splitLengths xs)[g]'(by simpa using hg) =
      (xs.drop (g * ell)).take ell := by
  induction K generalizing xs g with
  | zero => omega
  | succ K ih =>
    cases g with
    | zero => simp [replicate_succ, splitLengths_cons]
    | succ g =>
      simp only [replicate_succ, splitLengths_cons, getElem_cons_succ]
      rw [ih (xs.drop ell) g (Nat.lt_of_succ_lt_succ hg)]
      simp [drop_drop, Nat.succ_mul, Nat.add_comm]

/-- The length of a repeated-size block is its requested size or the remaining source length. -/
theorem length_getElem_splitLengths_replicate {α : Type*} (xs : List α) (K ell g : ℕ)
    (hg : g < K) :
    (((replicate K ell).splitLengths xs)[g]'(by simpa using hg)).length =
      min ell (xs.length - g * ell) := by
  rw [getElem_splitLengths_replicate xs K ell g hg]
  simp

end List
