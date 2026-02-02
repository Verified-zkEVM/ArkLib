/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib

/-!
# Partial sums and products of lists

This file is currently not used anywhere in ArkLib. May delete in the future.
-/

namespace List

-- TODO: put this elsewhere (for some reason `@[to_additive]` doesn't work)
def partialSum {α : Type*} [AddMonoid α] (l : List α) : List α :=
  [0] ++ match l with
  | [] => []
  | a :: l' => (partialSum l').map (a + ·)

@[to_additive existing]
def partialProd {α : Type*} [Monoid α] (l : List α) : List α :=
  [1] ++ match l with
  | [] => []
  | a :: l' => (partialProd l').map (a * ·)

@[simp]
theorem partialSum_nil : [].partialSum = [0] := rfl

variable {α : Type*} [AddMonoid α]

@[simp]
theorem partialSum_succ {a : α} {l : List α} :
    (a :: l).partialSum = [0] ++ (partialSum l).map (a + ·) := rfl

variable [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)]

-- Pinpoint the first element in the list whose partial sum up to that point is more than `j`
def findSum (l : List α) (j : α) : Option α := l.partialSum.find? (j < ·)

-- TODO: extend theorems to more general types than just `ℕ`

theorem sum_mem_partialSum (l : List ℕ) : l.sum ∈ l.partialSum := by
  induction l with
  | nil => simp [partialSum]
  | cons a l' ih =>
    simp only [partialSum_succ, sum_cons, singleton_append, mem_cons, mem_map]
    right
    exact ⟨l'.sum, ih, rfl⟩

theorem partialSum_length (l : List ℕ) : l.partialSum.length = l.length + 1 := by
  induction l with
  | nil => simp [partialSum]
  | cons a l' ih =>
    simp only [partialSum_succ, singleton_append, length_cons, length_map, ih]

theorem findSum_of_le_sum {l : List ℕ} {j : ℕ} (h : j < l.sum) : ∃ n, findSum l j = some n := by
  unfold findSum
  rw [← Option.isSome_iff_exists]
  rw [List.find?_isSome]
  exact ⟨l.sum, sum_mem_partialSum l, by simp [h]⟩

-- Pinpoint the first index in the list whose partial sum is more than `j`
def findSumIdx (l : List α) (j : α) : ℕ := l.partialSum.findIdx (j < ·)

-- Variant of `findSumIdx` with bounds
def findSumIdx' (l : List ℕ) (j : Fin l.sum) : Fin l.length := ⟨findSumIdx l j, sorry⟩

def findSumIdxWith (l : List ℕ) (j : Fin l.sum) : (i : Fin l.length) × Fin (l.get i) := sorry

@[simp]
theorem ranges_length_eq_self_length {l : List ℕ} : l.ranges.length = l.length := by
  induction l with
  | nil => simp only [List.ranges, List.length_nil]
  | cons n l' ih => simp only [List.ranges, List.length_cons, List.length_map, ih]

@[simp]
theorem ranges_nil : List.ranges [] = [] := rfl

@[simp]
theorem ranges_succ {a : ℕ} {l : List ℕ} :
    List.ranges (a :: l) = range a :: l.ranges.map (map (a + ·)) := rfl

end List
