/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AlgebraicMachine.Basic

/-!
# Heap extension and materialized lists

List representations are proof relations over pair cells, not executable conversions.
Allocation preserves existing cells in a well-formed heap. Consequently a list already
represented in a well-formed heap remains represented after an extension.
-/

@[expose] public section

namespace AlgebraicMachine

variable {F : Type*}

/-- No cell is allocated at or beyond the next fresh address. -/
def Heap.WellFormed (h : Heap F) : Prop :=
  ∀ address, h.next ≤ address → h.cells address = none

/-- An extension retains the allocation frontier and all older cells. -/
structure Heap.Extends (new old : Heap F) : Prop where
  next_le : old.next ≤ new.next
  cells_eq : ∀ address, address < old.next → new.cells address = old.cells address

/-- The empty heap has no allocated cells. -/
theorem Heap.empty_wellFormed : (Heap.empty : Heap F).WellFormed := by
  intro address _h
  rfl

/-- An occupied cell in a well-formed heap lies below its allocation frontier. -/
theorem Heap.address_lt_next {h : Heap F} (hw : h.WellFormed)
    {address : ℕ} {cell : Value F × Value F} (hc : h.cells address = some cell) :
    address < h.next := by
  apply Nat.lt_of_not_ge
  intro hge
  have hn := hw address hge
  rw [hc] at hn
  cases hn

/-- Pair allocation does not overwrite any previously allocated address. -/
theorem Heap.allocate_extends (h : Heap F) (a b : Value F) :
    (h.allocate a b).Extends h := by
  refine ⟨Nat.le_succ _, ?_⟩
  intro address hlt
  exact Function.update_of_ne (Nat.ne_of_lt hlt) _ _

/-- Fresh pair allocation preserves the frontier invariant. -/
theorem Heap.allocate_wellFormed {h : Heap F} (hw : h.WellFormed) (a b : Value F) :
    (h.allocate a b).WellFormed := by
  intro address hge
  have hlt : h.next < address := hge
  change Function.update h.cells h.next (some (a, b)) address = none
  rw [Function.update_of_ne (Ne.symm (Nat.ne_of_lt hlt))]
  exact hw address (Nat.le_of_lt hlt)

/-- The fresh cell stores exactly the two supplied atoms. -/
theorem Heap.allocate_cell (h : Heap F) (a b : Value F) :
    (h.allocate a b).cells h.next = some (a, b) := by
  exact Function.update_self _ _ _

/-- A null-terminated list is represented by a chain of literal pair cells. -/
inductive RepresentsList (heap : Heap F) : Value F → List (Value F) → Prop where
  | nil : RepresentsList heap .null []
  | cons {address : ℕ} {head tail : Value F} {rest : List (Value F)}
      (cell : heap.cells address = some (head, tail))
      (represented : RepresentsList heap tail rest) :
      RepresentsList heap (.pointer address) (head :: rest)

/-- Heap extension preserves every existing represented list. -/
theorem RepresentsList.extends {old new : Heap F} {root : Value F}
    {xs : List (Value F)} (hr : RepresentsList old root xs)
    (hw : old.WellFormed) (he : new.Extends old) : RepresentsList new root xs := by
  induction hr with
  | nil => exact .nil
  | cons hc _ ih =>
      exact .cons ((he.cells_eq _ (Heap.address_lt_next hw hc)).trans hc) ih

/-- Allocating a new head onto an existing list gives its materialized cons representation. -/
theorem RepresentsList.allocate_cons {h : Heap F} {tail : Value F}
    {xs : List (Value F)} (hr : RepresentsList h tail xs) (hw : h.WellFormed)
    (head : Value F) :
    RepresentsList (h.allocate head tail) (.pointer h.next) (head :: xs) := by
  exact .cons (h.allocate_cell head tail)
    (hr.extends hw (h.allocate_extends head tail))

end AlgebraicMachine
