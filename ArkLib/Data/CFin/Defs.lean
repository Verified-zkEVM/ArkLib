/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib
import ArkLib.Data.CNat.Defs
import ArkLib.Data.Classes.HasSucc
import ArkLib.Data.Classes.HasPred

/-!
# Generic Fin Type and Tuple Operations

This file implements:
1. A generic `GFin` type that works over any `N` type with a less-than operation
2. Generic tuple operations for `GFin` types (analogous to `FinVec` and `FinTuple`)
3. Specialized notation for `GFin` tuples

By parameterizing over the underlying `N` type, we can create finite types for
the CNat hierarchy and other N representations.

## Main Definitions

- `GFin N n`: Elements of type `N` that are less than `n`
- `GFinVec`: Homogeneous vectors indexed by `GFin`
- `GFinTuple`: Heterogeneous tuples indexed by `GFin`
- Generic operations: cons, concat, append, take, drop, slice
- Specialized notation similar to the `Fin` tuple notation

## Design Principles

The `GFin` type requires only minimal structure from `N`:
- A less-than relation `LT`
- Decidability of the less-than relation

Additional operations become available as `N` gains more structure through typeclasses.
-/

universe u v w

/-- The `GFin N n` type represents elements of type `N` that are less than `n`. This is the
  generalization of `Fin n` to arbitrary `N` types, though it is assumed that `N` has the structure
  of the natural numbers. -/
@[ext]
structure GFin (N : Type u) [LT N] (n : N) where
  /-- The underlying value of type `N`. -/
  val : N
  /-- The proof that the value is less than `n`. -/
  isLt : val < n

attribute [simp] GFin.isLt

namespace GFin

variable {N : Type u} [LT N] {n : N}

-- Basic Operations (requiring only LT)

/-- Coercion from `GFin` to the underlying `N` type. -/
instance : Coe (GFin N n) N := ⟨GFin.val⟩

-- Operations depending on additional structure

section DecidableEq

variable [DecidableEq N]

/-- `GFin N n` has decidable equality when `N` does. -/
instance : DecidableEq (GFin N n) := by
  intro a b
  by_cases h : a.val = b.val
  · right; exact GFin.ext h
  · left; intro heq; exact h (by rw [heq])

end DecidableEq

section Zero

variable [Zero N] [LT N] (h_pos : (0 : N) < n)

/-- Zero element of `GFin N n` when `N` has zero and `0 < n`. -/
def zero : GFin N n := ⟨0, h_pos⟩

instance [Zero N] [h : Fact ((0 : N) < n)] : Zero (GFin N n) :=
  ⟨zero h.out⟩

end Zero

section Conversions

variable [DecidableRel (· < · : N → N → Prop)]

/-- Try to create a `GFin` from a `N` value, returning `Option`. -/
def ofN? (val : N) : Option (GFin N n) :=
  if h : val < n then some ⟨val, h⟩ else none

/-- Create a `GFin` from a `N` value with a proof that it's less than `n`. -/
def ofN (val : N) (h : val < n) : GFin N n := ⟨val, h⟩

end Conversions

end GFin

-- GFin Vector and Tuple Operations

/-- A `GFinVec` is a homogeneous vector indexed by `GFin N n`. -/
abbrev GFinVec (N : Type u) [LT N] (α : Sort v) (n : N) : Sort _ :=
  GFin N n → α

/-- A `GFinTuple` is a heterogeneous tuple indexed by `GFin N n`. -/
abbrev GFinTuple (N : Type u) [LT N] (n : N) (α : GFinVec N (Sort v) n) : Sort _ :=
  (i : GFin N n) → α i

namespace GFinVec

variable {N : Type u} [LT N] [DecidableRel (· < · : N → N → Prop)]
variable [Zero N] [Add N] [One N] [HasSucc N]

/-- Empty vector for GFin types. -/
def empty {α : Sort v} : GFinVec N α 0 :=
  fun i => False.elim (not_lt_of_le (le_refl 0) i.isLt)

/-- Cons operation for GFin vectors. -/
def cons {α : Sort v} {n : N} (a : α) (v : GFinVec N α n)
    [h : Fact ((0 : N) < (1 : N) + n)] :
    GFinVec N α (1 + n) :=
  fun i =>
    if h : i.val = 0 then a
    else v ⟨i.val - 1, by sorry⟩ -- Need to prove bound properly

/-- Concatenation for GFin vectors. -/
def concat {α : Sort v} {n : N} (v : GFinVec N α n) (a : α)
    [h : Fact (n < n + (1 : N))] :
    GFinVec N α (n + 1) :=
  fun i =>
    if h : i.val < n then v ⟨i.val, h⟩
    else a

/-- Append operation for GFin vectors. -/
def append {α : Sort v} {m n : N} (u : GFinVec N α m) (v : GFinVec N α n)
    [Add N] : GFinVec N α (m + n) :=
  fun i =>
    if h : i.val < m then u ⟨i.val, h⟩
    else v ⟨i.val - m, by sorry⟩ -- Need to prove bound properly

end GFinVec

namespace GFinTuple

variable {N : Type u} [LT N] [DecidableRel (· < · : N → N → Prop)]
variable [Zero N] [Add N] [One N] [HasSucc N]

/-- Empty tuple for GFin types. -/
def empty {α : GFin N 0 → Sort v} : GFinTuple N 0 α :=
  fun i => False.elim (not_lt_of_le (le_refl 0) i.isLt)

/-- Cons operation for GFin tuples. -/
def cons {n : N} {α : Sort v} {β : GFin N n → Sort v} (a : α) (b : GFinTuple N n β)
    [h : Fact ((0 : N) < (1 : N) + n)] :
    GFinTuple N (1 + n) (GFinVec.cons α β) :=
  fun i =>
    if h : i.val = 0 then a
    else b ⟨i.val - 1, by sorry⟩ -- Need to prove bound properly

/-- Concatenation for GFin tuples. -/
def concat {n : N} {α : GFin N n → Sort v} {β : Sort v}
    (u : GFinTuple N n α) (a : β)
    [h : Fact (n < n + (1 : N))] :
    GFinTuple N (n + 1) (GFinVec.concat α β) :=
  fun i =>
    if h : i.val < n then u ⟨i.val, h⟩
    else a

/-- Append operation for GFin tuples. -/
def append {m n : N} {α : GFin N m → Sort v} {β : GFin N n → Sort v}
    (u : GFinTuple N m α) (v : GFinTuple N n β) :
    GFinTuple N (m + n) (GFinVec.append α β) :=
  fun i =>
    if h : i.val < m then u ⟨i.val, h⟩
    else v ⟨i.val - m, by sorry⟩ -- Need to prove bound properly

end GFinTuple
