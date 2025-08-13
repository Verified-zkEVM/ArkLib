/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic

universe u

/-!
# HasSucc Typeclass

This file defines the `HasSucc` typeclass for types that have a successor operation,
along with the `LawfulHasSucc` class that ensures the successor operation behaves
correctly with respect to addition.

## Main Definitions

- `HasSucc T`: A typeclass for types with a successor operation `succ : T → T`
- `LawfulHasSucc T`: A typeclass ensuring that `succ x = x + 1`

## Implementation Notes

The `LawfulHasSucc` class requires that the type has `Add` and `One` instances,
and that the successor operation is equivalent to adding one on the right.
-/

/-- Typeclass for types that have a successor operation. -/
class HasSucc (T : Type u) where
  /-- The successor operation for the `HasSucc` typeclass.
    We put this as prime to avoid potential conflict with future changes upstream. -/
  succ' : T → T

export HasSucc (succ')

/-- A lawful successor operation should be equivalent to adding one.

This class ensures that `succ x = x + 1` for all `x : T`.
It requires the type to have `Add` and `One` instances.
-/
class LawfulHasSucc (T : Type u) [HasSucc T] [Add T] [One T] : Prop where
  /-- The successor of `x` should equal `x + 1`. -/
  succ'_eq_add_one : ∀ x : T, succ' x = x + 1

export LawfulHasSucc (succ'_eq_add_one)

attribute [simp] succ'_eq_add_one

namespace HasSucc

/-- Natural numbers have a successor operation. -/
instance : HasSucc Nat where
  succ' := Nat.succ

/-- Natural numbers have a lawful successor operation. -/
instance : LawfulHasSucc Nat where
  succ'_eq_add_one := Nat.succ_eq_add_one

-- Convenience lemmas

/-- Successor distributes over the successor operation (when lawful). -/
theorem succ_succ {T : Type u} [HasSucc T] [Add T] [One T] [LawfulHasSucc T] (x : T) :
    succ' (succ' x) = x + 1 + 1 := by
  rw [LawfulHasSucc.succ'_eq_add_one, LawfulHasSucc.succ'_eq_add_one]

/-- Successor is injective for natural numbers. -/
theorem succ'_injective : Function.Injective (succ' : Nat → Nat) :=
  Nat.succ_injective

/-- Successor is never zero for natural numbers. -/
theorem succ'_ne_zero (n : Nat) : succ' n ≠ 0 :=
  Nat.succ_ne_zero n

end HasSucc
