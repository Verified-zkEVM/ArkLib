/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Classes.HasSucc

/-!
# HasPred Typeclass

This file defines the `HasPred` typeclass for types that have a predecessor operation,
along with the `LawfulHasPred` class that ensures the predecessor operation behaves
correctly with respect to the successor operation.

## Main Definitions

- `HasPred T`: A typeclass for types with a predecessor operation `pred : T → T`
- `LawfulHasPred T`: A typeclass ensuring that `pred (succ x) = x`

## Implementation Notes

The predecessor operation is typically related to the successor operation,
but the relationship is not always bidirectional. For example, with natural numbers,
`pred (succ n) = n` but `succ (pred 0) ≠ 0` since `pred 0 = 0`.

The `LawfulHasPred` class only requires the "left inverse" property:
`pred ∘ succ = id`, but NOT `succ ∘ pred = id`.
-/

universe u

/-- Typeclass for types that have a predecessor operation. -/
class HasPred (T : Type u) where
  /-- The predecessor operation for the `HasPred` typeclass.
    We put this as prime to avoid potential conflict with future changes upstream. -/
  pred' : T → T

export HasPred (pred')

/-- A lawful predecessor operation should be the left inverse of successor.

This class ensures that `pred (succ x) = x` for all `x : T`.
It requires the type to have a `HasSucc` instance.

Note: This does NOT require `succ (pred x) = x`, as this is not true in general
(e.g., for natural numbers with truncated predecessor).
-/
class LawfulHasPred (T : Type u) [HasSucc T] [HasPred T] : Prop where
  /-- Predecessor after successor gives back the original. -/
  pred'_succ : ∀ x : T, pred' (succ' x) = x

export LawfulHasPred (pred'_succ)

attribute [simp] pred'_succ

namespace HasPred

/-- Natural numbers have a predecessor operation (truncated). -/
instance : HasPred Nat where
  pred' := Nat.pred

/-- Natural numbers have a lawful predecessor operation. -/
instance : LawfulHasPred Nat where
  pred'_succ := Nat.pred_succ

end HasPred
