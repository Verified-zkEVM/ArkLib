import Mathlib
import ArkLib.Data.Classes.HasSucc

universe u

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

/-- Typeclass for types that have a predecessor operation. -/
class HasPred (T : Type u) where
  /-- The predecessor operation. -/
  pred : T → T

/-- A lawful predecessor operation should be the left inverse of successor.

This class ensures that `pred (succ x) = x` for all `x : T`.
It requires the type to have a `HasSucc` instance.

Note: This does NOT require `succ (pred x) = x`, as this is not true in general
(e.g., for natural numbers with truncated predecessor).
-/
class LawfulHasPred (T : Type u) [HasSucc T] [HasPred T] : Prop where
  /-- Predecessor after successor gives back the original. -/
  pred_succ : ∀ x : T, HasPred.pred (HasSucc.succ x) = x

namespace HasPred

/-- Natural numbers have a predecessor operation (truncated). -/
instance : HasPred Nat where
  pred := Nat.pred

/-- Natural numbers have a lawful predecessor operation. -/
instance : LawfulHasPred Nat where
  pred_succ := Nat.pred_succ

-- Convenience lemmas

/-- Predecessor of successor is identity (from LawfulHasPred). -/
theorem pred_succ {T : Type u} [HasSucc T] [HasPred T] [LawfulHasPred T] (x : T) :
    pred (HasSucc.succ x) = x :=
  LawfulHasPred.pred_succ x

/-- Predecessor of zero is zero for natural numbers. -/
theorem pred_zero : pred (0 : Nat) = 0 :=
  Nat.pred_zero

/-- Successor of predecessor for positive natural numbers.
Note: This is NOT a general law - it only holds for positive natural numbers. -/
theorem succ_pred_eq_of_pos {n : Nat} (h : 0 < n) : HasSucc.succ (pred n) = n :=
  Nat.succ_pred_eq_of_pos h

end HasPred
