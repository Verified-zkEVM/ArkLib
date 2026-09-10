/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryEqualMachine
public import ArkLib.Data.Computation.BinaryWordSemantics

/-!
# Same-run Boolean equality guard

Equality compares decoded natural values, allowing any physical zero padding. Both comparison
and the final Boolean branch occur on the same actual trace; the original modulus is retained.
-/

@[expose] public section

namespace Computation.BinaryEqualMachine

open BinaryWordMachine (Word value natOrder)

/-- The finite ordering branch agrees with the proof-side equality specification. -/
theorem orderEq_natOrder (a b : ℕ) : orderEq (natOrder a b) = decide (a = b) := by
  by_cases h : a = b
  · subst b
    simp [natOrder, orderEq]
  · unfold natOrder
    split_ifs <;> simp [orderEq, h]
    omega

/-- Every original comparison successor occupies the same four physical inner tapes. -/
theorem compare_step {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.step s = some t) (q : Word) :
    step (.compare q s) = some (.compare q t) := by
  cases s <;> first
  | exact congrArg (Option.map (Configuration.compare q)) h
  | cases h

theorem compare_trace {n : ℕ} {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.Trace n s t) (q : Word) : Trace n (.compare q s) (.compare q t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (compare_step head q) ih

/-- Same-trace equality has exact physical-width cost, with no canonical-input requirement. -/
theorem equality_correct (q xs ys : Word) :
    Trace (max xs.length ys.length + 3) (.compare q (.startCompare xs ys))
      (.done q (decide (value xs = value ys))) ∧
    runFuel (max xs.length ys.length + 3) (.compare q (.startCompare xs ys)) =
      .done q (decide (value xs = value ys)) := by
  have hcmp := (BinaryWordMachine.compare_correct xs ys).1
  have hs : Trace 1 (.compare q (.ordering (natOrder (value xs) (value ys))))
      (.done q (orderEq (natOrder (value xs) (value ys)))) := .cons rfl (.nil _)
  have ht := (compare_trace hcmp q).append hs
  rw [orderEq_natOrder] at ht
  exact ⟨ht, ht.runFuel_eq⟩

/-- The actual RAM-lifted equality guard preserves memory and its original modulus tape. -/
theorem equality_ramRunFuel (mem : AddressedBits.Memory) (q xs ys : Word) :
    ramRunFuel (max xs.length ys.length + 3) (mem, .compare q (.startCompare xs ys)) =
      (mem, .done q (decide (value xs = value ys))) := by
  rw [ramRunFuel_eq, (equality_correct q xs ys).2]

end Computation.BinaryEqualMachine
