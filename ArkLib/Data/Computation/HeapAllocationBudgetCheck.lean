/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.HeapAllocationBudget

/-! # Kernel checks of the last permitted allocation and reserved successor -/

@[expose] public section

namespace Computation.HeapAllocationBudget

open AddressedBits (Memory)
open SharedListHeap (nilPointer)

example : Available .empty 2 1 [false, true] :=
  available_empty (by decide) (by decide) (by decide)

example : Available .empty 2 0 [true, true] :=
  available_empty (by decide) (by decide) (by decide)

/-- The last permitted allocation physically writes its cell and retains successor three. -/
example :
    SharedListAllocator.runFuel (SharedListAllocator.steps 2 1)
      ⟨Memory.empty, .incrementing [true] (nilPointer 2) (.scan [false, true] [] [] true)⟩ =
      ⟨SharedListHeap.writeCell .empty [false, true] [true] (nilPointer 2),
        .writing [true, true]
          (.writing [true] (nilPointer 2) (.done [false, true] (List.replicate 4 true)))⟩ := by
  decide +kernel

/-- Attempting to advance the reserved final pointer overflows before writing any bit. -/
example :
    SharedListAllocator.runFuel 10
      ⟨Memory.empty, .incrementing [true] (nilPointer 2) (.scan [true, true] [] [] true)⟩ =
      ⟨Memory.empty, .overflow [true, true] (nilPointer 2) [true] (nilPointer 2)⟩ := by
  decide +kernel

/-- The proof consumes the actual last available unit without a caller-supplied carry flag. -/
example : ∃ final : SharedListAllocator.Configuration,
    SharedListAllocator.runFuel (SharedListAllocator.steps 2 1)
      ⟨Memory.empty, .incrementing [true] (nilPointer 2) (.scan [false, true] [] [] true)⟩ = final ∧
    Available final.memory 2 0 [true, true] := by
  obtain ⟨final, _ht, hf, _ho, _hr, _hframe, hb⟩ := allocate_execution
    (mem := .empty) (w := 2) (h := 1) (remaining := 0)
    (current := [false, true]) (head := [true])
    (available_empty (by decide) (by decide) (by decide)) (by decide)
    (SharedListHeap.RepList.nil (mem := .empty) (w := 2) (h := 1))
  exact ⟨final, hf, hb⟩

end Computation.HeapAllocationBudget
