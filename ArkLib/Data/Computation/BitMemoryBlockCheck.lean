/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BitMemoryBlock

/-!
# Kernel checks for actual bit-memory word writes

The controller preserves another equal-width pointer block, stores zero as well as one bits,
returns only after all address resets, and retains tapes on malformed-child failure.
-/

@[expose] public section

namespace Computation.BitMemoryBlock

open AddressedBits (Memory)

private def base : List Bool := [false, true]
private def other : List Bool := [true, false]
private def initial : Memory := Memory.empty.write (slot other []) true
private def written := runFuel 76 ⟨initial, .next base [] [true, false, true]⟩

example : written.control = .done base [true, true, true] ∧
    written.memory.lookup (slot base []) = true ∧
    written.memory.lookup (slot base [true]) = false ∧
    written.memory.lookup (slot base [true, true]) = true ∧
    written.memory.lookup (slot other []) = true := by decide +kernel

example : (runFuel 75 ⟨initial, .next base [] [true, false, true]⟩).control =
    .next base [true, true, true] [] := by decide +kernel

theorem empty_source_finishes_without_writing :
    let base : List Bool := [false, true]
    let initial : Memory := Memory.empty.write (slot [true, false] []) true
    runFuel 1 ⟨initial, .next base [true] []⟩ =
      ⟨initial, .done base [true]⟩ := by decide +kernel

private def malformed := runFuel 3
  ⟨initial, .writing base [true] [false, true] (.access (.write true) [])⟩

example : malformed =
    ⟨initial, .failed base [true] [false, true] (.done none)⟩ := by decide +kernel

-- The retained child's operation, not a reconstructed outer payload, determines the written bit.
private def retained := runFuel 7
  ⟨initial, .writing base [] [] (.access (.write true) [true, false])⟩

example : retained.memory.lookup [false] = true ∧
    retained.control = .done base [true] := by decide +kernel

end Computation.BitMemoryBlock
