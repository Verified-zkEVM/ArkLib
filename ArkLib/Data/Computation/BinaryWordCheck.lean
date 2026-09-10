/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryWordSemantics

/-!
# Literal local-bit arithmetic execution checks

Carry propagation crosses a full input word, unequal widths require zero extension, and padding
is physically removed. Comparison must let a higher differing bit override an earlier decision.
The checks execute the actual successor observer, including final emission, and retain RAM memory.
-/

@[expose] public section

namespace Computation.BinaryWordMachine

/-- Carry-out, carry-in, zero inputs and removal of high padding use actual bit transitions. -/
example :
    runFuel 11 (.startAdd [true, true, true] [true] false) =
      .word [false, false, false, true] ∧
    runFuel 9 (.startAdd [true, true] [true] true) = .word [true, false, true] ∧
    runFuel 5 (.startAdd [] [] true) = .word [true] ∧
    runFuel 5 (.startAdd [] [] false) = .word [] ∧
    runFuel 11 (.startAdd [true, false, false] [true] false) = .word [false, true] ∧
    runFuel 11 (.startAdd [false, false, false] [] false) = .word [] := by
  decide +kernel

/-- Higher differing bits override lower decisions; physical zero padding does not change value. -/
example :
    runFuel 4 (.startCompare [true] [false, true]) = .ordering .lt ∧
    runFuel 4 (.startCompare [false, true] [true]) = .ordering .gt ∧
    runFuel 5 (.startCompare [false, true, false] [false, true]) = .ordering .eq ∧
    runFuel 4 (.startCompare [] [false, false]) = .ordering .eq ∧
    runFuel 2 (.startCompare [] []) = .ordering .eq := by
  decide +kernel

/-- The last emit is charged, and the actual RAM lift preserves nonempty memory. -/
example :
    let mem := AddressedBits.Memory.node true .empty (.node false .empty .empty)
    runFuel 10 (.startAdd [true, true, true] [true] false) =
      .reverse [] [false, false, false, true] ∧
    ramRunFuel 11 (mem, .startAdd [true, true, true] [true] false) =
      (mem, .word [false, false, false, true]) := by
  decide +kernel

end Computation.BinaryWordMachine
