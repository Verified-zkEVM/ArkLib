/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryMulField

/-!
# Literal multiplication countdown checks

The checks exercise zero iterations, multiple actual decrements, modular wraparound, and padded
retained operands. Boundary states require the physical accumulator/counter transfer passes.
-/

@[expose] public section

namespace Computation.BinaryMulMachine

/-- Products execute repeated literal modular additions and retain the exact modulus and factor. -/
example :
    runFuel 290 (.start [true, true] [false, true] [false, true]) =
      .done [true, true] [false, true] [true] ∧
    runFuel 602 (.start [true, false, true] [true, true] [false, false, true]) =
      .done [true, false, true] [false, false, true] [false, true] ∧
    runFuel 602 (.start [true, false, true] [] [false, false, true]) =
      .done [true, false, true] [false, false, true] [] ∧
    runFuel 602 (.start [true, false, true] [true, true] []) =
      .done [true, false, true] [] [] ∧
    runFuel 722 (.start [true, false, true, false] [true, true] [false, true, false, false]) =
      .done [true, false, true, false] [false, true, false, false] [true] := by
  decide +kernel

/-- The empty accumulator still crosses its phases and the countdown moves before decrement. -/
example :
    runFuel 10 (.start [true, true] [false, true] [false, true]) =
      .decrement [true, true] [false, true] [] (.start [false, true] [] true) ∧
    runFuel 1 (.start [true, true] [] [true]) = .loop [true, true] [] [true] [] ∧
    runFuel 2 (.start [true, true] [] [true]) = .done [true, true] [true] [] := by
  decide +kernel

/-- The lifted repeated-addition loop preserves nonempty RAM. -/
example :
    let mem := AddressedBits.Memory.node true .empty .empty
    ramRunFuel 290 (mem, .start [true, true] [false, true] [false, true]) =
      (mem, .done [true, true] [false, true] [true]) := by
  decide +kernel

end Computation.BinaryMulMachine
