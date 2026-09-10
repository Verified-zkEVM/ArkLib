/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinarySubtractSemantics

/-!
# Literal subtraction boundary checks

Long borrow chains, underflow with a nonempty discarded result, unequal widths and zero padding
exercise actual successors. The underflow boundary checks require the final clearing transition.
-/

@[expose] public section

namespace Computation.BinarySubtractMachine

/-- Borrow propagates through zeros; saturation and input padding produce canonical output. -/
example :
    runFuel 12 (.start [false, false, false, true] [true] false) =
      .normalize (.word [true, true, true]) ∧
    runFuel 10 (.start [true] [false, false, true] false) = .normalize (.word []) ∧
    runFuel 10 (.start [true, false, false] [true] false) = .normalize (.word []) ∧
    runFuel 10 (.start [true, true, false] [true] false) =
      .normalize (.word [false, true]) ∧
    runFuel 4 (.start [] [] true) = .normalize (.word []) ∧
    runFuel 4 (.start [] [] false) = .normalize (.word []) := by
  decide +kernel

/-- Borrow-in decrements without a right operand, including zero and powers of two. -/
example :
    runFuel 10 (.start [false, false, true] [] true) =
      .normalize (.word [true, true]) ∧
    runFuel 6 (.start [true] [] true) = .normalize (.word []) ∧
    runFuel 10 (.start [false, false, false] [] true) = .normalize (.word []) := by
  decide +kernel

/-- Underflow clearing and final emission are charged, and nonempty RAM remains identical. -/
example :
    let mem := AddressedBits.Memory.node true .empty (.node false .empty .empty)
    runFuel 7 (.start [true] [false, false, true] false) = .discard [true] ∧
    runFuel 8 (.start [true] [false, false, true] false) = .discard [] ∧
    ramRunFuel 9 (mem, .start [true] [false, false, true] false) =
      (mem, .normalize (.word [])) := by
  decide +kernel

end Computation.BinarySubtractMachine
