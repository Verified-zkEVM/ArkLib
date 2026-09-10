/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryInverseField

/-!
# Literal prime-field inverse execution checks

The candidate search must perform real failed multiplications before finding the inverse. Zero
and padded inputs exercise full restoration; product tests and candidate increments expose the
physical phase boundaries independently of the final arithmetic value.
-/

@[expose] public section

namespace Computation.BinaryInverseMachine

/-- Actual searches reach later inverse candidates and retain the exact input and modulus tapes. -/
example :
    runFuel 1064 (.start [true, true] [false, true]) =
      .done [true, true] [false, true] [false, true] ∧
    runFuel 3408 (.start [true, false, true] [false, true]) =
      .done [true, false, true] [false, true] [true, true] ∧
    runFuel 518 (.start [false, true] [true]) = .done [false, true] [true] [true] := by
  decide +kernel

/-- Padding survives on retained operands; padded zero returns zero only after restoration. -/
example :
    runFuel 1596 (.start [true, true, false] [false, true, false, false]) =
      .done [true, true, false] [false, true, false, false] [false, true] ∧
    runFuel 8 (.start [true, false, true] [false, false, false]) =
      .restore [true, false, true] [] [false, false, false] false ∧
    runFuel 9 (.start [true, false, true] [false, false, false]) =
      .done [true, false, true] [false, false, false] [] := by
  decide +kernel

/-- The finite one test pops its low bit; failed products are explicitly cleared. -/
example :
    runFuel 1 (.checkProduct [true, true] [false, true] [true] [true]) =
      .afterOne [true, true] [false, true] [true] [] ∧
    runFuel 2 (.checkProduct [true, true] [false, true] [true] [true]) =
      .recoverReverse [true, true] [false, true] [true] [] ∧
    runFuel 4 (.checkProduct [true, false, true] [true, true] [true] [true, true]) =
      .incrementReverse [true, false, true] [true, true] [true] [] := by
  decide +kernel

/-- Seed and increment create two physical candidate copies; lifted search preserves RAM. -/
example :
    let mem := AddressedBits.Memory.node true .empty (.node false .empty .empty)
    runFuel 8 (.start [true, true] [false, true]) =
      .multiply [true] (.start [true, true] [true] [false, true]) ∧
    runFuel 21 (.incrementReverse [true, false, true] [false, true] [false, true] []) =
      .multiply [true, true] (.start [true, false, true] [true, true] [false, true]) ∧
    ramRunFuel 1064 (mem, .start [true, true] [false, true]) =
      (mem, .done [true, true] [false, true] [false, true]) := by
  decide +kernel

end Computation.BinaryInverseMachine
