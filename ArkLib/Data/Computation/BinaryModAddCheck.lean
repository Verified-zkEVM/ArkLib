/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryModAddField

/-!
# Modular addition execution boundaries

Below-modulus, exact-modulus and carry-across-width sums distinguish backup recovery, zero
reduction and positive reduction. The original modulus word, including padding, is retained.
-/

@[expose] public section

namespace Computation.BinaryModAddMachine

/-- All three reduction branches run on the same physical seven-tape controller. -/
example :
    runFuel 55 (.start [true, false, true] [true] [true]) =
      .done [true, false, true] [false, true] ∧
    runFuel 55 (.start [true, false, true] [false, true] [true, true]) =
      .done [true, false, true] [] ∧
    runFuel 55 (.start [true, false, true] [false, false, true] [false, false, true]) =
      .done [true, false, true] [true, true] ∧
    runFuel 65 (.start [true, false, true, false] [true] [true]) =
      .done [true, false, true, false] [false, true] ∧
    runFuel 55 (.start [true, false, true] [] []) = .done [true, false, true] [] := by
  decide +kernel

/-- Copying produces the original modulus and sum on separate physical tapes before subtraction. -/
example :
    runFuel 23 (.start [true, false, true] [true] [true]) =
      .subtract [true, false, true] [false, true]
        ⟨.start [false, true] [true, false, true] false, false⟩ ∧
    runFuel 7 (.subtract [true, false, true] [false, true] ⟨.normalize (.word []), true⟩) =
      .recoverCopy [true, false, true] [] [false, true] ∧
    runFuel 8 (.subtract [true, false, true] [false, true] ⟨.normalize (.word []), true⟩) =
      .done [true, false, true] [false, true] := by
  decide +kernel

/-- The real memory lift retains nonempty RAM together with the original modulus tape. -/
example :
    let mem := AddressedBits.Memory.node true .empty (.node false .empty .empty)
    ramRunFuel 55 (mem, .start [true, false, true] [false, false, true] [false, false, true]) =
      (mem, .done [true, false, true] [true, true]) := by
  decide +kernel

end Computation.BinaryModAddMachine
