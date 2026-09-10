/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryBorrowSemantics

/-!
# Actual final-borrow checks

Equality and underflow both return a zero word; their finite-control flags must differ.
The exhausted-input scan transition overwrites any stale flag before normalization or clearing.
-/

@[expose] public section

namespace Computation.BinaryBorrowMachine

/-- Actual flag and output jointly distinguish underflow, equality, and a positive difference. -/
example :
    runFuel 10 ⟨.start [true] [false, false, true] false, false⟩ =
      ⟨.normalize (.word []), true⟩ ∧
    runFuel 10 ⟨.start [true, false, false] [true] false, false⟩ =
      ⟨.normalize (.word []), false⟩ ∧
    runFuel 12 ⟨.start [false, false, false, true] [true] false, false⟩ =
      ⟨.normalize (.word [true, true, true]), false⟩ ∧
    runFuel 4 ⟨.start [] [] true, false⟩ = ⟨.normalize (.word []), true⟩ := by
  decide +kernel

/-- Recording occurs on the real final scan transition and preserves memory in the lifted run. -/
example :
    let mem := AddressedBits.Memory.node true .empty .empty
    step ⟨.scan [] [] false [true], true⟩ = some ⟨.normalize (.trim [true]), false⟩ ∧
    step ⟨.scan [] [] true [false], false⟩ = some ⟨.discard [false], true⟩ ∧
    ramRunFuel 10 (mem, ⟨.start [true] [false, false, true] false, false⟩) =
      (mem, ⟨.normalize (.word []), true⟩) := by
  decide +kernel

end Computation.BinaryBorrowMachine
