/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListRead
public import ArkLib.Data.Computation.SharedListCellMachine
public import ArkLib.Data.Computation.SharedListCellReadMachine

/-!
# Kernel checks for literal block and cell reads

The tests observe actual traces at their final-step boundaries. Nonzero bit indices, zero
stored bits, mixed-valued length markers, dirty memory, and read-after-actual-write are covered.
The arbitrary suspended-child test prevents a false claim that every possible state is read-only.
-/

@[expose] public section

namespace Computation.BitMemoryRead

open AddressedBits (Memory)
open BitMemoryBlock (slot)

private def base : List Bool := [false, true]
private def other : List Bool := [true, false]
private def initial : Memory := Memory.empty.write (slot other []) true
private def stored := BitMemoryBlock.store initial base [true, true] [true, false, true]
private def readBack := runFuel 104 ⟨stored, .next base [true, true] [false, true, false] []⟩

example : readBack =
    ⟨stored, .done base [true, true, true, true, true] [true, false, true]⟩ ∧
    readBack.memory.lookup (slot other []) = true ∧
    (runFuel 103 ⟨stored, .next base [true, true] [false, false, false] []⟩).control =
      .reverse base [true, true, true, true, true] [] [true, false, true] := by
  decide +kernel

example : runFuel 1 ⟨stored, .next base [true] [] []⟩ =
      ⟨stored, .reverse base [true] [] []⟩ ∧
    runFuel 2 ⟨stored, .next base [true] [] []⟩ = ⟨stored, .done base [true] []⟩ := by
  decide +kernel

private def writtenCell := SharedListCellMachine.runFuel 160
  ⟨initial, .building base (.copyTail [true, false] [false, false] [] [])⟩
private def cellRead := runFuel 152
  ⟨writtenCell.memory, .next base [] [false, true, false, true, false] []⟩

example : writtenCell.control = .writing [true, false] [false, false]
      (.done base [true, true, true, true, true]) ∧
    cellRead = ⟨writtenCell.memory,
      .done base [true, true, true, true, true] [true, true, false, false, false]⟩ := by
  decide +kernel

private def parsedCell := SharedListCellRead.runFuel 160
  ⟨writtenCell.memory, .reading [true, false] (.next base []
    [false, true, false, true, false] [])⟩

example : parsedCell = ⟨writtenCell.memory,
      .done base [true, true, true, true, true] [true, false] [false, false]⟩ ∧
    (SharedListCellRead.runFuel 159
      ⟨writtenCell.memory, .reading [true, false] (.next base []
        [false, true, false, true, false] [])⟩).control =
      .reverse base [true, true, true, true, true] [false, false] [] [true, false] := by
  decide +kernel

example : SharedListCellRead.runFuel 1 ⟨stored, .scan base [] [] [true, false] [false]⟩ =
      ⟨stored, .rejected base [] [] [true, false] [false]⟩ ∧
    SharedListCellRead.runFuel 1 ⟨stored, .tag base [] [false, true] [false]⟩ =
      ⟨stored, .rejected base [] [false, true] [false] []⟩ ∧
    SharedListCellRead.runFuel 3 ⟨stored, .tag base [] [true, false, true] []⟩ =
      ⟨stored, .done base [] [] [false, true]⟩ := by
  decide +kernel

private def malformed := runFuel 3
  ⟨initial, .reading base [true] [false] [true, false] (.access .read [])⟩
private def retainedWrite := runFuel 10
  ⟨initial, .reading base [] [] [] (.access (.write true) [true, false])⟩

theorem malformed_child_and_retained_write_are_observed :
    let base : List Bool := [false, true]
    let initial : Memory := Memory.empty.write (slot [true, false] []) true
    let malformed := runFuel 3
      ⟨initial, .reading base [true] [false] [true, false] (.access .read [])⟩
    let retainedWrite := runFuel 10
      ⟨initial, .reading base [] [] [] (.access (.write true) [true, false])⟩
    malformed =
      ⟨initial, .failed base [true] [false] [true, false] (.done none)⟩ ∧
    retainedWrite.memory.lookup [false] = true ∧
    retainedWrite.control = .done base [true] [true] := by
  decide +kernel

end Computation.BitMemoryRead
