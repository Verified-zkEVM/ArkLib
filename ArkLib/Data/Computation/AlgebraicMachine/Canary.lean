/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AlgebraicMachine.BatchHorner
public import Mathlib.Algebra.Field.ZMod

/-!
# Kernel-checked algebraic execution boundary checks

These examples reduce the interpreter itself; they do not invoke the routine correctness
theorems. The literal input heap represents descending coefficients `[2, 3, 5]` and points
`[1, 4]` over the field of seventeen elements. Reading the final registers/cells is a test
observation, not an extra machine instruction or an asserted free output conversion.
-/

@[expose] public section

namespace AlgebraicMachine

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private def exampleHeap : Heap (ZMod 17) :=
  ⟨5, fun a => match a with
    | 0 => some (.field 5, .null)
    | 1 => some (.field 3, .pointer 0)
    | 2 => some (.field 2, .pointer 1)
    | 3 => some (.field 4, .null)
    | 4 => some (.field 1, .pointer 3)
    | _ => none⟩

private def exampleState : State (ZMod 17) 8 :=
  ({ State.empty with heap := exampleHeap }.write Horner.cursor (.pointer 2)).write
    Horner.point (.field 4)

/-- `2 * 4² + 3 * 4 + 5 = 15` in this field, at the exact transition bound. -/
example : (run 43 ⟨exampleState, [.execute Horner.program]⟩).map
    (fun s => s.registers Horner.accumulator) = some (.field 15) := by decide

/-- One fewer transition does not produce a successful termination. -/
example : (run 42 ⟨exampleState, [.execute Horner.program]⟩).isNone = true := by decide

private def batchState : State (ZMod 17) 8 :=
  (exampleState.write BatchHorner.coefficients (.pointer 2)).write BatchHorner.points (.pointer 4)

/-- The final output head is the newly allocated cell at address six. -/
example : (run 123 ⟨batchState, [.execute BatchHorner.program]⟩).map
    (fun s => s.registers BatchHorner.output) = some (.pointer 6) := by decide

/-- The final output is explicitly `[15, 10]`, in reversed point order. -/
example : (run 123 ⟨batchState, [.execute BatchHorner.program]⟩).bind
    (fun s => s.heap.cells 6) = some (.field 15, .pointer 5) := by decide

/-- The first allocated output cell is the result at the first supplied point. -/
example : (run 123 ⟨batchState, [.execute BatchHorner.program]⟩).bind
    (fun s => s.heap.cells 5) = some (.field 10, .null) := by decide

/-- A type-invalid Boolean branch is stuck, not accepted as halted. -/
theorem type_invalid_boolean_branch_is_stuck :
    let _ : Fact (Nat.Prime 17) := ⟨by decide⟩
    (run 10 (⟨State.empty, [.execute (.branch 0 .skip .skip)]⟩ :
    Configuration (ZMod 17) 8)).isNone = true := by decide

end AlgebraicMachine
