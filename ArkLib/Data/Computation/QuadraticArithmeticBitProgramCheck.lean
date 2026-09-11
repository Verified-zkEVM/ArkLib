/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticArithmeticBitProgram

/-!
# Kernel replay of composed arithmetic dispatch and halting

These closed checks execute the physical controller directly. They preserve the independently
checked ADD and EQUAL programs, equality-flag adoption by Boolean emission, and empty/rejected
handoffs. They are regression checks, not a generic whole-program refinement or cost theorem.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitProgramCheck

open BinaryWordMachine (Word)
open QuadraticArithmeticBitProgram

private def q : Word := [true, false, true]
private def regs : Registers := ![[true, true, false], [false, false, true], [true], [],
  [false], [true, false], [false, true], [true, false, false]]
private def input : Inputs := ![[true], [], [false, true], [true, false], [false]]
private def flags : Flags := ![false, true]
private def code : Code := ⟨[], by decide⟩
private def observe (s : Control) : List Word :=
  List.ofFn (fun i : Fin 13 ↦ tapes s (.inl i)) ++
  List.ofFn (fun i : Fin 8 ↦ tapes s (.inr (.inl i))) ++
  List.ofFn (fun i : Fin 5 ↦ tapes s (.inr (.inr (.inl i)))) ++
  List.ofFn (fun i : Fin 2 ↦ tapes s (.inr (.inr (.inr i))))

-- Equality's finite frame must adopt the new bit before a Boolean emitter reads it.
private def equalThenBoolean : Control := .equal ⟨[.boolean], by decide⟩ input flags
  (.done q regs 0 true)
example : (observe (runFuel 3 equalThenBoolean)).head? = some [true] := by decide +kernel
example : output (runFuel 3 equalThenBoolean) = some (.boolean true) := by decide +kernel

-- No output is claimed for an empty code cursor or a scalar child terminal.
example : output (.ready code q regs input flags) = none ∧
    output (.add code input flags (.done q regs)) = none := by decide +kernel
example : observe (runFuel 1 (.ready code q regs input flags)) =
    observe (.ready code q regs input flags) := by decide +kernel

-- Rejected literal child states must halt with their arbitrary physical words intact.
private def malformed : Control := .initializing code input
  (.literal (.rejected [true, false, false] [false, true]))
example : (step malformed).isNone = true ∧ observe (runFuel 10 malformed) = observe malformed := by
  decide +kernel

private def validInput : Inputs := ![[true, true, false], [false, false, true],
  [true, false, false], [false, true, false], [false, false, false]]
private def initial (op : QuadraticAlgebra.ArithmeticMachine.Operation) : Control :=
  .initializing (literalCode op) validInput (.literal (.start q false))

-- Literal programs execute through initialization, dispatch, scalar children, and output.
example : output (runFuel 416 (initial .add)) =
    some (.pair ([false, false, true], [true, false, false])) := by decide +kernel
theorem literal_equal_program_emits_boolean :
    let validInput : Inputs := ![[true, true, false], [false, false, true],
      [true, false, false], [false, true, false], [false, false, false]]
    output (runFuel 228 (.initializing (literalCode .equal) validInput
      (.literal (.start [true, false, true] false)))) = some (.boolean false) := by decide +kernel

end Computation.QuadraticArithmeticBitProgramCheck
