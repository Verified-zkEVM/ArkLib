/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticArithmeticBitProgram

/-!
# Bounded instruction execution inside the unified controller

These theorems include the actual dispatch and return transitions around each scalar child.
They preserve fixed widths and reduced register values and identify the decoded destination.
They do not prove the induction over a whole literal program or its total execution bound.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitProgram

open BinaryWordMachine (Word value)
open QuadraticAlgebra

/-- A nonempty bounded code cursor dispatches in one actual transition. -/
theorem dispatch_trace (code : Code) (q : Word) (r : Registers) (input : Inputs)
    (flags : Flags) (i : ArithmeticMachine.Instruction) (rest : List ArithmeticMachine.Instruction)
    (hcode : code.val = i :: rest) :
    Trace 1 (.ready code q r input flags) (launch (tailCode code) q r input flags i) :=
  .cons (by simp only [step, hcode]) (.nil _)

/-- The ADD child returns to the next bounded cursor, charging both control transitions. -/
theorem run_add (code : Code) (q : Word) (x y dst : Fin 8)
    (r : Registers) (input : Inputs) (flags : Flags)
    (rest : List ArithmeticMachine.Instruction) (hcode : code.val = .add x y dst :: rest)
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    ∃ n ≤ 22 * q.length + 50, ∃ out,
      Trace n (.ready code q r input flags)
        (.ready (tailCode code) q (Function.update r dst out) input flags) ∧
      runFuel n (.ready code q r input flags) =
        .ready (tailCode code) q (Function.update r dst out) input flags ∧
      out.length = q.length ∧ value out < value q ∧
      QuadraticArithmeticBitAdd.decodeRegisters q (Function.update r dst out) =
        Function.update (QuadraticArithmeticBitAdd.decodeRegisters q r) dst
          (QuadraticArithmeticBitAdd.decodeRegisters q r x +
            QuadraticArithmeticBitAdd.decodeRegisters q r y) ∧
      (∀ i, (Function.update r dst out i).length = q.length) ∧
      (∀ i, value (Function.update r dst out i) < value q) := by
  obtain ⟨n, hn, out, ht, _, hw, hb, hd, hwall, hrall⟩ :=
    QuadraticArithmeticBitAdd.add_execution q x y dst r hwidth hred
  have hi := dispatch_trace code q r input flags (.add x y dst) rest hcode
  have ho : Trace 1 (.add (tailCode code) input flags
      (.done q (Function.update r dst out)))
      (.ready (tailCode code) q (Function.update r dst out) input flags) := .cons rfl (.nil _)
  have hall := (hi.append (lift_add (tailCode code) input flags ht)).append ho
  exact ⟨_, by omega, out, hall, hall.runFuel_eq, hw, hb, hd, hwall, hrall⟩

/-- The MUL child returns to the next bounded cursor, charging both control transitions. -/
theorem run_mul (code : Code) (q : Word) (x y dst : Fin 8)
    (r : Registers) (input : Inputs) (flags : Flags)
    (rest : List ArithmeticMachine.Instruction) (hcode : code.val = .mul x y dst :: rest)
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    ∃ n ≤ value q * (24 * q.length + 48) + 15 * q.length + 34, ∃ out,
      Trace n (.ready code q r input flags)
        (.ready (tailCode code) q (Function.update r dst out) input flags) ∧
      runFuel n (.ready code q r input flags) =
        .ready (tailCode code) q (Function.update r dst out) input flags ∧
      out.length = q.length ∧ value out < value q ∧
      QuadraticArithmeticBitMul.decodeRegisters q (Function.update r dst out) =
        Function.update (QuadraticArithmeticBitMul.decodeRegisters q r) dst
          (QuadraticArithmeticBitMul.decodeRegisters q r x *
            QuadraticArithmeticBitMul.decodeRegisters q r y) ∧
      (∀ i, (Function.update r dst out i).length = q.length) ∧
      (∀ i, value (Function.update r dst out i) < value q) := by
  obtain ⟨n, hn, out, ht, _, hw, hb, hd, hwall, hrall⟩ :=
    QuadraticArithmeticBitMul.mul_execution q x y dst r hwidth hred
  have hi := dispatch_trace code q r input flags (.mul x y dst) rest hcode
  have ho : Trace 1 (.mul (tailCode code) input flags
      (.done q (Function.update r dst out)))
      (.ready (tailCode code) q (Function.update r dst out) input flags) := .cons rfl (.nil _)
  have hall := (hi.append (lift_mul (tailCode code) input flags ht)).append ho
  exact ⟨_, by omega, out, hall, hall.runFuel_eq, hw, hb, hd, hwall, hrall⟩

/-- The NEG child returns to the next bounded cursor, charging both control transitions. -/
theorem run_neg (code : Code) (q : Word) (x dst : Fin 8)
    (r : Registers) (input : Inputs) (flags : Flags)
    (rest : List ArithmeticMachine.Instruction) (hcode : code.val = .neg x dst :: rest)
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    ∃ n ≤ 16 * q.length + 32, ∃ out,
      Trace n (.ready code q r input flags)
        (.ready (tailCode code) q (Function.update r dst out) input flags) ∧
      runFuel n (.ready code q r input flags) =
        .ready (tailCode code) q (Function.update r dst out) input flags ∧
      out.length = q.length ∧ value out < value q ∧
      QuadraticArithmeticBitNeg.decodeRegisters q (Function.update r dst out) =
        Function.update (QuadraticArithmeticBitNeg.decodeRegisters q r) dst
          (-QuadraticArithmeticBitNeg.decodeRegisters q r x) ∧
      (∀ i, (Function.update r dst out i).length = q.length) ∧
      (∀ i, value (Function.update r dst out i) < value q) := by
  obtain ⟨n, hn, out, ht, _, hw, hb, hd, hwall, hrall⟩ :=
    QuadraticArithmeticBitNeg.neg_execution q x dst r hwidth hred
  have hi := dispatch_trace code q r input flags (.neg x dst) rest hcode
  have ho : Trace 1 (.neg (tailCode code) input flags
      (.done q (Function.update r dst out)))
      (.ready (tailCode code) q (Function.update r dst out) input flags) := .cons rfl (.nil _)
  have hall := (hi.append (lift_neg (tailCode code) input flags ht)).append ho
  exact ⟨_, by omega, out, hall, hall.runFuel_eq, hw, hb, hd, hwall, hrall⟩

/-- The INV child returns to the next bounded cursor, charging both control transitions. -/
theorem run_inv (code : Code) (q : Word) (hp : Nat.Prime (value q)) (x dst : Fin 8)
    (r : Registers) (input : Inputs) (flags : Flags)
    (rest : List ArithmeticMachine.Instruction) (hcode : code.val = .inv x dst :: rest)
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    ∃ n ≤ value q * (value q * (24 * q.length + 48) + 16 * q.length + 32) +
      13 * q.length + 26, ∃ out,
      Trace n (.ready code q r input flags)
        (.ready (tailCode code) q (Function.update r dst out) input flags) ∧
      runFuel n (.ready code q r input flags) =
        .ready (tailCode code) q (Function.update r dst out) input flags ∧
      out.length = q.length ∧ value out < value q ∧
      QuadraticArithmeticBitInv.decodeRegisters q (Function.update r dst out) =
        Function.update (QuadraticArithmeticBitInv.decodeRegisters q r) dst
          ((QuadraticArithmeticBitInv.decodeRegisters q r x)⁻¹) ∧
      (∀ i, (Function.update r dst out i).length = q.length) ∧
      (∀ i, value (Function.update r dst out i) < value q) := by
  obtain ⟨n, hn, out, ht, _, hw, hb, hd, hwall, hrall⟩ :=
    QuadraticArithmeticBitInv.inv_execution q hp x dst r hwidth hred
  have hi := dispatch_trace code q r input flags (.inv x dst) rest hcode
  have ho : Trace 1 (.inv (tailCode code) input flags
      (.done q (Function.update r dst out)))
      (.ready (tailCode code) q (Function.update r dst out) input flags) := .cons rfl (.nil _)
  have hall := (hi.append (lift_inv (tailCode code) input flags ht)).append ho
  exact ⟨_, by omega, out, hall, hall.runFuel_eq, hw, hb, hd, hwall, hrall⟩

/-- LOAD includes clearing an arbitrary old destination and returning to the next cursor. -/
theorem run_load (code : Code) (q : Word) (source : ArithmeticMachine.Source) (dst : Fin 8)
    (r : Registers) (input : Inputs) (flags : Flags)
    (rest : List ArithmeticMachine.Instruction) (hcode : code.val = .load source dst :: rest) :
    Trace ((r dst).length + 2 * (input (QuadraticArithmeticBitLoad.sourceIndex source)).length + 7)
      (.ready code q r input flags)
      (.ready (tailCode code) q
        (Function.update r dst (input (QuadraticArithmeticBitLoad.sourceIndex source)))
        input flags) := by
  have hi := dispatch_trace code q r input flags (.load source dst) rest hcode
  have hc := lift_load (tailCode code) flags
    (QuadraticArithmeticBitLoad.load_trace q
      (QuadraticArithmeticBitLoad.sourceIndex source) dst r input)
  have ho : Trace 1 (.load (tailCode code) flags
      (.done q (Function.update r dst
        (input (QuadraticArithmeticBitLoad.sourceIndex source))) input))
      (.ready (tailCode code) q (Function.update r dst
        (input (QuadraticArithmeticBitLoad.sourceIndex source))) input flags) := .cons rfl (.nil _)
  convert (hi.append hc).append ho using 1
  all_goals omega

/-- EQUAL adopts the newly written flag in the controller's next ready state. -/
theorem run_equal (code : Code) (q : Word) (x y : Fin 8) (dst : Fin 2)
    (r : Registers) (input : Inputs) (flags : Flags)
    (rest : List ArithmeticMachine.Instruction) (hcode : code.val = .equal x y dst :: rest)
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    let result := decide (QuadraticArithmeticBitEqual.decodeRegisters q r x =
      QuadraticArithmeticBitEqual.decodeRegisters q r y)
    Trace (5 * q.length + 17) (.ready code q r input flags)
      (.ready (tailCode code) q r input (Function.update flags dst result)) := by
  dsimp only
  have hi := dispatch_trace code q r input flags (.equal x y dst) rest hcode
  have hc := lift_equal (tailCode code) input flags
    (QuadraticArithmeticBitEqual.equal_execution q x y dst r hwidth hred).1
  have ho : Trace 1 (.equal (tailCode code) input flags
      (.done q r dst (decide (QuadraticArithmeticBitEqual.decodeRegisters q r x =
        QuadraticArithmeticBitEqual.decodeRegisters q r y))))
      (.ready (tailCode code) q r input (Function.update flags dst
        (decide (QuadraticArithmeticBitEqual.decodeRegisters q r x =
          QuadraticArithmeticBitEqual.decodeRegisters q r y)))) := .cons rfl (.nil _)
  convert (hi.append hc).append ho using 1
  all_goals omega

/-- PAIR dispatches and terminates with the two physical output words. -/
theorem run_pair (code : Code) (q : Word) (x y : Fin 8)
    (r : Registers) (input : Inputs) (flags : Flags)
    (rest : List ArithmeticMachine.Instruction) (hcode : code.val = .pair x y :: rest) :
    Trace (2 * (r x).length + 2 * (r y).length + 10) (.ready code q r input flags)
      (.pair input flags (.done q r (r x) (r y))) := by
  have hi := dispatch_trace code q r input flags (.pair x y) rest hcode
  have hc := lift_pair input flags (QuadraticArithmeticBitPair.pair_trace q x y r)
  convert hi.append hc using 1
  omega

/-- BOOLEAN dispatches and writes the actual conjunction bit in exactly two transitions. -/
theorem run_boolean (code : Code) (q : Word) (r : Registers) (input : Inputs) (flags : Flags)
    (rest : List ArithmeticMachine.Instruction) (hcode : code.val = .boolean :: rest) :
    Trace 2 (.ready code q r input flags)
      (.boolean input (.done q r flags (flags 0 && flags 1))) := by
  exact (dispatch_trace code q r input flags .boolean rest hcode).append
    (lift_boolean input (QuadraticArithmeticBitBoolean.boolean_trace q r flags))

end Computation.QuadraticArithmeticBitProgram
