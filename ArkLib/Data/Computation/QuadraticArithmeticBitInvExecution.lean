/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticArithmeticBitInv
public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine

/-!
# Actual INV instruction refinement with all register aliases

The same physical execution realizes the existing arithmetic machine's INV clause. Its bound
includes loading the operand, overwriting the old destination, and clearing the result copy.
The five immutable inputs, two flags and RAM are retained. Register initialization and the other
instruction forms remain separate obligations. This is one proved instruction.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitInv

open BinaryWordMachine (Word value)

theorem lift_load (q : Word) (x dst : Register) (r : Registers) {n : ℕ}
    {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.loading q x dst r s) (.loading q x dst r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_inv (dst : Register) (r : Registers) {n : ℕ}
    {s t : PaddedInverse.Control} (h : PaddedInverse.Trace n s t) :
    Trace n (.inverting dst r s) (.inverting dst r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_store (q : Word) (dst : Register) (r : Registers) {n : ℕ}
    {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.storing q dst r s) (.storing q dst r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- The actual operand is copied and restored before the possibly aliased destination is touched. -/
theorem load_trace (q : Word) (x dst : Register) (r : Registers) :
    Trace (2 * (r x).length + 5) (.start q x dst r)
      (.inverting dst r (.inverting (.start q (r x)))) := by
  have hi : Trace 1 (.start q x dst r)
      (.loading q x dst (Function.update r x []) (.clear (r x) [])) := .cons rfl (.nil _)
  have hl := lift_load q x dst (Function.update r x [])
    (WordCopyMachine.copy_correct (r x) []).1
  have ho : Trace 1 (.loading q x dst (Function.update r x []) (.done (r x) (r x)))
      (.inverting dst r (.inverting (.start q (r x)))) :=
    .cons (by simp [step, WordCopyMachine.step]) (.nil _)
  convert (hi.append hl).append ho using 1
  simp only [List.length_nil]
  omega

theorem clear_trace (q : Word) (r : Registers) (word : Word) :
    Trace (word.length + 1) (.clearing q r word) (.done q r) := by
  induction word with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih => exact .cons rfl ih

/-- The retained inverse operand is explicitly cleared before result write-back. -/
theorem clearInput_trace (q : Word) (dst : Register) (r : Registers) (out operand : Word) :
    Trace (operand.length + 1) (.clearInput q dst r out operand)
      (.storing q dst (Function.update r dst []) (.clear out (r dst))) := by
  induction operand with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih => exact .cons rfl ih

/-- The actual retained operand and result temporaries are both destroyed at charged cost. -/
theorem store_trace (q : Word) (dst : Register) (r : Registers) (out operand : Word) :
    Trace (operand.length + (r dst).length + 3 * out.length + 7)
      (.inverting dst r (.padding operand (.padding q (.done out))))
      (.done q (Function.update r dst out)) := by
  have hi : Trace 1 (.inverting dst r (.padding operand (.padding q (.done out))))
      (.clearInput q dst r out operand) := .cons rfl (.nil _)
  have hr := clearInput_trace q dst r out operand
  have hs := lift_store q dst (Function.update r dst [])
    (WordCopyMachine.copy_correct out (r dst)).1
  have hh : Trace 1 (.storing q dst (Function.update r dst []) (.done out out))
      (.clearing q (Function.update r dst out) out) :=
    .cons (by simp [step, WordCopyMachine.step]) (.nil _)
  have hc := clear_trace q (Function.update r dst out) out
  convert (((hi.append hr).append hs).append hh).append hc using 1
  omega

/-- The decoded register bank is a mathematical relation, not a runtime encoding operation. -/
def decodeRegisters (q : Word) (r : Registers) : Register → ZMod (value q) :=
  fun i ↦ value (r i)

/-- All aliases obey the same actual trace, with no assumed register assignment cost. -/
theorem inv_execution (q : Word) (hp : Nat.Prime (value q)) (x dst : Register) (r : Registers)
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    ∃ n ≤ value q * (value q * (24 * q.length + 48) + 16 * q.length + 32) +
      13 * q.length + 24, ∃ out,
      Trace n (.start q x dst r) (.done q (Function.update r dst out)) ∧
      runFuel n (.start q x dst r) = .done q (Function.update r dst out) ∧
      out.length = q.length ∧ value out < value q ∧
      decodeRegisters q (Function.update r dst out) =
        Function.update (decodeRegisters q r) dst ((decodeRegisters q r x)⁻¹) ∧
      (∀ i, (Function.update r dst out i).length = q.length) ∧
      (∀ i, value (Function.update r dst out i) < value q) := by
  have hl := load_trace q x dst r
  obtain ⟨na, hna, out, ha, _hra, hw, hv, hb⟩ :=
    PaddedInverse.inverse_fixed_width q (r x) hp (hred x) (hwidth x)
  have hs := store_trace q dst r out (r x)
  have hall := (hl.append (lift_inv dst r ha)).append hs
  refine ⟨_, ?_, out, hall, hall.runFuel_eq, hw, hb, ?_, ?_, ?_⟩
  · simp only [hwidth, hw]
    omega
  · funext i
    by_cases hi : i = dst
    · subst i
      simpa [decodeRegisters] using hv
    · simp [decodeRegisters, Function.update_of_ne hi]
  · intro i
    by_cases hi : i = dst
    · subst i; simpa using hw
    · simpa [Function.update_of_ne hi] using hwidth i
  · intro i
    by_cases hi : i = dst
    · subst i; simpa using hb
    · simpa [Function.update_of_ne hi] using hred i

/-- Decode the five retained input tapes in the existing source machine's order. -/
def decodeInput (q : Word) (input : Fin 5 → Word) :
    QuadraticAlgebra.ArithmeticMachine.Input (ZMod (value q)) :=
  ⟨value (input 4), (value (input 0), value (input 1)), (value (input 2), value (input 3))⟩

/-- One bit run refines the INV successor and retains the other physical state. -/
theorem source_execution (mem : AddressedBits.Memory) (q : Word)
    (input : Fin 5 → Word) (flags : Fin 2 → Bool)
    (x dst : Register) (r : Registers)
    (rest : List QuadraticAlgebra.ArithmeticMachine.Instruction)
    [Fact (Nat.Prime (value q))]
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    ∃ n ≤ value q * (value q * (24 * q.length + 48) + 16 * q.length + 32) +
      13 * q.length + 24, ∃ out,
      Trace n (.start q x dst r) (.done q (Function.update r dst out)) ∧
      ramRunFuel n ⟨mem, input, flags, .start q x dst r⟩ =
        ⟨mem, input, flags, .done q (Function.update r dst out)⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      QuadraticAlgebra.ArithmeticMachine.step (decodeInput q input)
        (.running (.inv x dst :: rest) (decodeRegisters q r) flags) =
        some (.running rest (decodeRegisters q (Function.update r dst out)) flags,
          QuadraticAlgebra.ArithmeticMachine.instructionCost (.inv x dst)) := by
  obtain ⟨n, hn, out, ht, hf, hw, hb, hd, _hw, _hb⟩ := inv_execution q Fact.out x dst r hwidth hred
  refine ⟨n, hn, out, ht, ?_, hw, hb, ?_⟩
  · rw [ramRunFuel_eq, hf]
  · rw [QuadraticAlgebra.ArithmeticMachine.step, QuadraticAlgebra.ArithmeticMachine.execute, hd]

end Computation.QuadraticArithmeticBitInv
