/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticArithmeticBitAdd
public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine

/-!
# Actual ADD instruction refinement with all register aliases

The same physical execution realizes the existing arithmetic machine's ADD clause. Its bound
includes loading both operands, overwriting the old destination, and clearing the result copy.
The five immutable inputs, two flags and RAM are retained. Register initialization and the other
instruction forms remain separate obligations. This is one proved instruction.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitAdd

open BinaryWordMachine (Word value)

theorem lift_left (q : Word) (x y dst : Register) (r : Registers) {n : ℕ}
    {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.left q x y dst r s) (.left q x y dst r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_right (q : Word) (y dst : Register) (r : Registers) (left : Word) {n : ℕ}
    {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.right q y dst r left s) (.right q y dst r left t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_add (dst : Register) (r : Registers) {n : ℕ}
    {s t : PaddedModAdd.Control} (h : PaddedModAdd.Trace n s t) :
    Trace n (.adding dst r s) (.adding dst r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_store (q : Word) (dst : Register) (r : Registers) {n : ℕ}
    {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.storing q dst r s) (.storing q dst r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Both operands are copied before overwriting the destination, even when indices alias. -/
theorem load_trace (q : Word) (x y dst : Register) (r : Registers) :
    Trace (2 * (r x).length + 2 * (r y).length + 9) (.start q x y dst r)
      (.adding dst r (.adding (.start q (r x) (r y)))) := by
  have hi : Trace 1 (.start q x y dst r)
      (.left q x y dst (Function.update r x []) (.clear (r x) [])) := .cons rfl (.nil _)
  have hl := lift_left q x y dst (Function.update r x [])
    (WordCopyMachine.copy_correct (r x) []).1
  have hh : Trace 1 (.left q x y dst (Function.update r x []) (.done (r x) (r x)))
      (.right q y dst (Function.update r y []) (r x) (.clear (r y) [])) :=
    .cons (by simp [step, WordCopyMachine.step]) (.nil _)
  have hr := lift_right q y dst (Function.update r y []) (r x)
    (WordCopyMachine.copy_correct (r y) []).1
  have ho : Trace 1 (.right q y dst (Function.update r y []) (r x) (.done (r y) (r y)))
      (.adding dst r (.adding (.start q (r x) (r y)))) :=
    .cons (by simp [step, WordCopyMachine.step]) (.nil _)
  convert (((hi.append hl).append hh).append hr).append ho using 1
  simp only [List.length_nil]
  omega

theorem clear_trace (q : Word) (r : Registers) (word : Word) :
    Trace (word.length + 1) (.clearing q r word) (.done q r) := by
  induction word with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih => exact .cons rfl ih

/-- The actual result overwrites the physical destination, then its temporary copy is destroyed. -/
theorem store_trace (q : Word) (dst : Register) (r : Registers) (out : Word) :
    Trace ((r dst).length + 3 * out.length + 6)
      (.adding dst r (.padding (.padding q (.done out))))
      (.done q (Function.update r dst out)) := by
  have hi : Trace 1 (.adding dst r (.padding (.padding q (.done out))))
      (.storing q dst (Function.update r dst []) (.clear out (r dst))) := .cons rfl (.nil _)
  have hs := lift_store q dst (Function.update r dst [])
    (WordCopyMachine.copy_correct out (r dst)).1
  have hh : Trace 1 (.storing q dst (Function.update r dst []) (.done out out))
      (.clearing q (Function.update r dst out) out) :=
    .cons (by simp [step, WordCopyMachine.step]) (.nil _)
  have hc := clear_trace q (Function.update r dst out) out
  convert ((hi.append hs).append hh).append hc using 1
  omega

/-- The decoded register bank is a mathematical relation, not a runtime encoding operation. -/
def decodeRegisters (q : Word) (r : Registers) : Register → ZMod (value q) :=
  fun i ↦ value (r i)

/-- All aliases obey the same actual trace, with no assumed register assignment cost. -/
theorem add_execution (q : Word) (x y dst : Register) (r : Registers)
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    ∃ n ≤ 22 * q.length + 48, ∃ out,
      Trace n (.start q x y dst r) (.done q (Function.update r dst out)) ∧
      runFuel n (.start q x y dst r) = .done q (Function.update r dst out) ∧
      out.length = q.length ∧ value out < value q ∧
      decodeRegisters q (Function.update r dst out) =
        Function.update (decodeRegisters q r) dst (decodeRegisters q r x + decodeRegisters q r y) ∧
      (∀ i, (Function.update r dst out i).length = q.length) ∧
      (∀ i, value (Function.update r dst out i) < value q) := by
  have hl := load_trace q x y dst r
  obtain ⟨na, hna, out, ha, _hra, hw, hv, hb⟩ :=
    PaddedModAdd.add_fixed_width q (r x) (r y) (hred x) (hred y) (hwidth x) (hwidth y)
  have hs := store_trace q dst r out
  have hall := (hl.append (lift_add dst r ha)).append hs
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

/-- One bit run refines the ADD successor and retains the other physical state. -/
theorem source_execution (mem : AddressedBits.Memory) (q : Word)
    (input : Fin 5 → Word) (flags : Fin 2 → Bool)
    (x y dst : Register) (r : Registers)
    (rest : List QuadraticAlgebra.ArithmeticMachine.Instruction)
    [Fact (Nat.Prime (value q))]
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    ∃ n ≤ 22 * q.length + 48, ∃ out,
      Trace n (.start q x y dst r) (.done q (Function.update r dst out)) ∧
      ramRunFuel n ⟨mem, input, flags, .start q x y dst r⟩ =
        ⟨mem, input, flags, .done q (Function.update r dst out)⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      QuadraticAlgebra.ArithmeticMachine.step (decodeInput q input)
        (.running (.add x y dst :: rest) (decodeRegisters q r) flags) =
        some (.running rest (decodeRegisters q (Function.update r dst out)) flags,
          QuadraticAlgebra.ArithmeticMachine.instructionCost (.add x y dst)) := by
  obtain ⟨n, hn, out, ht, hf, hw, hb, hd, _hw, _hb⟩ := add_execution q x y dst r hwidth hred
  refine ⟨n, hn, out, ht, ?_, hw, hb, ?_⟩
  · rw [ramRunFuel_eq, hf]
  · rw [QuadraticAlgebra.ArithmeticMachine.step, QuadraticAlgebra.ArithmeticMachine.execute, hd]

end Computation.QuadraticArithmeticBitAdd
