/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticArithmeticBitEqual
public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine

/-!
# Actual scalar-register equality and physical flag write

Two retained operand copies feed the literal equality child. Its Boolean result is written to
the selected flag tape by two actual transitions. The final flag view and the existing source
EQUAL successor agree on the same bounded run. All scalar words, five inputs and RAM are retained.
The configuration's `flags` field is the finite input frame; `resultFlags` reads the final bank.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitEqual

open BinaryWordMachine (Word value)

theorem lift_left (q : Word) (x y : Register) (dst : Fin 2) (r : Registers) {n : ℕ}
    {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.left q x y dst r s) (.left q x y dst r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_right (q : Word) (y : Register) (dst : Fin 2) (r : Registers) (left : Word) {n : ℕ}
    {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.right q y dst r left s) (.right q y dst r left t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_compare (dst : Fin 2) (r : Registers) {n : ℕ}
    {s t : BinaryEqualMachine.Configuration} (h : BinaryEqualMachine.Trace n s t) :
    Trace n (.comparing dst r s) (.comparing dst r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Both operands are copied before overwriting the destination, even when indices alias. -/
theorem load_trace (q : Word) (x y : Register) (dst : Fin 2) (r : Registers) :
    Trace (2 * (r x).length + 2 * (r y).length + 9) (.start q x y dst r)
      (.comparing dst r (.compare q (.startCompare (r x) (r y)))) := by
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
      (.comparing dst r (.compare q (.startCompare (r x) (r y)))) :=
    .cons (by simp [step, WordCopyMachine.step]) (.nil _)
  convert (((hi.append hl).append hh).append hr).append ho using 1
  simp only [List.length_nil]
  omega

/-- Both old-flag destruction and result-bit creation are included in this three-step handoff. -/
theorem write_flag_trace (q : Word) (r : Registers) (dst : Fin 2) (result : Bool) :
    Trace 3 (.comparing dst r (.done q result)) (.done q r dst result) :=
  .cons rfl (.cons rfl (.cons rfl (.nil _)))

def decodeRegisters (q : Word) (r : Registers) : Register → ZMod (value q) :=
  fun i ↦ value (r i)

/-- Source equality is observed in the final physical flag; all source scalar registers remain. -/
theorem equal_execution (q : Word) (x y : Register) (dst : Fin 2) (r : Registers)
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    let result := decide (decodeRegisters q r x = decodeRegisters q r y)
    Trace (5 * q.length + 15) (.start q x y dst r) (.done q r dst result) ∧
      runFuel (5 * q.length + 15) (.start q x y dst r) = .done q r dst result := by
  have hl := load_trace q x y dst r
  have hc := lift_compare dst r (BinaryEqualMachine.equality_zmod q (r x) (r y)
    (hred x) (hred y)).1
  have hw := write_flag_trace q r dst (decide (decodeRegisters q r x = decodeRegisters q r y))
  have ht : Trace (5 * q.length + 15) (.start q x y dst r)
      (.done q r dst (decide (decodeRegisters q r x = decodeRegisters q r y))) := by
    convert (hl.append hc).append hw using 1
    simp only [hwidth, max_self]
    omega
  exact ⟨ht, ht.runFuel_eq⟩

/-- The terminal finite observation is exactly the bit physically stored on each flag tape. -/
theorem final_flag_words (flags : Fin 2 → Bool) (q : Word) (r : Registers)
    (dst : Fin 2) (result : Bool) :
    flagWords flags (.done q r dst result) =
      fun i ↦ [resultFlags flags (.done q r dst result) i] := by
  funext i
  by_cases hi : i = dst
  · subst i; simp [flagWords, resultFlags]
  · simp [flagWords, resultFlags, Function.update_of_ne hi]

def decodeInput (q : Word) (input : Fin 5 → Word) :
    QuadraticAlgebra.ArithmeticMachine.Input (ZMod (value q)) :=
  ⟨value (input 4), (value (input 0), value (input 1)), (value (input 2), value (input 3))⟩

/-- The source EQUAL successor matches the actual final flag bank, including its other old flag. -/
theorem source_execution (mem : AddressedBits.Memory) (q : Word)
    (input : Fin 5 → Word) (flags : Fin 2 → Bool)
    (x y : Register) (dst : Fin 2) (r : Registers)
    (rest : List QuadraticAlgebra.ArithmeticMachine.Instruction) [Fact (Nat.Prime (value q))]
    (hwidth : ∀ i, (r i).length = q.length) (hred : ∀ i, value (r i) < value q) :
    let result := decide (decodeRegisters q r x = decodeRegisters q r y)
    Trace (5 * q.length + 15) (.start q x y dst r) (.done q r dst result) ∧
      ramRunFuel (5 * q.length + 15) ⟨mem, input, flags, .start q x y dst r⟩ =
        ⟨mem, input, flags, .done q r dst result⟩ ∧
      QuadraticAlgebra.ArithmeticMachine.step (decodeInput q input)
        (.running (.equal x y dst :: rest) (decodeRegisters q r) flags) =
        some (.running rest (decodeRegisters q r) (resultFlags flags (.done q r dst result)),
          QuadraticAlgebra.ArithmeticMachine.instructionCost (.equal x y dst)) := by
  obtain ⟨ht, hf⟩ := equal_execution q x y dst r hwidth hred
  refine ⟨ht, ?_, ?_⟩
  · rw [ramRunFuel_eq, hf]
  · rfl

end Computation.QuadraticArithmeticBitEqual
