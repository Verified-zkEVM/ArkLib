/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.WordCopyMachine
public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine
public import ArkLib.Data.Computation.BinaryWordSemantics

/-!
# Actual loads from the five immutable scalar inputs

The selected input tape and destination register are distinct physical positions. The copy child
clears the old destination, copies the source and restores it. The active source/destination are
removed from their inactive frames and represented only by the child's tapes. All other words,
RAM, modulus and both flags stay on the same fixed bank. All five source selectors are finite.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitLoad

open BinaryWordMachine (Word value)
abbrev Registers := Fin 8 → Word
abbrev Inputs := Fin 5 → Word
abbrev Slot := Fin 13 ⊕ (Fin 8 ⊕ (Fin 5 ⊕ Fin 2))

inductive Control where
  | start (q : Word) (src : Fin 5) (dst : Fin 8) (r : Registers) (input : Inputs)
  | copying (q : Word) (src : Fin 5) (dst : Fin 8) (r : Registers) (input : Inputs)
      (child : WordCopyMachine.Control)
  | done (q : Word) (r : Registers) (input : Inputs)

def step : Control → Option Control
  | .start q src dst r input =>
      some (.copying q src dst (Function.update r dst []) (Function.update input src [])
        (.clear (input src) (r dst)))
  | .copying q src dst r input child =>
      match WordCopyMachine.step child with
      | some next => some (.copying q src dst r input next)
      | none => match child with
          | .done source out =>
              some (.done q (Function.update r dst out) (Function.update input src source))
          | _ => none
  | .done _ _ _ => none

def work : Control → Fin 13 → Word
  | .start q _ _ _ _ | .done q _ _ =>
      ![[], [], [], [], q, [], [], [], [], [], [], [], []]
  | .copying q _ _ _ _ child =>
      ![[], [], WordCopyMachine.tapes child 1, [], q, [], [], [], [], [], [], [], []]

def registers : Control → Registers
  | .start _ _ _ r _ | .done _ r _ => r
  | .copying _ _ dst r _ child => Function.update r dst (WordCopyMachine.tapes child 2)

def inputs : Control → Inputs
  | .start _ _ _ _ input | .done _ _ input => input
  | .copying _ src _ _ input child => Function.update input src (WordCopyMachine.tapes child 0)

def tapes (flags : Fin 2 → Bool) (s : Control) : Slot → Word
  | .inl i => work s i
  | .inr (.inl i) => registers s i
  | .inr (.inr (.inl i)) => inputs s i
  | .inr (.inr (.inr i)) => [flags i]

private theorem update_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → Word) (i : ι) {a b : Word} (h : BitLocalActions.CellStep a b) :
    BitLocalActions.BankStep (Function.update r i a) (Function.update r i b) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using h
  · simp only [Function.update_of_ne hj]; exact .keep _

/-- Copy ownership handoffs and every bit action obey the same twenty-eight-tape rule. -/
theorem step_local {s t : Control} (h : step s = some t) (flags : Fin 2 → Bool) :
    BitLocalActions.BankStep (tapes flags s) (tapes flags t) := by
  cases s with
  | start q src dst r input =>
      cases h
      intro i
      rcases i with i | i
      · fin_cases i <;> exact .keep _
      · rcases i with i | i
        · simpa [tapes, registers, WordCopyMachine.tapes] using
            (BitLocalActions.CellStep.keep (r i))
        · rcases i with i | i
          · simpa [tapes, inputs, WordCopyMachine.tapes] using
              (BitLocalActions.CellStep.keep (input i))
          · exact .keep _
  | copying q src dst r input child =>
      cases hs : WordCopyMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := WordCopyMachine.step_local hs
          intro i
          rcases i with i | i
          · fin_cases i
            · exact .keep _
            · exact .keep _
            · exact hl 1
            all_goals exact .keep _
          · rcases i with i | i
            · exact update_local r dst (hl 2) i
            · rcases i with i | i
              · exact update_local input src (hl 0) i
              · exact .keep _
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          intro i
          rcases i with i | i
          · fin_cases i <;> exact .keep _
          · rcases i with i | i
            · exact .keep _
            · cases i <;> exact .keep _
  | done _ _ _ => cases h

inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

def runFuel : ℕ → Control → Control
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem Trace.append {n m : ℕ} {s u t : Control}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_eq {n : ℕ} {s t : Control} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

theorem lift_copy (q : Word) (src : Fin 5) (dst : Fin 8) (r : Registers) (input : Inputs)
    {n : ℕ} {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.copying q src dst r input s) (.copying q src dst r input t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Exact bit count includes the old destination, two source passes, and all control handoffs. -/
theorem load_trace (q : Word) (src : Fin 5) (dst : Fin 8) (r : Registers) (input : Inputs) :
    Trace ((r dst).length + 2 * (input src).length + 5) (.start q src dst r input)
      (.done q (Function.update r dst (input src)) input) := by
  have hi : Trace 1 (.start q src dst r input)
      (.copying q src dst (Function.update r dst []) (Function.update input src [])
        (.clear (input src) (r dst))) := .cons rfl (.nil _)
  have hc := lift_copy q src dst (Function.update r dst []) (Function.update input src [])
    (WordCopyMachine.copy_correct (input src) (r dst)).1
  have ho : Trace 1
      (.copying q src dst (Function.update r dst []) (Function.update input src [])
        (.done (input src) (input src)))
      (.done q (Function.update r dst (input src)) input) :=
    .cons (by simp [step, WordCopyMachine.step]) (.nil _)
  convert (hi.append hc).append ho using 1
  omega

/-- Fixed-width source and destination give a linear same-trace loading count. -/
theorem load_fixed_width (q : Word) (src : Fin 5) (dst : Fin 8) (r : Registers) (input : Inputs)
    (hr : (r dst).length = q.length) (hi : (input src).length = q.length) :
    Trace (3 * q.length + 5) (.start q src dst r input)
      (.done q (Function.update r dst (input src)) input) := by
  convert load_trace q src dst r input using 1
  rw [hr, hi]
  omega

structure Configuration where
  memory : AddressedBits.Memory
  flags : Fin 2 → Bool
  control : Control

def ramStep (s : Configuration) : Option Configuration :=
  (step s.control).map fun next ↦ { s with control := next }

def ramRunFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match ramStep s with
      | none => s
      | some t => ramRunFuel n t

theorem ramRunFuel_eq (s : Configuration) (n : ℕ) :
    ramRunFuel n s = { s with control := runFuel n s.control } := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => cases hs : step s.control <;> simp [ramRunFuel, ramStep, runFuel, hs, ih]

/-- Literal finite input-selector wiring, in the order of the existing source machine. -/
def sourceIndex : QuadraticAlgebra.ArithmeticMachine.Source → Fin 5
  | .leftRe => 0
  | .leftIm => 1
  | .rightRe => 2
  | .rightIm => 3
  | .parameter => 4

def decodeRegisters (q : Word) (r : Registers) : Fin 8 → ZMod (value q) := fun i ↦ value (r i)

def decodeInput (q : Word) (input : Inputs) :
    QuadraticAlgebra.ArithmeticMachine.Input (ZMod (value q)) :=
  ⟨value (input 4), (value (input 0), value (input 1)), (value (input 2), value (input 3))⟩

/-- All five LOAD clauses run on the same retained inputs and RAM. -/
theorem source_execution (mem : AddressedBits.Memory) (q : Word) (flags : Fin 2 → Bool)
    (source : QuadraticAlgebra.ArithmeticMachine.Source) (dst : Fin 8)
    (r : Registers) (input : Inputs) (rest : List QuadraticAlgebra.ArithmeticMachine.Instruction)
    [Fact (Nat.Prime (value q))] :
    let n := (r dst).length + 2 * (input (sourceIndex source)).length + 5
    let out := Function.update r dst (input (sourceIndex source))
    Trace n (.start q (sourceIndex source) dst r input) (.done q out input) ∧
      ramRunFuel n ⟨mem, flags, .start q (sourceIndex source) dst r input⟩ =
        ⟨mem, flags, .done q out input⟩ ∧
      QuadraticAlgebra.ArithmeticMachine.step (decodeInput q input)
        (.running (.load source dst :: rest) (decodeRegisters q r) flags) =
        some (.running rest (decodeRegisters q out) flags,
          QuadraticAlgebra.ArithmeticMachine.instructionCost (.load source dst)) := by
  have ht := load_trace q (sourceIndex source) dst r input
  refine ⟨ht, ?_, ?_⟩
  · rw [ramRunFuel_eq, ht.runFuel_eq]
  · have hd : decodeRegisters q (Function.update r dst (input (sourceIndex source))) =
        Function.update (decodeRegisters q r) dst
          (QuadraticAlgebra.ArithmeticMachine.readSource (decodeInput q input) source) := by
      funext i
      by_cases hi : i = dst
      · subst i
        cases source <;> simp [decodeRegisters, decodeInput, sourceIndex,
          QuadraticAlgebra.ArithmeticMachine.readSource]
      · simp [decodeRegisters, Function.update_of_ne hi]
    rw [QuadraticAlgebra.ArithmeticMachine.step, QuadraticAlgebra.ArithmeticMachine.execute, hd]

end Computation.QuadraticArithmeticBitLoad
