/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticArithmeticBitPair

/-!
# Literal Boolean conjunction and one-bit emission

The two physical flag bits select a finite Boolean conjunction. One successor pushes that bit
onto initially empty output tape zero. All eight scalar registers, five immutable inputs, the
modulus, both flags and RAM are retained. This is a closed finite-bit output instruction.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitBoolean

open BinaryWordMachine (Word value)
abbrev Registers := Fin 8 → Word
abbrev Slot := Fin 13 ⊕ (Fin 8 ⊕ (Fin 5 ⊕ Fin 2))

inductive Control where
  | start (q : Word) (r : Registers) (flags : Fin 2 → Bool)
  | done (q : Word) (r : Registers) (flags : Fin 2 → Bool) (result : Bool)

def step : Control → Option Control
  | .start q r flags => some (.done q r flags (flags 0 && flags 1))
  | .done _ _ _ _ => none

def work : Control → Fin 13 → Word
  | .start q _ _ => ![[], [], [], [], q, [], [], [], [], [], [], [], []]
  | .done q _ _ result => ![[result], [], [], [], q, [], [], [], [], [], [], [], []]

def registers : Control → Registers
  | .start _ r _ | .done _ r _ _ => r

def flags : Control → Fin 2 → Bool
  | .start _ _ b | .done _ _ b _ => b

def tapes (input : Fin 5 → Word) (s : Control) : Slot → Word
  | .inl i => work s i
  | .inr (.inl i) => registers s i
  | .inr (.inr (.inl i)) => input i
  | .inr (.inr (.inr i)) => [flags s i]

/-- The only new bit is the emitted conjunction; every other physical tape is kept. -/
theorem step_local {s t : Control} (h : step s = some t) (input : Fin 5 → Word) :
    BitLocalActions.BankStep (tapes input s) (tapes input t) := by
  cases s with
  | start q r b =>
      cases h
      intro i
      rcases i with i | i
      · fin_cases i
        · exact .push _ _
        all_goals exact .keep _
      · rcases i with i | i
        · exact .keep _
        · cases i <;> exact .keep _
  | done _ _ _ _ => cases h

inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

def runFuel : ℕ → Control → Control
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem boolean_trace (q : Word) (r : Registers) (b : Fin 2 → Bool) :
    Trace 1 (.start q r b) (.done q r b (b 0 && b 1)) := .cons rfl (.nil _)

structure Configuration where
  memory : AddressedBits.Memory
  input : Fin 5 → Word
  control : Control

def ramStep (s : Configuration) : Option Configuration :=
  (step s.control).map fun next ↦ { s with control := next }

def ramRunFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match ramStep s with
      | none => s
      | some t => ramRunFuel n t

/-- The actual emitted bit agrees with the source BOOLEAN successor and its stated charge. -/
theorem source_execution (mem : AddressedBits.Memory) (q : Word)
    (input : Fin 5 → Word) (b : Fin 2 → Bool) (r : Registers)
    (rest : List QuadraticAlgebra.ArithmeticMachine.Instruction) [Fact (Nat.Prime (value q))] :
    Trace 1 (.start q r b) (.done q r b (b 0 && b 1)) ∧
      ramRunFuel 1 ⟨mem, input, .start q r b⟩ = ⟨mem, input, .done q r b (b 0 && b 1)⟩ ∧
      QuadraticAlgebra.ArithmeticMachine.step (QuadraticArithmeticBitPair.decodeInput q input)
        (.running (.boolean :: rest) (QuadraticArithmeticBitPair.decodeRegisters q r) b) =
        some (.done (.boolean (b 0 && b 1)),
          QuadraticAlgebra.ArithmeticMachine.instructionCost .boolean) :=
  ⟨boolean_trace q r b, rfl, rfl⟩

end Computation.QuadraticArithmeticBitBoolean
