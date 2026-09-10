/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryWordMachine

/-!
# Literal equality guard retaining its modulus

The actual binary comparison consumes both supplied words. One finite-control transition maps
its resulting ordering to a Boolean guard. The modulus stays on a fifth physical tape throughout.
There is no extra entry transition: the initial state contains the original comparison entry.
-/

@[expose] public section

namespace Computation.BinaryEqualMachine

open BinaryWordMachine (Word)

/-- Finite Boolean branch on the comparison controller's final ordering. -/
def orderEq : Ordering → Bool
  | .eq => true
  | _ => false

inductive Configuration where
  | compare (modulus : Word) (state : BinaryWordMachine.Configuration)
  | done (modulus : Word) (result : Bool)
  deriving DecidableEq, Repr

/-- A guard executes only original comparison successors and one finite ordering branch. -/
def step : Configuration → Option Configuration
  | .compare q (.ordering result) => some (.done q (orderEq result))
  | .compare q state => (BinaryWordMachine.step state).map (.compare q)
  | .done _ _ => none

/-- Four comparison tapes plus one fixed retained-modulus tape. -/
def tapes : Configuration → Fin 5 → Word
  | .compare q state => (BinaryWordMachine.tapes state).frame fun _ : Fin 1 ↦ q
  | .done q _ => ({} : BitLocalActions.Tapes).frame fun _ : Fin 1 ↦ q

/-- Every successor obeys the same fixed-bank bit-cell rule and keeps the modulus in place. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  have compareLocal {q : Word} {state : BinaryWordMachine.Configuration} {t : Configuration}
      (h : (BinaryWordMachine.step state).map (.compare q) = some t) :
      BitLocalActions.BankStep (tapes (.compare q state)) (tapes t) := by
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact (BinaryWordMachine.step_local hs).frame fun _ : Fin 1 ↦ q
  cases s with
  | compare q state =>
    cases state <;> try exact compareLocal h
    cases h
    exact (show BitLocalActions.Step {} {} from
      ⟨.keep _, .keep _, .keep _, .keep _⟩).frame fun _ : Fin 1 ↦ q
  | done q result => cases h

/-- Actual traces count the shared local-bit successors, without arbitrary cost annotations. -/
inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- External fuel observer of the literal controller. -/
def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) :
    runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- Surplus observation fuel preserves a completed literal run. -/
theorem Trace.runFuel_done {n : ℕ} {s t : Configuration} (h : Trace n s t)
    (halted : step t = none) (extra : ℕ) : runFuel (n + extra) s = t := by
  induction h with
  | nil s => cases extra <;> simp [runFuel, halted]
  | cons head _ ih =>
    rw [Nat.add_right_comm, runFuel, head]
    exact ih halted

/-- Lift a local instruction into the approved memory architecture without touching RAM bits. -/
def ramStep (s : AddressedBits.Memory × Configuration) :
    Option (AddressedBits.Memory × Configuration) := (step s.2).map fun t ↦ (s.1, t)

/-- Literal successor observer for the same local program in the RAM memory state. -/
def ramRunFuel : ℕ → AddressedBits.Memory × Configuration → AddressedBits.Memory × Configuration
  | 0, s => s
  | n + 1, s => match ramStep s with
      | none => s
      | some t => ramRunFuel n t

/-- The lifted program has exactly the same local execution and retains the original memory. -/
theorem ramRunFuel_eq (mem : AddressedBits.Memory) (n : ℕ) (s : Configuration) :
    ramRunFuel n (mem, s) = (mem, runFuel n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hs : step s <;> simp [ramRunFuel, ramStep, runFuel, hs, ih]

/-- Lift the actual arithmetic trace, keeping its step count and the identical RAM memory. -/
theorem Trace.ramRunFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t)
    (mem : AddressedBits.Memory) : ramRunFuel n (mem, s) = (mem, t) := by
  rw [BinaryEqualMachine.ramRunFuel_eq, h.runFuel_eq]

/-- Every lifted successor preserves memory and satisfies the same address-controller tape rule. -/
theorem ramStep_local {s t : AddressedBits.Memory × Configuration}
    (h : ramStep s = some t) :
    t.1 = s.1 ∧ BitLocalActions.BankStep (tapes s.2) (tapes t.2) := by
  obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
  cases ht
  exact ⟨rfl, step_local hs⟩

end Computation.BinaryEqualMachine
