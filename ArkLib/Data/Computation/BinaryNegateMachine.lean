/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinarySubtractMachine

/-!
# Literal modular negation controller

The modulus and operand are physical input tapes. The operand is scanned for a nonzero bit,
then restored one bit per step before subtraction. Zero operands, including padded zero, clear
both inputs explicitly. Nonzero operands call the literal subtraction controller. No numeric
value test, free copy, or free restoration runs in dispatch.
-/

@[expose] public section

namespace Computation.BinaryNegateMachine

open BinaryWordMachine (Word)

inductive Configuration where
  | start (modulus operand : Word)
  | scan (modulus remaining saved : Word) (nonzero : Bool)
  | restore (modulus remaining operand : Word) (nonzero : Bool)
  | clear (modulus operand : Word)
  | subtract (state : BinarySubtractMachine.Configuration)
  deriving DecidableEq, Repr

/-- Literal finite-control dispatch, including zero testing and restoration. -/
def step : Configuration → Option Configuration
  | .start q xs => some (.scan q xs [] false)
  | .scan q [] saved nz => some (.restore q saved [] nz)
  | .scan q (x :: xs) saved nz => some (.scan q xs (x :: saved) (nz || x))
  | .restore q [] xs nz =>
      some (if nz then .subtract (.start q xs false) else .clear q xs)
  | .restore q (x :: saved) xs nz => some (.restore q saved (x :: xs) nz)
  | .clear [] [] => some (.subtract (.normalize (.word [])))
  | .clear (_ :: qs) [] => some (.clear qs [])
  | .clear [] (_ :: xs) => some (.clear [] xs)
  | .clear (_ :: qs) (_ :: xs) => some (.clear qs xs)
  | .subtract s => (BinarySubtractMachine.step s).map .subtract

/-- Modulus stays on the left; operand and its reversal use right and saved throughout. -/
def tapes : Configuration → BitLocalActions.Tapes
  | .start q xs => { left := q, right := xs }
  | .scan q xs saved _ => { left := q, right := xs, saved := saved }
  | .restore q saved xs _ => { left := q, right := xs, saved := saved }
  | .clear q xs => { left := q, right := xs }
  | .subtract s => BinarySubtractMachine.tapes s

theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.Step (tapes s) (tapes t) := by
  cases s with
  | start q xs => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
  | scan q xs saved nz =>
    cases xs with
    | nil => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨.keep _, .pop _ _, .push _ _, .keep _⟩
  | restore q saved xs nz =>
    cases saved with
    | nil => cases nz <;> cases h <;> exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons x saved => cases h; exact ⟨.keep _, .push _ _, .pop _ _, .keep _⟩
  | clear q xs =>
    cases q <;> cases xs <;> cases h
    · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    · exact ⟨.keep _, .pop _ _, .keep _, .keep _⟩
    · exact ⟨.pop _ _, .keep _, .keep _, .keep _⟩
    · exact ⟨.pop _ _, .pop _ _, .keep _, .keep _⟩
  | subtract state =>
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact BinarySubtractMachine.step_local hs

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
  rw [BinaryNegateMachine.ramRunFuel_eq, h.runFuel_eq]

/-- Every lifted successor preserves memory and satisfies the same address-controller tape rule. -/
theorem ramStep_local {s t : AddressedBits.Memory × Configuration}
    (h : ramStep s = some t) :
    t.1 = s.1 ∧ BitLocalActions.Step (tapes s.2) (tapes t.2) := by
  obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
  cases ht
  exact ⟨rfl, step_local hs⟩

/-- Subtraction uses exactly its proved local-bit successors. -/
theorem lift_trace {n : ℕ} {s t : BinarySubtractMachine.Configuration}
    (h : BinarySubtractMachine.Trace n s t) : Trace n (.subtract s) (.subtract t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp [step, head]) ih

end Computation.BinaryNegateMachine
