/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryWordMachine

/-!
# Literal saturating binary subtraction

The four physical tapes match the addition controller. A fixed full-subtractor consumes one
bit from each nonempty input and pushes one result bit. Final underflow clears the temporary
tape one cell at a time. Otherwise the existing literal normalization controller restores a
canonical result. Borrow-in implements decrement without constructing a numeric constant.
-/

@[expose] public section

namespace Computation.BinarySubtractMachine

open BinaryWordMachine (Word sumBit)

/-- Borrow-out is a fixed three-bit Boolean truth table. -/
def borrowBit (x y borrow : Bool) : Bool := (!x && y) || (!(x != y) && borrow)

inductive Configuration where
  | start (left right : Word) (borrow : Bool)
  | scan (left right : Word) (borrow : Bool) (saved : Word)
  | discard (saved : Word)
  | normalize (state : BinaryWordMachine.Configuration)
  deriving DecidableEq, Repr

/-- Literal local-cell successor; no numeric decoding or whole-list traversal is executed. -/
def step : Configuration → Option Configuration
  | .start xs ys b => some (.scan xs ys b [])
  | .scan [] [] b saved =>
      some (if b then .discard saved else .normalize (.trim saved))
  | .scan (x :: xs) [] b saved =>
      some (.scan xs [] (borrowBit x false b) (sumBit x false b :: saved))
  | .scan [] (y :: ys) b saved =>
      some (.scan [] ys (borrowBit false y b) (sumBit false y b :: saved))
  | .scan (x :: xs) (y :: ys) b saved =>
      some (.scan xs ys (borrowBit x y b) (sumBit x y b :: saved))
  | .discard [] => some (.normalize (.word []))
  | .discard (_ :: bs) => some (.discard bs)
  | .normalize s => (BinaryWordMachine.step s).map .normalize

/-- Fixed physical tape projection, including the normalization subprogram. -/
def tapes : Configuration → BitLocalActions.Tapes
  | .start xs ys _ => { left := xs, right := ys }
  | .scan xs ys _ saved => { left := xs, right := ys, saved := saved }
  | .discard saved => { saved := saved }
  | .normalize s => BinaryWordMachine.tapes s

theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.Step (tapes s) (tapes t) := by
  cases s with
  | start xs ys b => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
  | scan xs ys b saved =>
    cases xs <;> cases ys
    · cases b <;> cases h <;> exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    · cases h; exact ⟨.keep _, .pop _ _, .push _ _, .keep _⟩
    · cases h; exact ⟨.pop _ _, .keep _, .push _ _, .keep _⟩
    · cases h; exact ⟨.pop _ _, .pop _ _, .push _ _, .keep _⟩
  | discard saved =>
    cases saved with
    | nil => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons b bs => cases h; exact ⟨.keep _, .keep _, .pop _ _, .keep _⟩
  | normalize state =>
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact BinaryWordMachine.step_local hs

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
  rw [BinarySubtractMachine.ramRunFuel_eq, h.runFuel_eq]

/-- Every lifted successor preserves memory and satisfies the same address-controller tape rule. -/
theorem ramStep_local {s t : AddressedBits.Memory × Configuration}
    (h : ramStep s = some t) :
    t.1 = s.1 ∧ BitLocalActions.Step (tapes s.2) (tapes t.2) := by
  obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
  cases ht
  exact ⟨rfl, step_local hs⟩

/-- The normalization subprogram uses exactly the original local successors. -/
theorem lift_trace {n : ℕ} {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.Trace n s t) : Trace n (.normalize s) (.normalize t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp [step, head]) ih

end Computation.BinarySubtractMachine
