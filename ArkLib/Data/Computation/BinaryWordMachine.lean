/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BitLocalActions

/-!
# Literal binary-word local tape controller

Words are little-endian bit lists. The fixed controller consumes at most one cell from each
input per step and updates only finite Boolean control. Addition emits its sum bit and retains
the carry. Comparison retains the ordering of the most significant differing bit seen so far.
Output normalization trims leading zeros on the reversed result and restores order one bit per
transition. No numeric arithmetic, length, whole-list traversal, or callback runs in dispatch.

Counts are simultaneous finite-control local bit-RAM transitions in `BitLocalActions`, the same
interface satisfied by `AddressedBits`. They are not host evaluation time. Heap load/store,
input materialization, and architectural address accesses remain separate caller obligations.
-/

@[expose] public section

namespace Computation.BinaryWordMachine

abbrev Word := List Bool

/-- One full-adder's finite Boolean truth table. -/
def sumBit (x y carry : Bool) : Bool := (x != y) != carry

/-- Carry-out depends only on three bits, not on decoded natural numbers. -/
def carryBit (x y carry : Bool) : Bool := (x && y) || ((x != y) && carry)

/-- A higher differing bit overrides the ordering of all previously consumed lower bits. -/
def compareBit (x y : Bool) (previous : Ordering) : Ordering :=
  if x = y then previous else if x then .gt else .lt

/-- The fixed finite-control phases, with local bit tapes stored explicitly. -/
inductive Configuration where
  | startAdd (left right : Word) (carry : Bool)
  | add (left right : Word) (carry : Bool) (saved : Word)
  | trim (saved : Word)
  | reverse (saved output : Word)
  | word (output : Word)
  | startCompare (left right : Word)
  | compare (left right : Word) (previous : Ordering)
  | ordering (result : Ordering)
  deriving DecidableEq, Repr

/-- The only executed operations are local bit-cell actions and fixed finite Boolean control. -/
def step : Configuration → Option Configuration
  | .startAdd xs ys carry => some (.add xs ys carry [])
  | .add [] [] carry saved => some (.trim (if carry then true :: saved else saved))
  | .add (x :: xs) [] carry saved =>
      some (.add xs [] (carryBit x false carry) (sumBit x false carry :: saved))
  | .add [] (y :: ys) carry saved =>
      some (.add [] ys (carryBit false y carry) (sumBit false y carry :: saved))
  | .add (x :: xs) (y :: ys) carry saved =>
      some (.add xs ys (carryBit x y carry) (sumBit x y carry :: saved))
  | .trim [] => some (.word [])
  | .trim (false :: bs) => some (.trim bs)
  | .trim (true :: bs) => some (.reverse (true :: bs) [])
  | .reverse [] out => some (.word out)
  | .reverse (b :: bs) out => some (.reverse bs (b :: out))
  | .word _ => none
  | .startCompare xs ys => some (.compare xs ys .eq)
  | .compare [] [] previous => some (.ordering previous)
  | .compare (x :: xs) [] previous => some (.compare xs [] (compareBit x false previous))
  | .compare [] (y :: ys) previous => some (.compare [] ys (compareBit false y previous))
  | .compare (x :: xs) (y :: ys) previous => some (.compare xs ys (compareBit x y previous))
  | .ordering _ => none

/-- Projection keeps all four physical tapes fixed throughout addition and normalization. -/
def tapes : Configuration → BitLocalActions.Tapes
  | .startAdd xs ys _ => { left := xs, right := ys }
  | .add xs ys _ saved => { left := xs, right := ys, saved := saved }
  | .trim saved => { saved := saved }
  | .reverse saved out => { saved := saved, output := out }
  | .word out => { output := out }
  | .startCompare xs ys => { left := xs, right := ys }
  | .compare xs ys _ => { left := xs, right := ys }
  | .ordering _ => {}

/-- Every actual arithmetic successor is one permitted shared-model local bit transition. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.Step (tapes s) (tapes t) := by
  cases s with
  | startAdd xs ys c => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
  | add xs ys c saved =>
    cases xs <;> cases ys
    · cases c <;> cases h
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.keep _, .keep _, .push _ _, .keep _⟩
    · cases h; exact ⟨.keep _, .pop _ _, .push _ _, .keep _⟩
    · cases h; exact ⟨.pop _ _, .keep _, .push _ _, .keep _⟩
    · cases h; exact ⟨.pop _ _, .pop _ _, .push _ _, .keep _⟩
  | trim saved =>
    cases saved with
    | nil => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases b <;> cases h
      · exact ⟨.keep _, .keep _, .pop _ _, .keep _⟩
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
  | reverse saved out =>
    cases saved with
    | nil => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons b bs => cases h; exact ⟨.keep _, .keep _, .pop _ _, .push _ _⟩
  | word out => cases h
  | startCompare xs ys => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
  | compare xs ys previous =>
    cases xs <;> cases ys <;> cases h
    · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    · exact ⟨.keep _, .pop _ _, .keep _, .keep _⟩
    · exact ⟨.pop _ _, .keep _, .keep _, .keep _⟩
    · exact ⟨.pop _ _, .pop _ _, .keep _, .keep _⟩
  | ordering result => cases h

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
  rw [BinaryWordMachine.ramRunFuel_eq, h.runFuel_eq]

/-- Every lifted successor preserves memory and satisfies the same address-controller tape rule. -/
theorem ramStep_local {s t : AddressedBits.Memory × Configuration}
    (h : ramStep s = some t) :
    t.1 = s.1 ∧ BitLocalActions.Step (tapes s.2) (tapes t.2) := by
  obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
  cases ht
  exact ⟨rfl, step_local hs⟩

end Computation.BinaryWordMachine
