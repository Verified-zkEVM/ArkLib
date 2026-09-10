/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryModAddMachine

/-!
# Literal repeated-addition scalar multiplication

Eleven physical bit tapes hold the seven modular-add tapes plus a binary countdown, a retained
multiplicand, a shuttle, and a held accumulator. Countdown decrements and every operand copy,
transfer and restoration execute literal local-bit loops. The modulus and multiplicand remain
on their original tapes at completion. Empty canonical countdown is the sole loop exit test.
-/

@[expose] public section

namespace Computation.BinaryMulMachine

open BinaryWordMachine (Word)

structure Storage extends BinaryModAddMachine.Storage where
  counter : Word := []
  factor : Word := []
  shuttle : Word := []
  held : Word := []
  deriving DecidableEq, Repr

def Storage.Step (s t : Storage) : Prop :=
  BinaryModAddMachine.Storage.Step s.toStorage t.toStorage ∧
    BitLocalActions.CellStep s.counter t.counter ∧ BitLocalActions.CellStep s.factor t.factor ∧
    BitLocalActions.CellStep s.shuttle t.shuttle ∧ BitLocalActions.CellStep s.held t.held

def Storage.bank (s : Storage) : Fin 11 → Word := fun i ↦
  if h : i.val < 7 then s.toStorage.bank ⟨i.val, h⟩
  else if i.val = 7 then s.counter else if i.val = 8 then s.factor
  else if i.val = 9 then s.shuttle else s.held

theorem Storage.Step.bank {s t : Storage} (h : s.Step t) :
    BitLocalActions.BankStep s.bank t.bank := by
  intro i
  unfold Storage.bank
  split_ifs
  · exact h.1.bank _
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

inductive Configuration where
  | start (modulus counter factor : Word)
  | loop (modulus counter factor accumulator : Word)
  | holdReverse (modulus counter factor remaining saved : Word)
  | holdCopy (modulus counter factor saved held : Word)
  | countReverse (modulus remaining factor saved held : Word)
  | countCopy (modulus saved factor count held : Word)
  | decrement (modulus factor held : Word) (state : BinarySubtractMachine.Configuration)
  | countOutReverse (modulus factor held remaining saved : Word)
  | countOutCopy (modulus factor held saved counter : Word)
  | factorReverse (modulus counter remaining saved held : Word)
  | factorCopy (modulus counter saved factor right held : Word)
  | accReverse (modulus counter factor right remaining saved : Word)
  | accCopy (modulus counter factor right saved left : Word)
  | add (counter factor : Word) (state : BinaryModAddMachine.Configuration)
  | done (modulus factor output : Word)
  deriving DecidableEq, Repr

/-- Literal dispatch contains no decoded counter, numeric arithmetic or whole-word operation. -/
def step : Configuration → Option Configuration
  | .start q count y => some (.loop q count y [])
  | .loop q [] y acc => some (.done q y acc)
  | .loop q (b :: bs) y acc => some (.holdReverse q (b :: bs) y acc [])
  | .holdReverse q count y [] saved => some (.holdCopy q count y saved [])
  | .holdReverse q count y (b :: bs) saved => some (.holdReverse q count y bs (b :: saved))
  | .holdCopy q count y [] held => some (.countReverse q count y [] held)
  | .holdCopy q count y (b :: bs) held => some (.holdCopy q count y bs (b :: held))
  | .countReverse q [] y saved held => some (.countCopy q saved y [] held)
  | .countReverse q (b :: bs) y saved held => some (.countReverse q bs y (b :: saved) held)
  | .countCopy q [] y count held => some (.decrement q y held (.start count [] true))
  | .countCopy q (b :: bs) y count held => some (.countCopy q bs y (b :: count) held)
  | .decrement q y held (.normalize (.word out)) => some (.countOutReverse q y held out [])
  | .decrement q y held state => (BinarySubtractMachine.step state).map (.decrement q y held)
  | .countOutReverse q y held [] saved => some (.countOutCopy q y held saved [])
  | .countOutReverse q y held (b :: bs) saved => some (.countOutReverse q y held bs (b :: saved))
  | .countOutCopy q y held [] count => some (.factorReverse q count y [] held)
  | .countOutCopy q y held (b :: bs) count => some (.countOutCopy q y held bs (b :: count))
  | .factorReverse q count [] saved held => some (.factorCopy q count saved [] [] held)
  | .factorReverse q count (b :: bs) saved held =>
      some (.factorReverse q count bs (b :: saved) held)
  | .factorCopy q count [] y right held => some (.accReverse q count y right held [])
  | .factorCopy q count (b :: bs) y right held =>
      some (.factorCopy q count bs (b :: y) (b :: right) held)
  | .accReverse q count y right [] saved => some (.accCopy q count y right saved [])
  | .accReverse q count y right (b :: bs) saved =>
      some (.accReverse q count y right bs (b :: saved))
  | .accCopy q count y right [] left => some (.add count y (.start q left right))
  | .accCopy q count y right (b :: bs) left => some (.accCopy q count y right bs (b :: left))
  | .add count y (.done q out) => some (.loop q count y out)
  | .add count y state => (BinaryModAddMachine.step state).map (.add count y)
  | .done _ _ _ => none

/-- Physical tape identities are fixed across arithmetic and transfer phases. -/
def storage : Configuration → Storage
  | .start q count y => { modulus := q, counter := count, factor := y }
  | .loop q count y acc => { modulus := q, counter := count, factor := y, output := acc }
  | .holdReverse q count y acc saved =>
      { modulus := q, counter := count, factor := y, output := acc, shuttle := saved }
  | .holdCopy q count y saved held =>
      { modulus := q, counter := count, factor := y, shuttle := saved, held := held }
  | .countReverse q count y saved held =>
      { modulus := q, counter := count, factor := y, shuttle := saved, held := held }
  | .countCopy q saved y count held =>
      { modulus := q, factor := y, shuttle := saved, left := count, held := held }
  | .decrement q y held state =>
      { toTapes := BinarySubtractMachine.tapes state, modulus := q, factor := y, held := held }
  | .countOutReverse q y held out saved =>
      { modulus := q, factor := y, held := held, output := out, shuttle := saved }
  | .countOutCopy q y held saved count =>
      { modulus := q, factor := y, held := held, shuttle := saved, counter := count }
  | .factorReverse q count y saved held =>
      { modulus := q, counter := count, factor := y, shuttle := saved, held := held }
  | .factorCopy q count saved y right held =>
      { modulus := q, counter := count, factor := y, right := right,
        shuttle := saved, held := held }
  | .accReverse q count y right held saved =>
      { modulus := q, counter := count, factor := y, right := right, held := held,
        shuttle := saved }
  | .accCopy q count y right saved left =>
      { modulus := q, counter := count, factor := y, right := right,
        shuttle := saved, left := left }
  | .add count y state =>
      { toStorage := BinaryModAddMachine.storage state, counter := count, factor := y }
  | .done q y out => { modulus := q, factor := y, output := out }

def tapes (s : Configuration) : Fin 11 → Word := (storage s).bank

theorem step_storage {s t : Configuration} (h : step s = some t) :
    (storage s).Step (storage t) := by
  have decLocal {q y held : Word} {state : BinarySubtractMachine.Configuration}
      {t : Configuration}
      (h : (BinarySubtractMachine.step state).map (.decrement q y held) = some t) :
      (storage (.decrement q y held state)).Step (storage t) := by
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact ⟨⟨BinarySubtractMachine.step_local hs, .keep _, .keep _, .keep _⟩,
      .keep _, .keep _, .keep _, .keep _⟩
  have addLocal {count y : Word} {state : BinaryModAddMachine.Configuration}
      {t : Configuration}
      (h : (BinaryModAddMachine.step state).map (.add count y) = some t) :
      (storage (.add count y state)).Step (storage t) := by
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact ⟨BinaryModAddMachine.step_storage hs, .keep _, .keep _, .keep _, .keep _⟩
  cases s with
  | start q count y =>
    cases h
    exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
  | loop q count y acc =>
    cases count <;> cases h <;>
      exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
  | holdReverse q count y acc saved =>
    cases acc with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.keep _, .keep _, .keep _, .pop _ _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .push _ _, .keep _⟩
  | holdCopy q count y saved held =>
    cases saved with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .pop _ _, .push _ _⟩
  | countReverse q count y saved held =>
    cases count with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .pop _ _, .keep _, .push _ _, .keep _⟩
  | countCopy q saved y count held =>
    cases saved with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.push _ _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .pop _ _, .keep _⟩
  | countOutReverse q y held out saved =>
    cases out with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.keep _, .keep _, .keep _, .pop _ _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .push _ _, .keep _⟩
  | countOutCopy q y held saved count =>
    cases saved with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .push _ _, .keep _, .pop _ _, .keep _⟩
  | factorReverse q count y saved held =>
    cases y with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .pop _ _, .push _ _, .keep _⟩
  | factorCopy q count saved y right held =>
    cases saved with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.keep _, .push _ _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .push _ _, .pop _ _, .keep _⟩
  | accReverse q count y right held saved =>
    cases held with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .push _ _, .pop _ _⟩
  | accCopy q count y right saved left =>
    cases saved with
    | nil => cases h; exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨.push _ _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .pop _ _, .keep _⟩
  | decrement q y held state =>
    cases state <;> try exact decLocal h
    rename_i state
    cases state <;> try exact decLocal h
    cases h
    exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
  | add count y state =>
    cases state <;> try exact addLocal h
    cases h
    exact ⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _, .keep _⟩
  | done q y out => cases h

/-- Every literal multiplication successor obeys the common eleven-tape bit-RAM rule. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := (step_storage h).bank

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
  rw [BinaryMulMachine.ramRunFuel_eq, h.runFuel_eq]

/-- Every lifted successor preserves memory and satisfies the same address-controller tape rule. -/
theorem ramStep_local {s t : AddressedBits.Memory × Configuration}
    (h : ramStep s = some t) :
    t.1 = s.1 ∧ BitLocalActions.BankStep (tapes s.2) (tapes t.2) := by
  obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
  cases ht
  exact ⟨rfl, step_local hs⟩

end Computation.BinaryMulMachine
