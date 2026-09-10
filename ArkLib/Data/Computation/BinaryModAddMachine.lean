/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryBorrowMachine

/-!
# Literal modular addition with retained modulus

Seven fixed physical tapes hold the four arithmetic tapes, the retained modulus, a sum backup,
and a reversal scratch tape. Each copy is a pair of charged local-bit passes. A recorded borrow
selects the backup sum or reduced difference; discarded bits are cleared explicitly.
-/

@[expose] public section

namespace Computation.BinaryModAddMachine

open BinaryWordMachine (Word)

/-- Four arithmetic tapes and three fixed retained/scratch tapes. -/
structure Storage extends BitLocalActions.Tapes where
  modulus : Word := []
  backup : Word := []
  scratch : Word := []
  deriving DecidableEq, Repr

def Storage.Step (s t : Storage) : Prop :=
  BitLocalActions.Step s.toTapes t.toTapes ∧
    BitLocalActions.CellStep s.modulus t.modulus ∧
    BitLocalActions.CellStep s.backup t.backup ∧
    BitLocalActions.CellStep s.scratch t.scratch

def Storage.bank (s : Storage) : Fin 7 → Word :=
  s.toTapes.frame fun i : Fin 3 ↦
    if i.val = 0 then s.modulus else if i.val = 1 then s.backup else s.scratch

/-- The physical storage rule is precisely the shared fixed-bank local-cell rule. -/
theorem Storage.Step.bank {s t : Storage} (h : s.Step t) :
    BitLocalActions.BankStep s.bank t.bank := by
  intro i
  unfold Storage.bank BitLocalActions.Tapes.frame
  split_ifs with hi
  · exact h.1.pad 3 i
  · dsimp only
    split_ifs
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

inductive Configuration where
  | start (modulus left right : Word)
  | add (modulus : Word) (state : BinaryWordMachine.Configuration)
  | sumReverse (modulus remaining saved : Word)
  | sumCopy (modulus remaining left backup : Word)
  | modReverse (remaining saved left backup : Word)
  | modCopy (saved modulus left right backup : Word)
  | subtract (modulus backup : Word) (state : BinaryBorrowMachine.Configuration)
  | clearBackup (modulus remaining output : Word)
  | discardResult (modulus backup output : Word)
  | recoverReverse (modulus remaining saved : Word)
  | recoverCopy (modulus saved output : Word)
  | done (modulus output : Word)
  deriving DecidableEq, Repr

/-- Fixed finite phases and individual tape-cell actions only. -/
def step : Configuration → Option Configuration
  | .start q xs ys => some (.add q (.startAdd xs ys false))
  | .add q (.word out) => some (.sumReverse q out [])
  | .add q s => (BinaryWordMachine.step s).map (.add q)
  | .sumReverse q [] saved => some (.sumCopy q saved [] [])
  | .sumReverse q (x :: xs) saved => some (.sumReverse q xs (x :: saved))
  | .sumCopy q [] left backup => some (.modReverse q [] left backup)
  | .sumCopy q (x :: xs) left backup => some (.sumCopy q xs (x :: left) (x :: backup))
  | .modReverse [] saved left backup => some (.modCopy saved [] left [] backup)
  | .modReverse (x :: qs) saved left backup =>
      some (.modReverse qs (x :: saved) left backup)
  | .modCopy [] q left right backup =>
      some (.subtract q backup ⟨.start left right false, false⟩)
  | .modCopy (x :: saved) q left right backup =>
      some (.modCopy saved (x :: q) left (x :: right) backup)
  | .subtract q backup ⟨.normalize (.word out), b⟩ =>
      some (if b then .discardResult q backup out else .clearBackup q backup out)
  | .subtract q backup s => (BinaryBorrowMachine.step s).map (.subtract q backup)
  | .clearBackup q [] out => some (.done q out)
  | .clearBackup q (_ :: bs) out => some (.clearBackup q bs out)
  | .discardResult q backup [] => some (.recoverReverse q backup [])
  | .discardResult q backup (_ :: out) => some (.discardResult q backup out)
  | .recoverReverse q [] saved => some (.recoverCopy q saved [])
  | .recoverReverse q (x :: bs) saved => some (.recoverReverse q bs (x :: saved))
  | .recoverCopy q [] out => some (.done q out)
  | .recoverCopy q (x :: bs) out => some (.recoverCopy q bs (x :: out))
  | .done _ _ => none

/-- Every phase assigns each word to the same physical tape across its boundary. -/
def storage : Configuration → Storage
  | .start q xs ys => { left := xs, right := ys, modulus := q }
  | .add q s => { toTapes := BinaryWordMachine.tapes s, modulus := q }
  | .sumReverse q out saved => { output := out, saved := saved, modulus := q }
  | .sumCopy q saved left backup =>
      { left := left, saved := saved, modulus := q, backup := backup }
  | .modReverse q saved left backup =>
      { left := left, modulus := q, backup := backup, scratch := saved }
  | .modCopy saved q left right backup =>
      { left := left, right := right, modulus := q, backup := backup, scratch := saved }
  | .subtract q backup s =>
      { toTapes := BinaryBorrowMachine.tapes s, modulus := q, backup := backup }
  | .clearBackup q backup out => { output := out, modulus := q, backup := backup }
  | .discardResult q backup out => { output := out, modulus := q, backup := backup }
  | .recoverReverse q backup saved => { modulus := q, backup := backup, scratch := saved }
  | .recoverCopy q saved out => { output := out, modulus := q, scratch := saved }
  | .done q out => { output := out, modulus := q }

def tapes (s : Configuration) : Fin 7 → Word := (storage s).bank

theorem step_storage {s t : Configuration} (h : step s = some t) :
    (storage s).Step (storage t) := by
  have addLocal {q : Word} {state : BinaryWordMachine.Configuration} {t : Configuration}
      (h : (BinaryWordMachine.step state).map (.add q) = some t) :
      (storage (.add q state)).Step (storage t) := by
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact ⟨BinaryWordMachine.step_local hs, .keep _, .keep _, .keep _⟩
  have subLocal {q backup : Word} {state : BinaryBorrowMachine.Configuration}
      {t : Configuration} (h : (BinaryBorrowMachine.step state).map (.subtract q backup) = some t) :
      (storage (.subtract q backup state)).Step (storage t) := by
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact ⟨BinaryBorrowMachine.step_local hs, .keep _, .keep _, .keep _⟩
  cases s with
  | start q xs ys => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
      .keep _, .keep _, .keep _⟩
  | add q state =>
    cases state <;> try exact addLocal h
    cases h
    exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩
  | sumReverse q out saved =>
    cases out with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨⟨.keep _, .keep _, .push _ _, .pop _ _⟩,
        .keep _, .keep _, .keep _⟩
  | sumCopy q saved left backup =>
    cases saved with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨⟨.push _ _, .keep _, .pop _ _, .keep _⟩,
        .keep _, .push _ _, .keep _⟩
  | modReverse q saved left backup =>
    cases q with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .pop _ _, .keep _, .push _ _⟩
  | modCopy saved q left right backup =>
    cases saved with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨⟨.keep _, .push _ _, .keep _, .keep _⟩,
        .push _ _, .keep _, .pop _ _⟩
  | subtract q backup state =>
    rcases state with ⟨state, b⟩
    cases state <;> try exact subLocal h
    rename_i state
    cases state <;> try exact subLocal h
    cases b <;> cases h <;>
      exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩
  | clearBackup q bs out =>
    cases bs with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .pop _ _, .keep _⟩
  | discardResult q backup out =>
    cases out with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .pop _ _⟩,
        .keep _, .keep _, .keep _⟩
  | recoverReverse q bs saved =>
    cases bs with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .pop _ _, .push _ _⟩
  | recoverCopy q saved out =>
    cases saved with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩,
        .keep _, .keep _, .keep _⟩
    | cons x xs => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .push _ _⟩,
        .keep _, .keep _, .pop _ _⟩
  | done q out => cases h

/-- Every actual successor is a shared-model transition on the same seven physical tapes. -/
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
  rw [BinaryModAddMachine.ramRunFuel_eq, h.runFuel_eq]

/-- Every lifted successor preserves memory and satisfies the same address-controller tape rule. -/
theorem ramStep_local {s t : AddressedBits.Memory × Configuration}
    (h : ramStep s = some t) :
    t.1 = s.1 ∧ BitLocalActions.BankStep (tapes s.2) (tapes t.2) := by
  obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
  cases ht
  exact ⟨rfl, step_local hs⟩

end Computation.BinaryModAddMachine
