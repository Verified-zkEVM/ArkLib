/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryNegateMachine

/-!
# Literal negation retaining its modulus

The input modulus initially occurs only on its retained tape. Two charged bit passes restore
that tape and write a separate arithmetic copy. The original literal negation then consumes
its copy and operand; a final dispatch retains the exact original modulus and canonical output.
-/

@[expose] public section

namespace Computation.BinaryRetainedNegateMachine

open BinaryWordMachine (Word)

structure Storage extends BitLocalActions.Tapes where
  modulus : Word := []
  scratch : Word := []
  deriving DecidableEq, Repr

def Storage.Step (s t : Storage) : Prop :=
  BitLocalActions.Step s.toTapes t.toTapes ∧ BitLocalActions.CellStep s.modulus t.modulus ∧
    BitLocalActions.CellStep s.scratch t.scratch

def Storage.bank (s : Storage) : Fin 6 → Word :=
  s.toTapes.frame fun i : Fin 2 ↦ if i.val = 0 then s.modulus else s.scratch

theorem Storage.Step.bank {s t : Storage} (h : s.Step t) :
    BitLocalActions.BankStep s.bank t.bank := by
  intro i
  unfold Storage.bank BitLocalActions.Tapes.frame
  split_ifs
  · exact h.1.pad 2 i
  · dsimp only
    split_ifs
    · exact h.2.1
    · exact h.2.2

inductive Configuration where
  | start (modulus input : Word)
  | copyReverse (remaining input saved : Word)
  | copyRestore (saved modulus left input : Word)
  | negate (modulus : Word) (state : BinaryNegateMachine.Configuration)
  | done (modulus output : Word)
  deriving DecidableEq, Repr

/-- Each copied modulus bit is written by the actual restoration successor. -/
def step : Configuration → Option Configuration
  | .start q x => some (.copyReverse q x [])
  | .copyReverse [] x saved => some (.copyRestore saved [] [] x)
  | .copyReverse (b :: bs) x saved => some (.copyReverse bs x (b :: saved))
  | .copyRestore [] q left x => some (.negate q (.start left x))
  | .copyRestore (b :: bs) q left x => some (.copyRestore bs (b :: q) (b :: left) x)
  | .negate q (.subtract (.normalize (.word out))) => some (.done q out)
  | .negate q s => (BinaryNegateMachine.step s).map (.negate q)
  | .done _ _ => none

/-- Six fixed physical tapes; retained modulus and its arithmetic copy are separate storage. -/
def storage : Configuration → Storage
  | .start q x => { modulus := q, right := x }
  | .copyReverse q x saved => { modulus := q, right := x, scratch := saved }
  | .copyRestore saved q left x => { modulus := q, left := left, right := x, scratch := saved }
  | .negate q s => { toTapes := BinaryNegateMachine.tapes s, modulus := q }
  | .done q out => { modulus := q, output := out }

def tapes (s : Configuration) : Fin 6 → Word := (storage s).bank

theorem step_storage {s t : Configuration} (h : step s = some t) :
    (storage s).Step (storage t) := by
  have negLocal {q : Word} {state : BinaryNegateMachine.Configuration} {t : Configuration}
      (h : (BinaryNegateMachine.step state).map (.negate q) = some t) :
      (storage (.negate q state)).Step (storage t) := by
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact ⟨BinaryNegateMachine.step_local hs, .keep _, .keep _⟩
  cases s with
  | start q x => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  | copyReverse q x saved =>
    cases q with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .pop _ _, .push _ _⟩
  | copyRestore saved q left x =>
    cases saved with
    | nil => cases h; exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs => cases h; exact ⟨⟨.push _ _, .keep _, .keep _, .keep _⟩, .push _ _, .pop _ _⟩
  | negate q state =>
    cases state <;> try exact negLocal h
    rename_i state
    cases state <;> try exact negLocal h
    rename_i state
    cases state <;> try exact negLocal h
    cases h
    exact ⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  | done q out => cases h

/-- Every actual successor satisfies the shared fixed six-tape local-bit rule. -/
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
  rw [BinaryRetainedNegateMachine.ramRunFuel_eq, h.runFuel_eq]

/-- Every lifted successor preserves memory and satisfies the same address-controller tape rule. -/
theorem ramStep_local {s t : AddressedBits.Memory × Configuration}
    (h : ramStep s = some t) :
    t.1 = s.1 ∧ BitLocalActions.BankStep (tapes s.2) (tapes t.2) := by
  obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
  cases ht
  exact ⟨rfl, step_local hs⟩

end Computation.BinaryRetainedNegateMachine
