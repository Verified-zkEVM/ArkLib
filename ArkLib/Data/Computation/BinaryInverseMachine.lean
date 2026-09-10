/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryMulMachine

/-!
# Literal prime-field inverse search

Thirteen fixed physical tapes extend multiplication with a retained search candidate and a
search scratch tape. The program tests zero by scanning and restoring the input, then searches
candidates starting at one. Multiplication, product-one testing, candidate increments, and all
copy/restore operations are literal local-bit phases. No inverse, numeric target, or decoded
counter runs in dispatch. The proof of prime-field inverse existence bounds this actual search.
-/

@[expose] public section

namespace Computation.BinaryInverseMachine

open BinaryWordMachine (Word)

structure Storage extends toMulStorage : BinaryMulMachine.Storage where
  candidate : Word := []
  searchScratch : Word := []
  deriving DecidableEq, Repr

def Storage.Step (s t : Storage) : Prop :=
  BinaryMulMachine.Storage.Step s.toMulStorage t.toMulStorage ∧
    BitLocalActions.CellStep s.candidate t.candidate ∧
    BitLocalActions.CellStep s.searchScratch t.searchScratch

def Storage.bank (s : Storage) : Fin 13 → Word := fun i ↦
  if h : i.val < 11 then s.toMulStorage.bank ⟨i.val, h⟩
  else if i.val = 11 then s.candidate else s.searchScratch

theorem Storage.Step.bank {s t : Storage} (h : s.Step t) :
    BitLocalActions.BankStep s.bank t.bank := by
  intro i
  unfold Storage.bank
  split_ifs
  · exact h.1.bank _
  · exact h.2.1
  · exact h.2.2

inductive Configuration where
  | start (modulus input : Word)
  | scan (modulus remaining saved : Word) (nonzero : Bool)
  | restore (modulus remaining input : Word) (nonzero : Bool)
  | seed (modulus input : Word)
  | multiply (candidate : Word) (state : BinaryMulMachine.Configuration)
  | checkProduct (modulus input candidate output : Word)
  | afterOne (modulus input candidate remaining : Word)
  | clearProduct (modulus input candidate remaining : Word)
  | incrementReverse (modulus input remaining saved : Word)
  | incrementCopy (modulus input saved left : Word)
  | increment (modulus input : Word) (state : BinaryWordMachine.Configuration)
  | candidateReverse (modulus input remaining saved : Word)
  | candidateCopy (modulus input saved counter candidate : Word)
  | recoverReverse (modulus input remaining saved : Word)
  | recoverCopy (modulus input saved output : Word)
  | done (modulus input output : Word)
  deriving DecidableEq, Repr

/-- Seed one Boolean bit; produce all subsequent candidates by literal increment. -/
def step : Configuration → Option Configuration
  | .start q x => some (.scan q x [] false)
  | .scan q [] saved nz => some (.restore q saved [] nz)
  | .scan q (b :: bs) saved nz => some (.scan q bs (b :: saved) (nz || b))
  | .restore q [] x nz => some (if nz then .seed q x else .done q x [])
  | .restore q (b :: bs) x nz => some (.restore q bs (b :: x) nz)
  | .seed q x => some (.multiply [true] (.start q [true] x))
  | .multiply candidate (.done q x out) => some (.checkProduct q x candidate out)
  | .multiply candidate state => (BinaryMulMachine.step state).map (.multiply candidate)
  | .checkProduct q x candidate [] => some (.incrementReverse q x candidate [])
  | .checkProduct q x candidate (false :: bs) => some (.clearProduct q x candidate bs)
  | .checkProduct q x candidate (true :: bs) => some (.afterOne q x candidate bs)
  | .afterOne q x candidate [] => some (.recoverReverse q x candidate [])
  | .afterOne q x candidate (b :: bs) => some (.clearProduct q x candidate (b :: bs))
  | .clearProduct q x candidate [] => some (.incrementReverse q x candidate [])
  | .clearProduct q x candidate (_ :: bs) => some (.clearProduct q x candidate bs)
  | .incrementReverse q x [] saved => some (.incrementCopy q x saved [])
  | .incrementReverse q x (b :: bs) saved => some (.incrementReverse q x bs (b :: saved))
  | .incrementCopy q x [] left => some (.increment q x (.startAdd left [] true))
  | .incrementCopy q x (b :: bs) left => some (.incrementCopy q x bs (b :: left))
  | .increment q x (.word out) => some (.candidateReverse q x out [])
  | .increment q x state => (BinaryWordMachine.step state).map (.increment q x)
  | .candidateReverse q x [] saved => some (.candidateCopy q x saved [] [])
  | .candidateReverse q x (b :: bs) saved => some (.candidateReverse q x bs (b :: saved))
  | .candidateCopy q x [] count candidate => some (.multiply candidate (.start q count x))
  | .candidateCopy q x (b :: bs) count candidate =>
      some (.candidateCopy q x bs (b :: count) (b :: candidate))
  | .recoverReverse q x [] saved => some (.recoverCopy q x saved [])
  | .recoverReverse q x (b :: bs) saved => some (.recoverReverse q x bs (b :: saved))
  | .recoverCopy q x [] out => some (.done q x out)
  | .recoverCopy q x (b :: bs) out => some (.recoverCopy q x bs (b :: out))
  | .done _ _ _ => none

/-- The modulus and input stay in multiplication's original slots throughout the search. -/
def storage : Configuration → Storage
  | .start q x => { modulus := q, factor := x }
  | .scan q x saved _ => { modulus := q, factor := x, searchScratch := saved }
  | .restore q saved x _ => { modulus := q, factor := x, searchScratch := saved }
  | .seed q x => { modulus := q, factor := x }
  | .multiply candidate state =>
      { toMulStorage := BinaryMulMachine.storage state, candidate := candidate }
  | .checkProduct q x candidate out =>
      { modulus := q, factor := x, candidate := candidate, output := out }
  | .afterOne q x candidate out =>
      { modulus := q, factor := x, candidate := candidate, output := out }
  | .clearProduct q x candidate out =>
      { modulus := q, factor := x, candidate := candidate, output := out }
  | .incrementReverse q x candidate saved =>
      { modulus := q, factor := x, candidate := candidate, searchScratch := saved }
  | .incrementCopy q x saved left =>
      { modulus := q, factor := x, searchScratch := saved, left := left }
  | .increment q x state => { toTapes := BinaryWordMachine.tapes state, modulus := q, factor := x }
  | .candidateReverse q x out saved =>
      { modulus := q, factor := x, output := out, searchScratch := saved }
  | .candidateCopy q x saved count candidate =>
      { modulus := q, factor := x, searchScratch := saved,
        counter := count, candidate := candidate }
  | .recoverReverse q x candidate saved =>
      { modulus := q, factor := x, candidate := candidate, searchScratch := saved }
  | .recoverCopy q x saved out =>
      { modulus := q, factor := x, searchScratch := saved, output := out }
  | .done q x out => { modulus := q, factor := x, output := out }

def tapes (s : Configuration) : Fin 13 → Word := (storage s).bank

theorem step_storage {s t : Configuration} (h : step s = some t) :
    (storage s).Step (storage t) := by
  have mulLocal {candidate : Word} {state : BinaryMulMachine.Configuration}
      {t : Configuration} (h : (BinaryMulMachine.step state).map (.multiply candidate) = some t) :
      (storage (.multiply candidate state)).Step (storage t) := by
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact ⟨BinaryMulMachine.step_storage hs, .keep _, .keep _⟩
  have incLocal {q x : Word} {state : BinaryWordMachine.Configuration}
      {t : Configuration} (h : (BinaryWordMachine.step state).map (.increment q x) = some t) :
      (storage (.increment q x state)).Step (storage t) := by
    obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact ⟨⟨⟨BinaryWordMachine.step_local hs, .keep _, .keep _, .keep _⟩,
      .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  cases s with
  | start q x =>
    cases h
    exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  | seed q x =>
    cases h
    exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .push _ _, .keep _, .keep _, .keep _⟩, .push _ _, .keep _⟩
  | scan q x saved nz =>
    cases x with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .pop _ _, .keep _, .keep _⟩, .keep _, .push _ _⟩
  | restore q saved x nz =>
    cases saved with
    | nil =>
      cases nz <;> cases h <;>
        exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .push _ _, .keep _, .keep _⟩, .keep _, .pop _ _⟩
  | checkProduct q x candidate out =>
    cases out with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases b <;> cases h <;>
        exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .pop _ _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  | afterOne q x candidate out =>
    cases out <;> cases h <;>
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  | clearProduct q x candidate out =>
    cases out with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .pop _ _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  | incrementReverse q x candidate saved =>
    cases candidate with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .pop _ _, .push _ _⟩
  | incrementCopy q x saved left =>
    cases saved with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.push _ _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .pop _ _⟩
  | candidateReverse q x out saved =>
    cases out with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .pop _ _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .push _ _⟩
  | candidateCopy q x saved count candidate =>
    cases saved with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .push _ _, .keep _, .keep _, .keep _⟩, .push _ _, .pop _ _⟩
  | recoverReverse q x candidate saved =>
    cases candidate with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .pop _ _, .push _ _⟩
  | recoverCopy q x saved out =>
    cases saved with
    | nil =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
    | cons b bs =>
      cases h
      exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .push _ _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .pop _ _⟩
  | multiply candidate state =>
    cases state <;> try exact mulLocal h
    cases h
    exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  | increment q x state =>
    cases state <;> try exact incLocal h
    cases h
    exact ⟨⟨⟨⟨.keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _, .keep _⟩,
          .keep _, .keep _, .keep _, .keep _⟩, .keep _, .keep _⟩
  | done q x out => cases h

/-- Every actual search successor obeys the same fixed thirteen-tape bit-RAM rule. -/
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
  rw [BinaryInverseMachine.ramRunFuel_eq, h.runFuel_eq]

/-- Every lifted successor preserves memory and satisfies the same address-controller tape rule. -/
theorem ramStep_local {s t : AddressedBits.Memory × Configuration}
    (h : ramStep s = some t) :
    t.1 = s.1 ∧ BitLocalActions.BankStep (tapes s.2) (tapes t.2) := by
  obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
  cases ht
  exact ⟨rfl, step_local hs⟩

end Computation.BinaryInverseMachine
