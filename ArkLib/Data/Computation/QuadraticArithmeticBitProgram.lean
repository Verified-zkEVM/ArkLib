/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.QuadraticArithmeticBitAddExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitMulExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitNegExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitInvExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitEqualExecution
public import ArkLib.Data.Computation.QuadraticArithmeticBitLoad
public import ArkLib.Data.Computation.QuadraticArithmeticBitBoolean
public import ArkLib.Data.Computation.QuadraticRegisterInitialization

/-!
# One physical controller for the literal quadratic arithmetic programs

The code cursor contains at most thirteen finite instructions. Child transitions execute the
verified register initializer, input loads, scalar instructions and result emitters. All children
share the same twenty-eight physical tapes and RAM. Each dispatch and return costs one actual
successor. EQUAL returns adopt its physically written `resultFlags`, not its old finite flag frame.

This module proves physical handoffs and child trace lifting. A whole-program semantic refinement
and a uniform total transition bound are separate obligations; individual instruction bounds must
not be treated as an already composed program theorem. Head-observation adequacy is also separate.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitProgram

open BinaryWordMachine (Word value)
open QuadraticAlgebra

abbrev Registers := Fin 8 → Word
abbrev Inputs := Fin 5 → Word
abbrev Flags := Fin 2 → Bool
abbrev Slot := Fin 13 ⊕ (Fin 8 ⊕ (Fin 5 ⊕ Fin 2))

/-- Bounded finite instruction metadata; no unbounded data-word cursor is a control field. -/
abbrev Code := { instructions : List ArithmeticMachine.Instruction // instructions.length ≤ 13 }

def literalCode (op : ArithmeticMachine.Operation) : Code :=
  ⟨ArithmeticMachine.program op, by cases op <;> decide⟩

def tailCode (code : Code) : Code := ⟨code.val.tail, by
  have h := code.property
  cases hs : code.val with
  | nil => simp
  | cons i rest => simp only [hs, List.length_cons] at h; simpa using (by omega : rest.length ≤ 13)⟩

inductive Control where
  | initializing (code : Code) (input : Inputs) (child : QuadraticRegisterInitialization.Control)
  | ready (code : Code) (q : Word) (r : Registers) (input : Inputs) (flags : Flags)
  | load (code : Code) (flags : Flags) (child : QuadraticArithmeticBitLoad.Control)
  | add (code : Code) (input : Inputs) (flags : Flags)
      (child : QuadraticArithmeticBitAdd.Control)
  | mul (code : Code) (input : Inputs) (flags : Flags)
      (child : QuadraticArithmeticBitMul.Control)
  | neg (code : Code) (input : Inputs) (flags : Flags)
      (child : QuadraticArithmeticBitNeg.Control)
  | inv (code : Code) (input : Inputs) (flags : Flags)
      (child : QuadraticArithmeticBitInv.Control)
  | equal (code : Code) (input : Inputs) (flags : Flags)
      (child : QuadraticArithmeticBitEqual.Control)
  | pair (input : Inputs) (flags : Flags) (child : QuadraticArithmeticBitPair.Control)
  | boolean (input : Inputs) (child : QuadraticArithmeticBitBoolean.Control)

/-- Literal instruction selection constructs the child entry on the very same occupied tapes. -/
def launch (code : Code) (q : Word) (r : Registers) (input : Inputs) (flags : Flags) :
    ArithmeticMachine.Instruction → Control
  | .load source dst => .load code flags
      (.start q (QuadraticArithmeticBitLoad.sourceIndex source) dst r input)
  | .add x y dst => .add code input flags (.start q x y dst r)
  | .mul x y dst => .mul code input flags (.start q x y dst r)
  | .neg x dst => .neg code input flags (.start q x dst r)
  | .inv x dst => .inv code input flags (.start q x dst r)
  | .equal x y dst => .equal code input flags (.start q x y dst r)
  | .pair x y => .pair input flags (.start q x y r)
  | .boolean => .boolean input (.start q r flags)

/-- Only literal child successors and finite-control dispatch/return instructions execute here. -/
def step : Control → Option Control
  | .initializing code input child =>
      match QuadraticRegisterInitialization.step child with
      | some next => some (.initializing code input next)
      | none => match child with
          | .done q r => some (.ready code q r input (fun _ ↦ false))
          | _ => none
  | .ready code q r input flags => match code.val with
      | [] => none
      | i :: _ => some (launch (tailCode code) q r input flags i)
  | .load code flags child =>
      match QuadraticArithmeticBitLoad.step child with
      | some next => some (.load code flags next)
      | none => match child with
          | .done q r input => some (.ready code q r input flags)
          | _ => none
  | .add code input flags child =>
      match QuadraticArithmeticBitAdd.step child with
      | some next => some (.add code input flags next)
      | none => match child with
          | .done q r => some (.ready code q r input flags)
          | _ => none
  | .mul code input flags child =>
      match QuadraticArithmeticBitMul.step child with
      | some next => some (.mul code input flags next)
      | none => match child with
          | .done q r => some (.ready code q r input flags)
          | _ => none
  | .neg code input flags child =>
      match QuadraticArithmeticBitNeg.step child with
      | some next => some (.neg code input flags next)
      | none => match child with
          | .done q r => some (.ready code q r input flags)
          | _ => none
  | .inv code input flags child =>
      match QuadraticArithmeticBitInv.step child with
      | some next => some (.inv code input flags next)
      | none => match child with
          | .done q r => some (.ready code q r input flags)
          | _ => none
  | .equal code input flags child =>
      match QuadraticArithmeticBitEqual.step child with
      | some next => some (.equal code input flags next)
      | none => match child with
          | .done q r dst result => some (.ready code q r input (Function.update flags dst result))
          | _ => none
  | .pair input flags child =>
      (QuadraticArithmeticBitPair.step child).map (.pair input flags)
  | .boolean input child =>
      (QuadraticArithmeticBitBoolean.step child).map (.boolean input)

def readyTapes (q : Word) (r : Registers) (input : Inputs) (flags : Flags) : Slot → Word
  | .inl i => ![[], [], [], [], q, [], [], [], [], [], [], [], []] i
  | .inr (.inl i) => r i
  | .inr (.inr (.inl i)) => input i
  | .inr (.inr (.inr i)) => [flags i]

def tapes : Control → Slot → Word
  | .initializing _ input child => QuadraticRegisterInitialization.tapes input child
  | .ready _ q r input flags => readyTapes q r input flags
  | .load _ flags child => QuadraticArithmeticBitLoad.tapes flags child
  | .add _ input flags child => QuadraticArithmeticBitAdd.tapes input flags child
  | .mul _ input flags child => QuadraticArithmeticBitMul.tapes input flags child
  | .neg _ input flags child => QuadraticArithmeticBitNeg.tapes input flags child
  | .inv _ input flags child => QuadraticArithmeticBitInv.tapes input flags child
  | .equal _ input flags child => QuadraticArithmeticBitEqual.tapes input flags child
  | .pair input flags child => QuadraticArithmeticBitPair.tapes input flags child
  | .boolean input child => QuadraticArithmeticBitBoolean.tapes input child

/-- Dispatch preserves each word literally; the source instruction only selects finite control. -/
theorem launch_tapes (code : Code) (q : Word) (r : Registers) (input : Inputs) (flags : Flags)
    (i : ArithmeticMachine.Instruction) :
    tapes (launch code q r input flags i) = readyTapes q r input flags := by
  cases i <;> funext slot
  all_goals rcases slot with i | i
  all_goals fin_cases i <;> rfl

theorem initialize_handoff (code : Code) (input : Inputs) (q : Word) (r : Registers) :
    tapes (.initializing code input (.done q r)) =
      tapes (.ready code q r input (fun _ ↦ false)) := by
  funext slot
  rcases slot with i | i
  · fin_cases i <;> rfl
  · rcases i with i | i
    · rfl
    · cases i <;> rfl

theorem load_handoff (code : Code) (flags : Flags) (q : Word) (r : Registers) (input : Inputs) :
    tapes (.load code flags (.done q r input)) = tapes (.ready code q r input flags) := by
  funext slot
  rcases slot with i | i
  · fin_cases i <;> rfl
  · rcases i with i | i
    · rfl
    · cases i <;> rfl

theorem add_handoff (code : Code) (input : Inputs) (flags : Flags) (q : Word) (r : Registers) :
    tapes (.add code input flags (.done q r)) = tapes (.ready code q r input flags) := by
  funext slot
  rcases slot with i | i
  · fin_cases i <;> rfl
  · rcases i with i | i
    · rfl
    · cases i <;> rfl

theorem mul_handoff (code : Code) (input : Inputs) (flags : Flags) (q : Word) (r : Registers) :
    tapes (.mul code input flags (.done q r)) = tapes (.ready code q r input flags) := by
  funext slot
  rcases slot with i | i
  · fin_cases i <;> rfl
  · rcases i with i | i
    · rfl
    · cases i <;> rfl

theorem neg_handoff (code : Code) (input : Inputs) (flags : Flags) (q : Word) (r : Registers) :
    tapes (.neg code input flags (.done q r)) = tapes (.ready code q r input flags) := by
  funext slot
  rcases slot with i | i
  · fin_cases i <;> rfl
  · rcases i with i | i
    · rfl
    · cases i <;> rfl

theorem inv_handoff (code : Code) (input : Inputs) (flags : Flags) (q : Word) (r : Registers) :
    tapes (.inv code input flags (.done q r)) = tapes (.ready code q r input flags) := by
  funext slot
  rcases slot with i | i
  · fin_cases i <;> rfl
  · rcases i with i | i
    · rfl
    · cases i <;> rfl

theorem equal_handoff (code : Code) (input : Inputs) (flags : Flags) (q : Word)
    (r : Registers) (dst : Fin 2) (result : Bool) :
    tapes (.equal code input flags (.done q r dst result)) =
      tapes (.ready code q r input (Function.update flags dst result)) := by
  funext slot
  rcases slot with i | i
  · fin_cases i <;> rfl
  · rcases i with i | i
    · rfl
    · rcases i with i | i
      · rfl
      · by_cases hi : i = dst
        · subst i; simp [tapes, readyTapes, QuadraticArithmeticBitEqual.tapes,
            QuadraticArithmeticBitEqual.flagWords]
        · simp [tapes, readyTapes, QuadraticArithmeticBitEqual.tapes,
            QuadraticArithmeticBitEqual.flagWords, Function.update_of_ne hi]

/-- Every actual transition, including adoption of the new equality flag, is tape-local. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  cases s with
  | initializing code input child =>
      cases hs : QuadraticRegisterInitialization.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact QuadraticRegisterInitialization.step_local hs input
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          rw [initialize_handoff]
          intro i
          exact .keep _
  | ready code q r input flags =>
      cases hc : code.val with
      | nil => simp only [step, hc] at h; cases h
      | cons i rest =>
          simp only [step, hc, Option.some.injEq] at h
          subst t
          rw [launch_tapes]
          intro i
          exact .keep _
  | load code flags child =>
      cases hs : QuadraticArithmeticBitLoad.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact QuadraticArithmeticBitLoad.step_local hs flags
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          rw [load_handoff]
          intro i
          exact .keep _
  | add code input flags child =>
      cases hs : QuadraticArithmeticBitAdd.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact QuadraticArithmeticBitAdd.step_local hs input flags
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          rw [add_handoff]
          intro i
          exact .keep _
  | mul code input flags child =>
      cases hs : QuadraticArithmeticBitMul.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact QuadraticArithmeticBitMul.step_local hs input flags
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          rw [mul_handoff]
          intro i
          exact .keep _
  | neg code input flags child =>
      cases hs : QuadraticArithmeticBitNeg.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact QuadraticArithmeticBitNeg.step_local hs input flags
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          rw [neg_handoff]
          intro i
          exact .keep _
  | inv code input flags child =>
      cases hs : QuadraticArithmeticBitInv.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact QuadraticArithmeticBitInv.step_local hs input flags
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          rw [inv_handoff]
          intro i
          exact .keep _
  | equal code input flags child =>
      cases hs : QuadraticArithmeticBitEqual.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact QuadraticArithmeticBitEqual.step_local hs input flags
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          rw [equal_handoff]
          intro i
          exact .keep _
  | pair input flags child =>
      obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
      cases ht
      exact QuadraticArithmeticBitPair.step_local hs input flags
  | boolean input child =>
      obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
      cases ht
      exact QuadraticArithmeticBitBoolean.step_local hs input

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

theorem Trace.runFuel_eq
    {n : ℕ} {s t : Control} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

theorem lift_initializing (code : Code) (input : Inputs)
    {n : ℕ} {s t : QuadraticRegisterInitialization.Control}
    (h : QuadraticRegisterInitialization.Trace n s t) :
    Trace n (.initializing code input s) (.initializing code input t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_load (code : Code) (flags : Flags)
    {n : ℕ} {s t : QuadraticArithmeticBitLoad.Control}
    (h : QuadraticArithmeticBitLoad.Trace n s t) :
    Trace n (.load code flags s) (.load code flags t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_add (code : Code) (input : Inputs) (flags : Flags)
    {n : ℕ} {s t : QuadraticArithmeticBitAdd.Control}
    (h : QuadraticArithmeticBitAdd.Trace n s t) :
    Trace n (.add code input flags s) (.add code input flags t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_mul (code : Code) (input : Inputs) (flags : Flags)
    {n : ℕ} {s t : QuadraticArithmeticBitMul.Control}
    (h : QuadraticArithmeticBitMul.Trace n s t) :
    Trace n (.mul code input flags s) (.mul code input flags t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_neg (code : Code) (input : Inputs) (flags : Flags)
    {n : ℕ} {s t : QuadraticArithmeticBitNeg.Control}
    (h : QuadraticArithmeticBitNeg.Trace n s t) :
    Trace n (.neg code input flags s) (.neg code input flags t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_inv (code : Code) (input : Inputs) (flags : Flags)
    {n : ℕ} {s t : QuadraticArithmeticBitInv.Control}
    (h : QuadraticArithmeticBitInv.Trace n s t) :
    Trace n (.inv code input flags s) (.inv code input flags t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_equal (code : Code) (input : Inputs) (flags : Flags)
    {n : ℕ} {s t : QuadraticArithmeticBitEqual.Control}
    (h : QuadraticArithmeticBitEqual.Trace n s t) :
    Trace n (.equal code input flags s) (.equal code input flags t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_pair (input : Inputs) (flags : Flags)
    {n : ℕ} {s t : QuadraticArithmeticBitPair.Control}
    (h : QuadraticArithmeticBitPair.Trace n s t) :
    Trace n (.pair input flags s) (.pair input flags t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head, Option.map_some]) ih

theorem lift_boolean (input : Inputs)
    {n : ℕ} {s t : QuadraticArithmeticBitBoolean.Control}
    (h : QuadraticArithmeticBitBoolean.Trace n s t) :
    Trace n (.boolean input s) (.boolean input t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head, Option.map_some]) ih

/-- The unified controller physically initializes its scalar/flag bank before its first dispatch. -/
theorem initialized_trace (op : ArithmeticMachine.Operation) (q : Word) (input : Inputs) :
    Trace (19 * q.length + 41)
      (.initializing (literalCode op) input (.literal (.start q false)))
      (.ready (literalCode op) q (fun _ ↦ List.replicate q.length false)
        input (fun _ ↦ false)) := by
  have hi := lift_initializing (literalCode op) input
    (QuadraticRegisterInitialization.initialization_trace q)
  have hh : Trace 1
      (.initializing (literalCode op) input (.done q (fun _ ↦ List.replicate q.length false)))
      (.ready (literalCode op) q (fun _ ↦ List.replicate q.length false) input (fun _ ↦ false)) :=
    .cons rfl (.nil _)
  convert hi.append hh using 1

structure Configuration where
  memory : AddressedBits.Memory
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

/-- Only literal child output states count as completed results. -/
def output : Control → Option (ArithmeticMachine.Result Word)
  | .pair _ _ (.done _ _ left right) => some (.pair (left, right))
  | .boolean _ (.done _ _ _ result) => some (.boolean result)
  | _ => none

end Computation.QuadraticArithmeticBitProgram
