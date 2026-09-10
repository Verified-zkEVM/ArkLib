/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BitLocalActions
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype

/-!
# Finite control with head-only observations of a fixed bit-tape bank

The dispatch table receives only a finite control label and one optional bit per tape. It
returns a control label and one keep, pop or literal-bit push per tape. Whole words never enter
that interface. All updates read the old bank simultaneously. Popping an empty tape keeps it
empty. This strengthens locality with an explicit restriction on how instructions are selected;
it is not a global RAM compiler or a bound on address, heap or scalar arithmetic.
-/

@[expose] public section

namespace Computation.FiniteHeadProgram

/-- The entire instruction vocabulary for one tape. -/
inductive Action where
  | keep
  | pop
  | push (bit : Bool)
  deriving DecidableEq, Repr, Fintype

/-- One literal action changes at most one cell; an empty pop has no effect. -/
def Action.apply : Action → List Bool → List Bool
  | .keep, bits => bits
  | .pop, bits => bits.tail
  | .push b, bits => b :: bits

/-- A program-fixed finite bank of optional head observations. -/
abbrev Heads (tapes : ℕ) := Fin tapes → Option Bool

/-- A fixed finite controller cannot receive a whole tape through its dispatch interface. -/
structure Program (states tapes : ℕ) where
  dispatch : Fin states → Heads tapes → Option (Fin states × (Fin tapes → Action))

/-- The table itself belongs to a finite type: both observations and selected actions are finite. -/
instance (states tapes : ℕ) : Finite (Program states tapes) :=
  Finite.of_injective Program.dispatch (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

/-- Unbounded words are stored only in the tape bank, outside the finite control. -/
structure Configuration (states tapes : ℕ) where
  control : Fin states
  bank : Fin tapes → List Bool
  deriving DecidableEq

/-- Observe exactly one head, or emptiness, on each fixed physical tape. -/
def observe {tapes : ℕ} (bank : Fin tapes → List Bool) : Heads tapes :=
  fun i ↦ (bank i).head?

/-- Execute all actions against the previous bank, without tape renaming or exchange. -/
def applyActions {tapes : ℕ} (actions : Fin tapes → Action) (bank : Fin tapes → List Bool) :
    Fin tapes → List Bool := fun i ↦ (actions i).apply (bank i)

/-- Instruction selection factors through finite control and the finite head observation. -/
def decision {states tapes : ℕ} (program : Program states tapes)
    (state : Configuration states tapes) : Option (Fin states × (Fin tapes → Action)) :=
  program.dispatch state.control (observe state.bank)

/-- One actual transition; a missing table entry halts without changing any tape. -/
def step {states tapes : ℕ} (program : Program states tapes)
    (state : Configuration states tapes) : Option (Configuration states tapes) :=
  (decision program state).map fun instruction ↦
    ⟨instruction.1, applyActions instruction.2 state.bank⟩

/-- Equal current observations force the same instruction, regardless of all hidden tails. -/
theorem decision_eq_of_heads_eq {states tapes : ℕ} (program : Program states tapes)
    {s t : Configuration states tapes} (hc : s.control = t.control)
    (hh : observe s.bank = observe t.bank) : decision program s = decision program t := by
  simp only [decision, hc, hh]

/-- Every literal tape action satisfies the shared local storage relation. -/
theorem Action.local (action : Action) (bits : List Bool) :
    BitLocalActions.CellStep bits (action.apply bits) := by
  cases action with
  | keep => exact .keep _
  | pop => cases bits <;> constructor
  | push b => exact .push _ _

/-- Actual table-selected transitions inherit tape locality; locality alone is not the model. -/
theorem step_local {states tapes : ℕ} {program : Program states tapes}
    {s t : Configuration states tapes} (h : step program s = some t) :
    BitLocalActions.BankStep s.bank t.bank := by
  cases hd : decision program s with
  | none => simp only [step, hd, Option.map_none, reduceCtorEq] at h
  | some instruction =>
      simp only [step, hd, Option.map_some, Option.some.injEq] at h
      subst t
      intro i
      exact (instruction.2 i).local (s.bank i)

/-- A trace counts actual selected instructions, with no batch operation hidden in an edge. -/
inductive Trace {states tapes : ℕ} (program : Program states tapes) :
    ℕ → Configuration states tapes → Configuration states tapes → Prop where
  | nil (s) : Trace program 0 s s
  | cons {n s u t} (head : step program s = some u) (tail : Trace program n u t) :
      Trace program (n + 1) s t

/-- Fuel bounds dispatched instructions, including incomplete and already halted runs. -/
def runFuel {states tapes : ℕ} (program : Program states tapes) :
    ℕ → Configuration states tapes → Configuration states tapes
  | 0, s => s
  | n + 1, s => match step program s with
      | none => s
      | some t => runFuel program n t

/-- The finite-head trace and the actual interpreter have the identical endpoint and count. -/
theorem Trace.runFuel_eq {states tapes n : ℕ} {program : Program states tapes}
    {s t : Configuration states tapes} (h : Trace program n s t) : runFuel program n s = t := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Computation.FiniteHeadProgram
