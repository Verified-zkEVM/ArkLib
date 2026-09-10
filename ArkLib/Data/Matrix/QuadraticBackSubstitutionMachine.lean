/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.BackSubstitutionMachine
public import ArkLib.Data.Matrix.QuadraticPivotSolveMachine

/-!
# Coordinate back substitution

Residual RHS values are tested by actual retained equality instructions before solving. The
pivot list is reversed explicitly and each row runs the retained coordinate PivotSolve child.
The call pays four input-record writes and two initial dot-zero writes/constants in addition
to source dispatch. Every child instruction retains its ledger and pays a driver wrapper.
Reversal pays the extra cell slot. Input preparation, host fuel and bit time are excluded.
-/

@[expose] public section

namespace Matrix.QuadraticBackSubstitutionMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Row (F : Type*) := ForwardEchelonMachine.Row (Pair F)
abbrev Pivot (F : Type*) := ForwardEchelonMachine.Pivot (Pair F)
abbrev administrative := QuadraticPivotMachine.administrative
abbrev wrapper := QuadraticPivotMachine.rowWrapper
abbrev launch := QuadraticPivotMachine.launch
abbrev zeroSeed := QuadraticPivotMachine.zeroSeed
abbrev returned := QuadraticPivotMachine.returned

/-- Additional materialized slots beyond the source's bundled writes. -/
def allocation (n : ℕ) : Cost := ⟨{ data := n }, 0⟩

inductive Configuration (F : Type*) where
  | ready (state : BackSubstitutionMachine.Configuration (Pair F))
  | checking (remaining : List (Row F)) (pivots : List (Pivot F)) (values : List (Pair F))
      (payload : ArithmeticMachine.Input F) (state : ArithmeticMachine.Configuration F)
  | row (input : QuadraticPivotSolveMachine.Input F) (pending : List (Pivot F))
      (state : QuadraticPivotSolveMachine.Configuration F)

/-- A source row phase enters the actual child with the original row and vector retained. -/
def enter {F : Type*} (a : F) : BackSubstitutionMachine.Configuration (Pair F) → Configuration F
  | .row p v ps s => .row ⟨a, p.2, p.1, v⟩ ps (.ready s)
  | s => .ready s

/-- Branch only on the materialized equality result. -/
def checked {F : Type*} (rs : List (Row F)) (ps : List (Pivot F)) (v : List (Pair F))
    (b : Bool) : Configuration F × Cost :=
  if b then (.ready (.check rs ps v), administrative BackSubstitutionMachine.checkCost + returned)
  else (.ready .inconsistent, administrative BackSubstitutionMachine.contradictionCost + returned)

variable {F : Type*} [Field F] [DecidableEq F]

/-- One local driver step or actual retained child instruction. -/
def step (a : F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.check (r :: rs) ps v) =>
      some (.checking rs ps v ⟨a, r.2, (0, 0)⟩ (.start .equal), launch + zeroSeed)
  | .ready (.check [] ps v) =>
      some (.ready (.reverse ps [] v), administrative BackSubstitutionMachine.checkEndCost)
  | .ready (.reverse (p :: ps) out v) =>
      some (.ready (.reverse ps (p :: out) v),
        administrative BackSubstitutionMachine.reverseCost + allocation 1)
  | .ready (.reverse [] ps v) =>
      some (.ready (.solve ps v), administrative BackSubstitutionMachine.reverseEndCost)
  | .ready (.solve (p :: ps) v) =>
      some (.row ⟨a, p.2, p.1, v⟩ ps (.ready (.dot p.2.1 v (0, 0))),
        (administrative BackSubstitutionMachine.callCost + allocation 4) + zeroSeed)
  | .ready (.solve [] v) =>
      some (.ready (.done v), administrative BackSubstitutionMachine.emitCost)
  | .ready (.row p v ps s) =>
      some (.row ⟨a, p.2, p.1, v⟩ ps (.ready s), wrapper + allocation 4)
  | .ready (.done _) | .ready .inconsistent | .ready .rejected => none
  | .checking rs ps v payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.checking rs ps v payload t, delegated c)
      | none => match s with
          | .done (.boolean b) => some (checked rs ps v b)
          | _ => none
  | .row input ps s => match QuadraticPivotSolveMachine.step input s with
      | some (t, c) => some (.row input ps t, c + wrapper)
      | none => match s with
          | .ready (.done out) =>
              some (.ready (.solve ps out), administrative BackSubstitutionMachine.returnCost)
          | .ready .rejected =>
              some (.ready .rejected, administrative BackSubstitutionMachine.rejectCost)
          | _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a 0 s 0 s
  | cons {n s u t c d} (head : step a s = some (u, c)) (tail : Trace a n u d t) :
      Trace a (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {s t : Configuration F} {c : Cost}
    (h : step a s = some (t, c)) : Trace a 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a n s c u) (h' : Trace a m u d t) :
    Trace a (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a n s c t) : runFuel a n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Matrix.QuadraticBackSubstitutionMachine
