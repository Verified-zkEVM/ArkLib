/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.ForwardEchelonMachine
public import ArkLib.Data.Matrix.QuadraticSelectionMachine
public import ArkLib.Data.Matrix.QuadraticAugmentMachine

/-!
# Coordinate forward-echelon execution

The driver retains actual selection and augmented-column child states. Each child instruction
keeps its full ledger and adds outer dispatch/root charges. Column advancement, pivot storage,
reversal and output remain explicit. Residual rows retain their RHS values, and malformed or
failed child returns reject. Extra indexed-pair/cell writes supplement the source ledger.
Input preparation, host fuel, reclamation and bit time are excluded.
-/

@[expose] public section

namespace Matrix.QuadraticForwardEchelonMachine

open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Row (F : Type*) := ForwardEchelonMachine.Row (Pair F)
abbrev Pivot (F : Type*) := ForwardEchelonMachine.Pivot (Pair F)
abbrev administrative := QuadraticPivotMachine.administrative
abbrev wrapper := QuadraticPivotMachine.rowWrapper

/-- Supplement the source's bundled pair/cell allocations with extra slot writes. -/
def allocation (n : ℕ) : Cost := ⟨{ data := n }, 0⟩

inductive Configuration (F : Type*) where
  | ready (state : ForwardEchelonMachine.Configuration (Pair F))
  | select (column left : ℕ) (completed : List (Pivot F))
      (state : QuadraticSelectionMachine.Configuration F)
  | eliminate (column left : ℕ) (completed : List (Pivot F))
      (state : QuadraticAugmentMachine.Configuration F)

/-- Source child phases enter their actual coordinate interpreter, preserving suspended state. -/
def enter {F : Type*} : ForwardEchelonMachine.Configuration (Pair F) → Configuration F
  | .select j left rev s => .select j left rev (.ready s)
  | .eliminate j left rev s => .eliminate j left rev (QuadraticAugmentMachine.enter s)
  | s => .ready s

variable {F : Type*} [Field F] [DecidableEq F]

/-- One local driver transition or one actual child step with its full wrapper cost. -/
def step (a : F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.loop j (left + 1) rows rev) =>
      some (.select j left rev (.ready (.scan rows [])),
        administrative ForwardEchelonMachine.selectCost)
  | .ready (.loop _ 0 rows rev) =>
      some (.ready (.reverse rev [] rows), administrative ForwardEchelonMachine.finishCost)
  | .ready (.select j left rev s) => some (.select j left rev (.ready s), wrapper)
  | .ready (.eliminate j left rev s) =>
      some (.eliminate j left rev (QuadraticAugmentMachine.enter s), wrapper)
  | .ready (.reverse (p :: ps) out rest) =>
      some (.ready (.reverse ps (p :: out) rest),
        administrative ForwardEchelonMachine.reverseCost + allocation 1)
  | .ready (.reverse [] out rest) =>
      some (.ready (.done out rest), administrative ForwardEchelonMachine.emitCost)
  | .ready (.done _ _) | .ready .rejected => none
  | .select j left rev s => match QuadraticSelectionMachine.step a j s with
      | some (t, c) => some (.select j left rev t, c + wrapper)
      | none => match s with
          | .ready (.done false rows) =>
              some (.ready (.loop (j + 1) left rows rev),
                administrative ForwardEchelonMachine.nextCost)
          | .ready (.done true (p :: rows)) =>
              some (.eliminate j left rev (.ready (.pack (p :: rows) [])),
                administrative ForwardEchelonMachine.eliminateCost)
          | .ready (.done true []) | .ready .rejected =>
              some (.ready .rejected, administrative ForwardEchelonMachine.rejectCost)
          | _ => none
  | .eliminate j left rev s => match QuadraticAugmentMachine.step a j s with
      | some (t, c) => some (.eliminate j left rev t, c + wrapper)
      | none => match s with
          | .ready (.done (p :: rows)) =>
              some (.ready (.loop (j + 1) left rows ((j, p) :: rev)),
                administrative ForwardEchelonMachine.storeCost + allocation 2)
          | .ready (.done []) | .ready .rejected =>
              some (.ready .rejected, administrative ForwardEchelonMachine.rejectCost)
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

end Matrix.QuadraticForwardEchelonMachine
