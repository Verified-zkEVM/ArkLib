/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotSelectionMachine
public import ArkLib.Data.Matrix.QuadraticPivotMachine

/-!
# Coordinate first-pivot selection

The first nonzero coefficient is selected by actual base equality instructions with a retained
input record. Zero rows are saved and restored in order around the pivot; untouched tails and
RHS values are shared. Missing entries reject only when scanned. All output cells, the selected
option, zero literals and child wrappers are charged explicitly. Input preparation, host fuel,
reclamation and bit time are outside this primitive ledger.
-/

@[expose] public section

namespace Matrix.QuadraticSelectionMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Row (F : Type*) := PivotSelectionMachine.Row (Pair F)
abbrev administrative := QuadraticPivotMachine.administrative
abbrev launch := QuadraticPivotMachine.launch
abbrev zeroSeed := QuadraticPivotMachine.zeroSeed
abbrev returned := QuadraticPivotMachine.returned

/-- Supplement a bundled source allocation with its additional slot/root or option write. -/
def allocation : Cost := ⟨{ data := 1 }, 0⟩

inductive Configuration (F : Type*) where
  | ready (state : PivotSelectionMachine.Configuration (Pair F))
  | checking (candidate : Row F) (rows saved : List (Row F))
      (payload : ArithmeticMachine.Input F) (state : ArithmeticMachine.Configuration F)

/-- Consume a materialized equality result, saving a zero row or remembering the first pivot. -/
def checked {F : Type*} (r : Row F) (rows saved : List (Row F)) (b : Bool) :
    Configuration F × Cost :=
  if b then (.ready (.scan rows (r :: saved)),
    (administrative PivotSelectionMachine.zeroCost + allocation) + returned)
  else (.ready (.restore (some r) saved rows),
    (administrative PivotSelectionMachine.foundCost + allocation) + returned)

variable {F : Type*} [Field F] [DecidableEq F]

/-- One explicit selection/list step or actual retained arithmetic child instruction. -/
def step (a : F) (j : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .ready (.scan (r :: rows) saved) =>
      some (.ready (.lookup r rows saved r.1 j), administrative PivotSelectionMachine.takeCost)
  | .ready (.scan [] saved) =>
      some (.ready (.restore none saved []), administrative PivotSelectionMachine.exhaustedCost)
  | .ready (.lookup r rows saved (_ :: xs) (i + 1)) =>
      some (.ready (.lookup r rows saved xs i), administrative PivotSelectionMachine.seekCost)
  | .ready (.lookup r rows saved (x :: _) 0) =>
      some (.ready (.check r rows saved x), administrative PivotSelectionMachine.hitCost)
  | .ready (.lookup _ _ _ [] _) =>
      some (.ready .rejected, administrative PivotSelectionMachine.rejectCost)
  | .ready (.check r rows saved x) =>
      some (.checking r rows saved ⟨a, x, (0, 0)⟩ (.start .equal), launch + zeroSeed)
  | .ready (.restore p (r :: rs) out) =>
      some (.ready (.restore p rs (r :: out)),
        administrative PivotSelectionMachine.reverseCost + allocation)
  | .ready (.restore none [] out) =>
      some (.ready (.emit false out), administrative PivotSelectionMachine.finishCost)
  | .ready (.restore (some p) [] out) =>
      some (.ready (.emit true (p :: out)),
        administrative PivotSelectionMachine.assembleCost + allocation)
  | .ready (.emit b out) =>
      some (.ready (.done b out), administrative PivotSelectionMachine.emitCost)
  | .ready (.done _ _) | .ready .rejected => none
  | .checking r rows saved payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.checking r rows saved payload t, delegated c)
      | none => match s with
          | .done (.boolean b) => some (checked r rows saved b)
          | _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) (j : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a j 0 s 0 s
  | cons {n s u t c d} (head : step a j s = some (u, c)) (tail : Trace a j n u d t) :
      Trace a j (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : step a j s = some (t, c)) : Trace a j 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {j n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a j n s c u) (h' : Trace a j m u d t) : Trace a j (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) (j : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a j s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a j n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {j n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a j n s c t) : runFuel a j n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Matrix.QuadraticSelectionMachine
