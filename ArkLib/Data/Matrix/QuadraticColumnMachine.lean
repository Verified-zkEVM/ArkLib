/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.ColumnEliminationMachine
public import ArkLib.Data.Matrix.QuadraticPivotMachine

/-!
# Coordinate column elimination

Pivot validation runs a retained base equality payload. Each target executes the actual
coordinate pivot child. The pivot stays first, target order is retained, and outer cells and
reversal are explicit. Partial and rejected children remain observable. Wrapper and extra
cell-slot/root charges supplement source administrative costs; input materialization, host
fuel, reclamation and bit time are excluded.
-/

@[expose] public section

namespace Matrix.QuadraticColumnMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev administrative := QuadraticPivotMachine.administrative
abbrev launch := QuadraticPivotMachine.launch
abbrev zeroSeed := QuadraticPivotMachine.zeroSeed
abbrev returned := QuadraticPivotMachine.returned
abbrev wrapper := QuadraticPivotMachine.rowWrapper

/-- One additional root/slot write for source outer-cell allocations. -/
def allocation : Cost := ⟨{ data := 1 }, 0⟩

inductive Configuration (F : Type*) where
  | ready (state : ColumnEliminationMachine.Configuration (Pair F))
  | checking (pivot : List (Pair F)) (rows : List (List (Pair F)))
      (payload : ArithmeticMachine.Input F) (state : ArithmeticMachine.Configuration F)
  | pivot (head : List (Pair F)) (rows reversed : List (List (Pair F)))
      (state : QuadraticPivotMachine.Configuration F)

/-- Source delegated states enter the actual coordinate pivot interpreter. -/
def enter {F : Type*} : ColumnEliminationMachine.Configuration (Pair F) → Configuration F
  | .row p rows rev s => .pivot p rows rev (QuadraticPivotMachine.enter s)
  | s => .ready s

/-- A materialized equality result selects rejection or allocates the pivot output singleton. -/
def checked {F : Type*} (p : List (Pair F)) (rows : List (List (Pair F))) (b : Bool) :
    Configuration F × Cost :=
  if b then (.ready .rejected, administrative ColumnEliminationMachine.zeroCost + returned)
  else (.ready (.scan p rows [p]),
    (administrative ColumnEliminationMachine.validCost + allocation) + returned)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Every transition is local allocation/traversal or one actual child instruction. -/
def step (a : F) (j : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .ready (.begin []) | .ready (.validate _ _ [] _) =>
      some (.ready .rejected, administrative ColumnEliminationMachine.rejectCost)
  | .ready (.begin (p :: rows)) =>
      some (.ready (.validate p rows p j), administrative ColumnEliminationMachine.beginCost)
  | .ready (.validate p rows (_ :: xs) (i + 1)) =>
      some (.ready (.validate p rows xs i), administrative ColumnEliminationMachine.seekCost)
  | .ready (.validate p rows (x :: _) 0) =>
      some (.ready (.check p rows x), administrative ColumnEliminationMachine.hitCost)
  | .ready (.check p rows x) =>
      some (.checking p rows ⟨a, x, (0, 0)⟩ (.start .equal), launch + zeroSeed)
  | .ready (.scan p (t :: ts) rev) =>
      some (.pivot p ts rev (.ready (.lookup p t p t j)),
        administrative ColumnEliminationMachine.callCost)
  | .ready (.scan _ [] rev) =>
      some (.ready (.reverse rev []), administrative ColumnEliminationMachine.beginReverseCost)
  | .ready (.row p rows rev s) => some (.pivot p rows rev (QuadraticPivotMachine.enter s), wrapper)
  | .ready (.reverse (r :: rs) out) =>
      some (.ready (.reverse rs (r :: out)),
        administrative ColumnEliminationMachine.reverseCost + allocation)
  | .ready (.reverse [] out) =>
      some (.ready (.done out), administrative ColumnEliminationMachine.emitCost)
  | .ready (.done _) | .ready .rejected => none
  | .checking p rows payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.checking p rows payload t, delegated c)
      | none => match s with
          | .done (.boolean b) => some (checked p rows b)
          | _ => none
  | .pivot p rows rev s => match QuadraticPivotMachine.step a s with
      | some (t, c) => some (.pivot p rows rev t, c + wrapper)
      | none => match s with
          | .ready (.done out) => some (.ready (.scan p rows (out :: rev)),
              administrative ColumnEliminationMachine.storeCost + allocation)
          | .ready .rejected =>
              some (.ready .rejected, administrative ColumnEliminationMachine.rejectCost)
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

end Matrix.QuadraticColumnMachine
