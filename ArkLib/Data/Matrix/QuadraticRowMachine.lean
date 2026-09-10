/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.RowReductionMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationMachine

/-!
# Coordinate row-add-multiple execution

Materialized coordinate rows are scanned in lockstep. Each multiplication and addition runs
one retained arithmetic payload through its actual base instructions. Addition returns a pair
to a separate cell-allocation phase; explicit reversal preserves entry order. Unequal lengths
reject without emitting a partial row. Augmented entries are processed like every other entry.

The ledger charges administrative accesses, call setup, each child instruction and wrapper,
returns, cell slots/root writes and output. Unchanged registers and lists are shared. Input
preparation, reclamation, host fuel and compiled/bit time are outside this primitive model.
-/

@[expose] public section

namespace Matrix.QuadraticRowMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F

/-- Retain the row machine's administrative costs without abstract field operations. -/
def administrative (c : RowReductionMachine.Cost) : Cost :=
  ⟨{ control := c.control, data := c.data, output := c.output }, 0⟩
/-- Read and store parameter and two operands once. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩
/-- Read the returned pair and write the resumed scalar register. -/
def returned : Cost := ⟨{ control := 1, data := 3 }, 0⟩
/-- Read pair/root, write the two cell slots and the new root. -/
def saveCost : Cost := ⟨{ control := 1, data := 5 }, 0⟩

/-- Fixed return destinations retain the original row cursors and accumulator. -/
inductive Continuation (F : Type*) where
  | product (target source reversed : List (Pair F)) (entry : Pair F)
  | sum (target source reversed : List (Pair F))

inductive Configuration (F : Type*) where
  | ready (state : RowReductionMachine.Configuration (Pair F))
  | call (continuation : Continuation F) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)
  | save (target source reversed : List (Pair F)) (entry : Pair F)

/-- Install a materialized arithmetic result without recomputing the saved input. -/
def resume {F : Type*} : Continuation F → Pair F → Configuration F
  | .product ts ss rev t, p => .ready (.add ts ss rev t p)
  | .sum ts ss rev, p => .save ts ss rev p

variable {F : Type*} [Field F] [DecidableEq F]

/-- Closed dispatch exposes every scalar instruction, allocation and traversal. -/
def step (a : F) (scalar : Pair F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.scan [] [] rev) =>
      some (.ready (.reverse rev []), administrative RowReductionMachine.beginReverseCost)
  | .ready (.scan [] (_ :: _) _) | .ready (.scan (_ :: _) [] _) =>
      some (.ready .rejected, administrative RowReductionMachine.rejectCost)
  | .ready (.scan (t :: ts) (s :: ss) rev) =>
      some (.ready (.multiply ts ss rev t s), administrative RowReductionMachine.takeCost)
  | .ready (.multiply ts ss rev t s) =>
      some (.call (.product ts ss rev t) ⟨a, scalar, s⟩ (.start .mul),
        administrative RowReductionMachine.multiplyCost + launch)
  | .ready (.add ts ss rev t p) =>
      some (.call (.sum ts ss rev) ⟨a, t, p⟩ (.start .add), launch)
  | .save ts ss rev p => some (.ready (.scan ts ss (p :: rev)), saveCost)
  | .ready (.reverse (x :: xs) out) =>
      some (.ready (.reverse xs (x :: out)), administrative RowReductionMachine.reverseCost)
  | .ready (.reverse [] out) =>
      some (.ready (.done out), administrative RowReductionMachine.emitCost)
  | .ready (.done _) | .ready .rejected => none
  | .call cont payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.call cont payload t, delegated c)
      | none => match s with
          | .done (.pair p) => some (resume cont p, returned)
          | _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) (scalar : Pair F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a scalar 0 s 0 s
  | cons {n s u t c d} (head : step a scalar s = some (u, c)) (tail : Trace a scalar n u d t) :
      Trace a scalar (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {scalar : Pair F} {s t : Configuration F} {c : Cost}
    (h : step a scalar s = some (t, c)) : Trace a scalar 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {scalar : Pair F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a scalar n s c u) (h' : Trace a scalar m u d t) :
    Trace a scalar (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) (scalar : Pair F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a scalar s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a scalar n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {scalar : Pair F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a scalar n s c t) : runFuel a scalar n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Matrix.QuadraticRowMachine
