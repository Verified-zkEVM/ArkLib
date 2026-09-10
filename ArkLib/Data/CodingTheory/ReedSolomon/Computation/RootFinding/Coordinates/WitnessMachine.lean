/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualWitnessMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticBatch
/-!
# Coordinate first-nonzero residual witness

The actual coordinate residual batch runs with a retained input record. Each residual is
compared to a materialized zero pair by the base arithmetic equality program. The first false
comparison emits its retained point; exhaustion emits none. The selected point is ordered, not
chosen existentially. Input construction, wrappers, point retention and emission are charged.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualWitnessMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Input := QuadraticResidualBatch.Input
abbrev Entry (F : Type*) := Pair F × Pair F

/-- Source administration survives; abstract field equality is replaced by actual instructions. -/
def administrative (c : ResidualWitnessMachine.Cost) : Cost :=
  ⟨{ control := c.machine.control, data := c.machine.data, output := c.machine.output },
    c.machine.natural⟩
/-- Each child instruction pays its outer dispatch and state-root accesses. -/
def wrapper : Cost := ⟨{ control := 1, data := 2 }, 0⟩
/-- Retained input and argument records require explicit slots. -/
def allocation (n : ℕ) : Cost := ⟨{ data := n }, 0⟩
/-- Retain the witness point and equality record; construct both zero coordinates. -/
def launch : Cost := ⟨{ control := 1, data := 11, constants := 2 }, 0⟩

inductive Configuration (F : Type*) where
  | start (samples : List (Pair F))
  | batch (payload : Input F) (state : QuadraticResidualBatch.Configuration F)
  | scan (remaining : List (Entry F))
  | check (point : Pair F) (remaining : List (Entry F)) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)
  | emit (result : Option (Pair F))
  | done (result : Option (Pair F))

variable {F : Type*} [Field F] [DecidableEq F]

/-- The actual equality Boolean controls advancement or selection of the retained point. -/
def checked (point : Pair F) (ps : List (Entry F)) (b : Bool) : Configuration F :=
  if b then .scan ps else .emit (some point)

/-- One child instruction or explicit outer transition; no bulk zero predicate executes. -/
def step (a : F) (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start ps => some (.batch
      ⟨input.coefficients, input.terms, input.center, input.order⟩ (.start ps),
      administrative ResidualWitnessMachine.entryCost + allocation 4)
  | .batch payload s => match QuadraticResidualBatch.step a payload s with
      | some (t, c) => some (.batch payload t, c + wrapper)
      | none => match s with
          | .done ps => some (.scan ps, administrative ResidualWitnessMachine.handoffCost)
          | _ => none
  | .scan [] => some (.emit none, administrative ResidualWitnessMachine.emptyCost)
  | .scan ((u, v) :: ps) => some (.check u ps ⟨a, v, (0, 0)⟩ (.start .equal), launch)
  | .check u ps payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.check u ps payload t, delegated c)
      | none => match s with
          | .done (.boolean b) =>
              some (checked u ps b, administrative ResidualWitnessMachine.checkCost)
          | _ => none
  | .emit b => some (.done b, administrative ResidualWitnessMachine.emitCost)
  | .done _ => none

/-- Concrete execution edges accumulate the full nested ledger. -/
inductive Trace (a : F) (input : Input F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a input 0 s 0 s
  | cons {n s u t c d} (head : step a input s = some (u, c))
      (tail : Trace a input n u d t) : Trace a input (n + 1) s (c + d) t

/-- Execute a single concrete transition. -/
theorem single {a : F} {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step a input s = some (t, c)) : Trace a input 1 s c t := by
  simpa using Trace.cons h (Trace.nil t)

/-- Compose actual runs without losing nested cost. -/
theorem Trace.trans {a : F} {input : Input F} {n m : ℕ}
    {s u t : Configuration F} {c d : Cost}
    (h : Trace a input n s c u) (h' : Trace a input m u d t) :
    Trace a input (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel exhaustion retains the partially executed batch or equality instruction. -/
def runFuel (a : F) (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a input s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input n t; (r.1, c + r.2)

/-- Exact trace fuel recovers the same result and ledger. -/
theorem Trace.runFuel_eq {a : F} {input : Input F} {n : ℕ}
    {s t : Configuration F} {c : Cost} (h : Trace a input n s c t) :
    runFuel a input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticResidualWitnessMachine
