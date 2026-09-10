/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CanonicalGuardBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ZeroMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.WitnessMachine
/-!
# Coordinate canonical-stage and center guard

Earlier equations run the actual coordinate residual-zero child. The separant runs the actual
ordered witness child, then the selected point is compared with the center by base arithmetic.
Every residual payload retains four roots and constructs its two zero coordinates explicitly.
Samples, candidate coefficients, equations and the outer input record arrive materialized.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticCanonicalGuardMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Equation (F : Type*) := CanonicalGuardMachine.Equation (Pair F)
abbrev Input (F : Type*) := CanonicalGuardMachine.Input (Pair F)

/-- Zero translation is a pair of explicit zero literals in a retained four-field payload. -/
def residualInput {F : Type*} [Zero F] (input : Input F) (terms : Equation F) :
    QuadraticResidualBatch.Input F := ⟨input.coefficients, terms, (0, 0), input.order⟩

def entryCost : Cost := ⟨{ control := 1, data := 3 }, 0⟩
/-- Source launch accesses, four retained fields, two zero slots, and two zero literals. -/
def residualLaunch : Cost := ⟨{ control := 1, data := 11, constants := 2 }, 0⟩
/-- Selected point/center accesses and the retained arithmetic argument record. -/
def compareLaunch : Cost := ⟨{ control := 1, data := 11 }, 0⟩
def returnCost : Cost := ⟨{ control := 1, data := 2 }, 0⟩
def emitCost : Cost := ⟨{ control := 1, data := 2, output := 1 }, 0⟩
def wrapper : Cost := ⟨{ control := 1, data := 2 }, 0⟩

inductive Configuration (F : Type*) where
  | start (previous : List (Equation F))
  | scan (previous : List (Equation F))
  | zero (payload : QuadraticResidualBatch.Input F) (remaining : List (Equation F))
      (state : QuadraticResidualZeroMachine.Configuration F)
  | witness (payload : QuadraticResidualBatch.Input F)
      (state : QuadraticResidualWitnessMachine.Configuration F)
  | compare (payload : ArithmeticMachine.Input F) (state : ArithmeticMachine.Configuration F)
  | emit (accepted : Bool)
  | done (accepted : Bool)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Only actual child results select branches; no global identity or equality predicate executes. -/
def step (a : F) (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start ps => some (.scan ps, entryCost)
  | .scan (q :: ps) =>
      some (.zero (residualInput input q) ps (.start input.samples), residualLaunch)
  | .scan [] =>
      some (.witness (residualInput input input.separant) (.start input.samples), residualLaunch)
  | .zero payload ps s => match QuadraticResidualZeroMachine.step a payload s with
      | some (t, c) => some (.zero payload ps t, c + wrapper)
      | none => match s with
          | .done true => some (.scan ps, returnCost)
          | .done false => some (.emit false, returnCost)
          | _ => none
  | .witness payload s => match QuadraticResidualWitnessMachine.step a payload s with
      | some (t, c) => some (.witness payload t, c + wrapper)
      | none => match s with
          | .done none => some (.emit false, returnCost)
          | .done (some u) => some (.compare ⟨a, u, input.center⟩ (.start .equal), compareLaunch)
          | _ => none
  | .compare payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.compare payload t, delegated c)
      | none => match s with
          | .done (.boolean b) => some (.emit b, returnCost)
          | _ => none
  | .emit b => some (.done b, emitCost)
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

end ReedSolomon.HiddenDerivative.QuadraticCanonicalGuardMachine
