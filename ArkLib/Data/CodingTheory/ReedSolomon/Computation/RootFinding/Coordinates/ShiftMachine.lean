/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterShiftMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.PreparationMachine
public import ArkLib.Data.Polynomial.QuadraticJetHornerMachine
/-!
# Coordinate change of center

An actual base negation program produces the retained Horner point. The coordinate jet evaluator
then executes at that point, and coordinate preparation reverses its full jet. Payload setup,
every delegated instruction, option handling and final emission are charged. Inputs are supplied
as materialized coefficient, center and degree registers; no polynomial translation executes.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticCenterShiftMachine

open Polynomial QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Input (F : Type*) := CenterShiftMachine.Input (Pair F)

/-- Preserve source administrative categories while executing negation in the base program. -/
def administrative (c : CenterShiftMachine.Cost) : Cost :=
  ⟨{ control := c.machine.control, data := c.machine.data, output := c.machine.output },
    c.machine.natural⟩
/-- Charge each delegated instruction's outer dispatch and state-root accesses. -/
def wrapper : Cost := ⟨{ control := 1, data := 2 }, 0⟩
/-- Parameter, operand and shared unused operand slots are explicitly retained. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩

inductive Configuration (F : Type*) where
  | start
  | negate (payload : ArithmeticMachine.Input F) (state : ArithmeticMachine.Configuration F)
  | jet (point : Pair F) (state : QuadraticJetHornerMachine.Configuration F)
  | prepare (state : QuadraticJetPreparationMachine.Configuration F)
  | done (result : Option (List (Pair F)))

variable {F : Type*} [Field F] [DecidableEq F]

/-- One explicit base, Horner or preparation instruction, retaining the emitted point. -/
def step (a : F) (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start => some (.negate ⟨a, input.center, input.center⟩ (.start .neg), launch)
  | .negate payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.negate payload t, delegated c)
      | none => match s with
          | .done (.pair x) => some
              (.jet x (.ready (.initialize input.coefficients (input.degree + 1) [])),
                administrative CenterShiftMachine.entryCost)
          | _ => none
  | .jet x s => match QuadraticJetHornerMachine.step a x s with
      | some (t, c) => some (.jet x t, c + wrapper)
      | none => match s with
          | .ready (.done js) => some (.prepare (.start input.degree js),
              administrative CenterShiftMachine.handoffCost)
          | _ => none
  | .prepare s => match QuadraticJetPreparationMachine.step s with
      | some (t, c) => some (.prepare t, c + wrapper)
      | none => match s with
          | .done out => some (.done out, administrative CenterShiftMachine.returnCost)
          | _ => none
  | .done _ => none

/-- Concrete instructions and their complete nested ledger. -/
inductive Trace (a : F) (input : Input F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a input 0 s 0 s
  | cons {n s u t c d} (head : step a input s = some (u, c))
      (tail : Trace a input n u d t) : Trace a input (n + 1) s (c + d) t

/-- Execute a single edge. -/
theorem single {a : F} {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step a input s = some (t, c)) : Trace a input 1 s c t := by
  simpa using Trace.cons h (Trace.nil t)

/-- Concatenation preserves every child charge. -/
theorem Trace.trans {a : F} {input : Input F} {n m : ℕ}
    {s u t : Configuration F} {c d : Cost}
    (h : Trace a input n s c u) (h' : Trace a input m u d t) :
    Trace a input (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel exhaustion exposes retained child state instead of fabricating output. -/
def runFuel (a : F) (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a input s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input n t; (r.1, c + r.2)

/-- Exact trace fuel recovers the same endpoint and charge. -/
theorem Trace.runFuel_eq {a : F} {input : Input F} {n : ℕ}
    {s t : Configuration F} {c : Cost} (h : Trace a input n s c t) :
    runFuel a input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticCenterShiftMachine
