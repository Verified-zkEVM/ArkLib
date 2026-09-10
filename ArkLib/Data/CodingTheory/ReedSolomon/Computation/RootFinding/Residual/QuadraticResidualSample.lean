/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.QuadraticJetHornerMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSampleMachine
/-!
# Residual sampling by actual base-field programs

Inputs are already materialized coordinate coefficient/term lists, center and sample. Jet and
sparse evaluation are suspended concrete coordinate interpreters, each advanced one instruction
at a time. The point-addition input record is allocated at launch and retained until return.
A separate base arithmetic program forms center plus sample. Packing allocates the
value-list head and the two-coordinate zero accumulator. No whole-list conversion, polynomial
operation or callback executes. Each delegated instruction retains its ledger and an additional
outer wrapper. Input preparation, host fuel administration and bit costs remain outside scope.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualSample

open Polynomial MvPolynomial QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Input (F : Type*) := ResidualSampleMachine.Input (Pair F)

/-- Original local administrative accesses, without an abstract extension addition. -/
def administrative (c : ResidualSampleMachine.Cost) : Cost :=
  ⟨{ control := c.control, data := c.data, output := c.output }, c.natural⟩
/-- An outer dispatch plus two accesses to the suspended child state. -/
def wrapper : Cost := ⟨{ control := 1, data := 2 }, 0⟩
/-- Read arithmetic operands/parameter and write the three input registers. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩
/-- Consume the base program's materialized pair and retain it for list packing. -/
def pointReturn : Cost := ⟨{ control := 1, data := 3 }, 0⟩
/-- Explicit scalar accumulator zero: two coordinate slots and two literal writes. -/
def zeroPair : Cost := ⟨{ data := 2, constants := 2 }, 0⟩

/-- Allocate both slots of the new value-list head, beyond root/register handoff accesses. -/
def valueCell : Cost := ⟨{ data := 2 }, 0⟩

inductive Configuration (F : Type*) where
  | start
  | jet (state : QuadraticJetHornerMachine.Configuration F)
  | point (jets : List (Pair F))
  | adding (jets : List (Pair F)) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)
  | pack (jets : List (Pair F)) (point : Pair F)
  | scalar (values : List (Pair F)) (state : QuadraticEvaluationMachine.Configuration F)
  | done (value : Pair F)

variable {F : Type*} [Field F] [DecidableEq F]

/-- One actual child instruction or one explicitly charged local allocation/handoff. -/
def step (a : F) (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start => some (.jet (.ready (.initialize input.coefficients (input.order + 1) [])),
      administrative ResidualSampleMachine.entryCost)
  | .jet s => match QuadraticJetHornerMachine.step a input.sample s with
      | some (t, c) => some (.jet t, c + wrapper)
      | none => match s with
          | .ready (.done js) =>
              some (.point js, administrative ResidualSampleMachine.jetReturnCost)
          | _ => none
  | .point js => some (.adding js ⟨a, input.center, input.sample⟩ (.start .add),
      administrative ResidualSampleMachine.pointCost + launch)
  | .adding js payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.adding js payload t, delegated c)
      | none => match s with
          | .done (.pair p) => some (.pack js p, pointReturn)
          | _ => none
  | .pack js p => some (.scalar (p :: js) (.ready (.terms input.terms (0, 0))),
      administrative ResidualSampleMachine.packCost + zeroPair + valueCell)
  | .scalar vs s => match QuadraticEvaluationMachine.step a vs s with
      | some (t, c) => some (.scalar vs t, c + wrapper)
      | none => match s with
          | .ready (.done v) => some (.done v, administrative ResidualSampleMachine.returnCost)
          | _ => none
  | .done _ => none

/-- Exact executable edges accumulate the entire nested primitive ledger. -/
inductive Trace (a : F) (input : Input F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a input 0 s 0 s
  | cons {n s u t c d} (head : step a input s = some (u, c))
      (tail : Trace a input n u d t) : Trace a input (n + 1) s (c + d) t

/-- A single executed wrapper transition. -/
theorem single {a : F} {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step a input s = some (t, c)) : Trace a input 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Compose actual runs through their materialized handoff states. -/
theorem Trace.trans {a : F} {input : Input F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a input n s c u) (h' : Trace a input m u d t) :
    Trace a input (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Bounded execution exposes the actual suspended child on exhaustion. -/
def runFuel (a : F) (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a input s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input n t; (r.1, c + r.2)

/-- The certified trace is the same run and accumulated cost as the interpreter. -/
theorem Trace.runFuel_eq {a : F} {input : Input F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a input n s c t) : runFuel a input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticResidualSample
