/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.CoefficientUpdateMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationMachine

/-!
# Coordinate indexed coefficient updates

The cursor copies and restores the prefix one cell at a time, sharing the untouched suffix.
The selected addition runs actual base instructions with a retained operand record, then saves
its emitted pair separately. Gamma is supplied materialized by the caller; input preparation,
gamma construction, interpreter administration and bit time are excluded.
-/

@[expose] public section

namespace Polynomial.QuadraticUpdateMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc total_add
  cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F

/-- Retain natural, dispatch, root and output work while lowering scalar arithmetic. -/
def administrative (c : CoefficientUpdateMachine.Cost) : Cost :=
  ⟨{ control := c.control, data := c.data, output := c.output }, c.natural⟩
/-- Construct the retained parameter and operand record. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩
/-- Retain the emitted pair for its separate save step. -/
def returned : Cost := ⟨{ control := 1, data := 3 }, 0⟩
/-- Supplement bundled source writes with the additional result or option root. -/
def allocation : Cost := ⟨{ data := 1 }, 0⟩

inductive Configuration (F : Type*) where
  | ready (state : CoefficientUpdateMachine.Configuration (Pair F))
  | call (tail reversed : List (Pair F)) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)
  | save (value : Pair F) (tail reversed : List (Pair F))

variable {F : Type*} [Field F] [DecidableEq F]

/-- One explicit cursor/save transition or one retained base addition instruction. -/
def step (a : F) (gamma : Pair F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.start cs j) =>
      some (.ready (.scan j cs []), administrative CoefficientUpdateMachine.startCost)
  | .ready (.scan _ [] _) =>
      some (.ready (.emit none), administrative CoefficientUpdateMachine.rejectCost)
  | .ready (.scan 0 (c :: cs) rev) =>
      some (.ready (.add c cs rev), administrative CoefficientUpdateMachine.selectCost)
  | .ready (.scan (j + 1) (c :: cs) rev) =>
      some (.ready (.scan j cs (c :: rev)), administrative CoefficientUpdateMachine.advanceCost)
  | .ready (.add c cs rev) => some (.call cs rev ⟨a, c, gamma⟩ (.start .add), launch)
  | .ready (.restore (c :: rev) out) =>
      some (.ready (.restore rev (c :: out)), administrative CoefficientUpdateMachine.restoreCost)
  | .ready (.restore [] out) => some (.ready (.emit (some out)),
      administrative CoefficientUpdateMachine.finishCost + allocation)
  | .ready (.emit out) =>
      some (.ready (.done out), administrative CoefficientUpdateMachine.emitCost)
  | .ready (.done _) => none
  | .call cs rev payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.call cs rev payload t, delegated c)
      | none => match s with
          | .done (.pair v) => some (.save v cs rev, returned)
          | _ => none
  | .save v cs rev => some (.ready (.restore rev (v :: cs)),
      administrative CoefficientUpdateMachine.addCost + allocation)

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) (gamma : Pair F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a gamma 0 s 0 s
  | cons {n s u t c d} (head : step a gamma s = some (u, c)) (tail : Trace a gamma n u d t) :
      Trace a gamma (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {gamma : Pair F} {s t : Configuration F} {c : Cost}
    (h : step a gamma s = some (t, c)) : Trace a gamma 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {gamma : Pair F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a gamma n s c u) (h' : Trace a gamma m u d t) :
    Trace a gamma (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) (gamma : Pair F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a gamma s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a gamma n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {gamma : Pair F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a gamma n s c t) : runFuel a gamma n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Polynomial.QuadraticUpdateMachine
