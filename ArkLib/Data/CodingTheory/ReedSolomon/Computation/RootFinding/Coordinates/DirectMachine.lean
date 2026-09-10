/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectCoefficientMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.Machine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectArithmeticMachine
public import ArkLib.Data.Polynomial.QuadraticUpdateMachine
/-!
# Coordinate direct coefficient execution

Two actual residual recoveries retain their four-field inputs. Between them, an actual indexed
update uses a materialized one pair. Lookups traverse returned vectors explicitly, and the scalar
suffix uses the retained DirectArithmetic machine. Every child instruction retains its full
ledger plus a wrapper. Input records, one coordinates, option payload and final handoff writes
are charged. Input preparation, interpreter administration and bit time are excluded.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticDirectCoefficientMachine

open Polynomial
open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Input := QuadraticResidualCoefficientMachine.Input
abbrev administrative := QuadraticResidualCoefficientMachine.administrative
abbrev allocation := QuadraticResidualCoefficientMachine.allocation
abbrev oneExtra := QuadraticResidualCoefficientMachine.seedExtra
abbrev wrapper := Matrix.QuadraticPivotMachine.rowWrapper

/-- Retain the already materialized arithmetic result as this driver's terminal payload. -/
def returned : Cost := ⟨{ control := 1, data := 2 }, 0⟩

inductive Configuration (F : Type*) where
  | start (samples : List (Pair F))
  | recover (beta : Option (Pair F)) (samples : List (Pair F)) (payload : Input F)
      (state : QuadraticResidualCoefficientMachine.Configuration F)
  | lookup (beta : Option (Pair F)) (samples : List (Pair F)) (index : ℕ) (values : List (Pair F))
  | update (beta : Pair F) (samples : List (Pair F)) (gamma : Pair F)
      (state : QuadraticUpdateMachine.Configuration F)
  | arithmetic (state : DirectArithmeticMachine.Configuration F)
  | done (result : Option (Pair F))

variable {F : Type*} [Field F] [DecidableEq F]

/-- One retained callee instruction or charged input/lookup/result handoff. -/
def step (a : F) (input : Input F) (w L k : ℕ) :
    Configuration F → Option (Configuration F × Cost)
  | .start xs =>
      some (.recover none xs (DirectCoefficientMachine.withCoefficients input input.coefficients)
        (.start xs), administrative DirectCoefficientMachine.startCost + allocation 4)
  | .recover b xs payload s => match QuadraticResidualCoefficientMachine.step a payload L s with
      | some (t, c) => some (.recover b xs payload t, c + wrapper)
      | none => match s with
          | .done (some out) => some (.lookup b xs k out,
              administrative DirectCoefficientMachine.lookupCost)
          | .done none => some (.arithmetic (.ready (.emit none)),
              administrative DirectCoefficientMachine.rejectCost)
          | _ => none
  | .lookup _ _ _ [] => some (.arithmetic (.ready (.emit none)),
      administrative DirectCoefficientMachine.rejectCost)
  | .lookup b xs (j + 1) (_ :: tail) =>
      some (.lookup b xs j tail, administrative DirectCoefficientMachine.advanceCost)
  | .lookup none xs 0 (b :: _) =>
      some (.update b xs (1, 0) (.ready
        (.start input.coefficients (w - 1 - (k + input.order)))),
        administrative DirectCoefficientMachine.selectZeroCost + oneExtra)
  | .lookup (some b) _ 0 (one :: _) => some (.arithmetic (.ready (.negate b one)),
      administrative DirectCoefficientMachine.selectOneCost)
  | .update b xs gamma s => match QuadraticUpdateMachine.step a gamma s with
      | some (t, c) => some (.update b xs gamma t, c + wrapper)
      | none => match s with
          | .ready (.done (some cs)) => some
              (.recover (some b) xs (DirectCoefficientMachine.withCoefficients input cs)
                (.start xs),
                administrative DirectCoefficientMachine.updateReturnCost + allocation 5)
          | .ready (.done none) => some (.arithmetic (.ready (.emit none)),
              administrative DirectCoefficientMachine.rejectCost)
          | _ => none
  | .arithmetic s => match DirectArithmeticMachine.step a s with
      | some (t, c) => some (.arithmetic t, c + wrapper)
      | none => match s with
          | .ready (.done out) => some (.done out, returned)
          | _ => none
  | .done _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) (input : Input F) (w L k : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a input w L k 0 s 0 s
  | cons {n s u t c d} (head : step a input w L k s = some (u, c))
      (tail : Trace a input w L k n u d t) :
      Trace a input w L k (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {input : Input F} {w L k : ℕ} {s t : Configuration F} {c : Cost}
    (h : step a input w L k s = some (t, c)) : Trace a input w L k 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {input : Input F} {w L k n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a input w L k n s c u)
    (h' : Trace a input w L k m u d t) :
    Trace a input w L k (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) (input : Input F) (w L k : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a input w L k s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input w L k n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {input : Input F} {w L k n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a input w L k n s c t) : runFuel a input w L k n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticDirectCoefficientMachine
