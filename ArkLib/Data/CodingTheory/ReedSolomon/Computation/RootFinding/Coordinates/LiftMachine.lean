/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Machine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.DirectMachine
public import ArkLib.Data.Polynomial.QuadraticUpdateMachine
/-!
# Coordinate regular lifting loop

Each stage constructs and retains the four-field direct input, executes that actual child, and
passes its materialized gamma to the actual indexed update. Counters and shared sample roots
persist across stages. Every child instruction retains its ledger plus outer dispatch/root work;
input construction and successful option allocation are explicit. The initial vector and samples
are supplied. Full residual acceptance, input preparation, interpreter and bit time are excluded.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticRegularLiftMachine

open Polynomial
open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Input := QuadraticDirectCoefficientMachine.Input
abbrev administrative := QuadraticResidualCoefficientMachine.administrative
abbrev allocation := QuadraticResidualCoefficientMachine.allocation
abbrev wrapper := Matrix.QuadraticPivotMachine.rowWrapper

inductive Configuration (F : Type*) where
  | start (samples : List (Pair F))
  | loop (next remaining : ℕ) (coefficients samples : List (Pair F))
  | direct (next remaining : ℕ) (samples : List (Pair F)) (payload : Input F)
      (state : QuadraticDirectCoefficientMachine.Configuration F)
  | update (next remaining : ℕ) (samples : List (Pair F)) (gamma : Pair F)
      (state : QuadraticUpdateMachine.Configuration F)
  | emit (result : Option (List (Pair F)))
  | done (result : Option (List (Pair F)))

variable {F : Type*} [Field F] [DecidableEq F]

/-- One retained direct/update instruction or fixed counter/input/result transition. -/
def step (a : F) (input : Input F) (D L : ℕ) :
    Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.loop 1 (D - input.order) input.coefficients xs,
      administrative RegularLiftMachine.startCost)
  | .loop _ 0 cs _ => some (.emit (some cs),
      administrative RegularLiftMachine.finishCost + allocation 1)
  | .loop k (n + 1) cs xs =>
      some (.direct k n xs (DirectCoefficientMachine.withCoefficients input cs) (.start xs),
        administrative RegularLiftMachine.stageCost + allocation 4)
  | .direct k n xs payload s =>
      match QuadraticDirectCoefficientMachine.step a payload (D + 1) L k s with
      | some (t, c) => some (.direct k n xs payload t, c + wrapper)
      | none => match s with
          | .done (some gamma) => some (.update k n xs gamma
              (.ready (.start payload.coefficients (D - (k + input.order)))),
                administrative RegularLiftMachine.directReturnCost)
          | .done none => some (.emit none, administrative RegularLiftMachine.rejectCost)
          | _ => none
  | .update k n xs gamma s => match QuadraticUpdateMachine.step a gamma s with
      | some (t, c) => some (.update k n xs gamma t, c + wrapper)
      | none => match s with
          | .ready (.done (some cs)) => some (.loop (k + 1) n cs xs,
              administrative RegularLiftMachine.updateReturnCost)
          | .ready (.done none) => some (.emit none, administrative RegularLiftMachine.rejectCost)
          | _ => none
  | .emit out => some (.done out, administrative RegularLiftMachine.emitCost)
  | .done _ => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) (input : Input F) (D L : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a input D L 0 s 0 s
  | cons {n s u t c d} (head : step a input D L s = some (u, c))
      (tail : Trace a input D L n u d t) :
      Trace a input D L (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step a input D L s = some (t, c)) : Trace a input D L 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {input : Input F} {D L n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a input D L n s c u) (h' : Trace a input D L m u d t) :
    Trace a input D L (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) (input : Input F) (D L : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a input D L s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input D L n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {input : Input F} {D L n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a input D L n s c t) : runFuel a input D L n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticRegularLiftMachine
