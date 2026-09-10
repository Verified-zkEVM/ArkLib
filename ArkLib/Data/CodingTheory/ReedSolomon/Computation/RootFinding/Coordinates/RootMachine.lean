/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.RegularRootMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.LiftMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ZeroMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ShiftMachine
/-!
# Accepted coordinate regular candidate

The actual lift emits a local candidate. Only the actual residual-zero Boolean permits center
translation and final emission. Retained child inputs are constructed and charged at each launch;
every instruction keeps its full child ledger and outer wrapper. Failure tags propagate exactly.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticRegularRootMachine

open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Input := QuadraticRegularLiftMachine.Input
abbrev administrative := QuadraticRegularLiftMachine.administrative
abbrev allocation := QuadraticRegularLiftMachine.allocation
abbrev wrapper := QuadraticRegularLiftMachine.wrapper

inductive Configuration (F : Type*) where
  | start (samples : List (Pair F))
  | lift (samples : List (Pair F)) (payload : Input F)
      (state : QuadraticRegularLiftMachine.Configuration F)
  | check (payload : Input F) (state : QuadraticResidualZeroMachine.Configuration F)
  | shift (payload : QuadraticCenterShiftMachine.Input F)
      (state : QuadraticCenterShiftMachine.Configuration F)
  | emit (result : Option (List (Pair F)))
  | done (result : Option (List (Pair F)))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Each call retains its actual input and executes one child instruction at a time. -/
def step (a : F) (input : Input F) (D L : ℕ) :
    Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.lift xs
      ⟨input.coefficients, input.terms, input.center, input.order⟩ (.start xs),
      administrative RegularRootMachine.startCost + allocation 4)
  | .lift xs payload s => match QuadraticRegularLiftMachine.step a payload D L s with
      | some (t, c) => some (.lift xs payload t, c + wrapper)
      | none => match s with
          | .done (some cs) => some (.check
              ⟨cs, input.terms, input.center, input.order⟩ (.start xs),
              administrative RegularRootMachine.liftReturnCost + allocation 4)
          | .done none => some (.emit none, administrative RegularRootMachine.returnCost)
          | _ => none
  | .check payload s => match QuadraticResidualZeroMachine.step a payload s with
      | some (t, c) => some (.check payload t, c + wrapper)
      | none => match s with
          | .done true => some (.shift ⟨payload.coefficients, input.center, D⟩ .start,
              administrative RegularRootMachine.zeroReturnCost + allocation 3)
          | .done false => some (.emit none, administrative RegularRootMachine.zeroReturnCost)
          | _ => none
  | .shift payload s => match QuadraticCenterShiftMachine.step a payload s with
      | some (t, c) => some (.shift payload t, c + wrapper)
      | none => match s with
          | .done out => some (.emit out, administrative RegularRootMachine.returnCost)
          | _ => none
  | .emit out => some (.done out, administrative RegularRootMachine.emitCost)
  | .done _ => none

/-- Actual outer and nested instructions accumulate all their costs. -/
inductive Trace (a : F) (input : Input F) (D L : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a input D L 0 s 0 s
  | cons {n s u t c d} (head : step a input D L s = some (u, c))
      (tail : Trace a input D L n u d t) : Trace a input D L (n + 1) s (c + d) t

/-- Execute a single concrete edge. -/
theorem single {a : F} {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step a input D L s = some (t, c)) : Trace a input D L 1 s c t := by
  simpa using Trace.cons h (Trace.nil t)

/-- Compose the exact execution and ledger. -/
theorem Trace.trans {a : F} {input : Input F} {D L n m : ℕ}
    {s u t : Configuration F} {c d : Cost}
    (h : Trace a input D L n s c u) (h' : Trace a input D L m u d t) :
    Trace a input D L (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel exhaustion retains partial child execution without fabricated acceptance. -/
def runFuel (a : F) (input : Input F) (D L : ℕ) :
    ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a input D L s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input D L n t; (r.1, c + r.2)

/-- Exact trace fuel gives the same endpoint and charge. -/
theorem Trace.runFuel_eq {a : F} {input : Input F} {D L n : ℕ}
    {s t : Configuration F} {c : Cost} (h : Trace a input D L n s c t) :
    runFuel a input D L n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticRegularRootMachine
