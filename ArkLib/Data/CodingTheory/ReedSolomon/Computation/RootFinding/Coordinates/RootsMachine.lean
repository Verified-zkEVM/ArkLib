/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetRootsMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.RootMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.PreparationMachine
/-!
# Coordinate candidate enumeration and acceptance

The actual scalar-free axes and Cartesian-product machines enumerate supplied coordinates.
Every jet is prepared by the coordinate padding machine and tested by the full coordinate root
machine. Candidates are saved and reversed explicitly, preserving order and duplicates. Each
root payload is retained with charged allocation; all child instructions and output are charged.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticJetRootsMachine

open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Input (F : Type*) := JetRootsMachine.Input (Pair F)
abbrev allocation := QuadraticRegularRootMachine.allocation
abbrev wrapper := QuadraticRegularRootMachine.wrapper

/-- Preserve all scalar-free primitive categories. -/
def enumerationCost (c : List.CartesianProductMachine.Cost) : Cost :=
  ⟨{ control := c.control, data := c.data, output := c.output }, c.natural⟩
/-- Outer dispatch, registers, counters and emitted handles. -/
def charge (data natural output : ℕ) : Cost :=
  ⟨{ control := 1, data := data, output := output }, natural⟩

/-- All materialization, callee, collection and reversal cursors are exposed. -/
inductive Configuration (F : Type*) where
  | start (samples : List (Pair F))
  | count (cursor : List (Pair F)) (size : ℕ) (samples : List (Pair F))
  | bounds (remaining size : ℕ) (bounds : List ℕ) (samples : List (Pair F))
  | axes (samples : List (Pair F)) (state : List.PrefixAxesMachine.Configuration (Pair F))
  | product (samples : List (Pair F)) (state : List.CartesianProductMachine.Configuration (Pair F))
  | scan (jets results : List (List (Pair F))) (samples : List (Pair F))
  | prepare (jets results : List (List (Pair F))) (samples : List (Pair F))
      (state : QuadraticJetPreparationMachine.Configuration F)
  | root (jets results : List (List (Pair F))) (samples : List (Pair F))
      (payload : QuadraticRegularRootMachine.Input F)
      (state : QuadraticRegularRootMachine.Configuration F)
  | save (jets results : List (List (Pair F))) (samples candidate : List (Pair F))
  | reverse (remaining output : List (List (Pair F)))
  | emit (result : Option (List (List (Pair F))))
  | done (result : Option (List (List (Pair F))))

variable {F : Type*} [Field F] [DecidableEq F]

/-- No list-wide operation, polynomial conversion or full-run callback occurs in dispatch. -/
def step (a : F) (input : Input F) (D L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.count input.alphabet 0 xs, charge 4 1 0)
  | .count (_ :: as) q xs => some (.count as (q + 1) xs, charge 4 1 0)
  | .count [] q xs => some (.bounds (input.order + 1) q [] xs, charge 4 1 0)
  | .bounds (n + 1) q bs xs => some (.bounds n q (q :: bs) xs, charge 5 2 0)
  | .bounds 0 _ bs xs => some (.axes xs (.start bs), charge 3 1 0)
  | .axes xs s => match List.PrefixAxesMachine.step input.alphabet s with
      | some (t, c) => some (.axes xs t, enumerationCost c + wrapper)
      | none => match s with
          | .done (some as) => some (.product xs (.start as), charge 4 0 0)
          | .done none => some (.emit none, charge 2 0 0)
          | _ => none
  | .product xs s => match List.CartesianProductMachine.step s with
      | some (t, c) => some (.product xs t, enumerationCost c + wrapper)
      | none => match s with
          | .done jets => some (.scan jets [] xs, charge 4 0 0)
          | _ => none
  | .scan (jet :: jets) out xs => some (.prepare jets out xs (.start D jet), charge 6 0 0)
  | .scan [] out _ => some (.reverse out [], charge 2 0 0)
  | .prepare jets out xs s => match QuadraticJetPreparationMachine.step s with
      | some (t, c) => some (.prepare jets out xs t, c + wrapper)
      | none => match s with
          | .done (some cs) => some (.root jets out xs
              ⟨cs, input.terms, input.center, input.order⟩ (.start xs), charge 5 0 0 + allocation 4)
          | .done none => some (.emit none, charge 2 0 0)
          | _ => none
  | .root jets out xs payload s => match QuadraticRegularRootMachine.step a payload D L s with
      | some (t, c) => some (.root jets out xs payload t, c + wrapper)
      | none => match s with
          | .done (some candidate) => some (.save jets out xs candidate, charge 2 0 0)
          | .done none => some (.scan jets out xs, charge 2 0 0)
          | _ => none
  | .save jets out xs candidate => some (.scan jets (candidate :: out) xs, charge 5 0 0)
  | .reverse (a :: as) out => some (.reverse as (a :: out), charge 5 0 0)
  | .reverse [] out => some (.emit (some out), charge 2 0 0 + allocation 1)
  | .emit out => some (.done out, charge 2 0 1)
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

end ReedSolomon.HiddenDerivative.QuadraticJetRootsMachine
