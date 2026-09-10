/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterRootsMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.RootsMachine
/-!
# Coordinate root enumeration across centers

Each supplied center runs the actual coordinate all-jet machine with a retained input record.
Candidate records and their outer cells are allocated separately. Explicit reversal preserves
center and jet order, including duplicates. All payload and child instruction costs are retained.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticCenterRootsMachine

open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Input (F : Type*) := CenterRootsMachine.Input (Pair F)
abbrev Record (F : Type*) := CenterRootsMachine.Record (Pair F)
abbrev allocation := QuadraticJetRootsMachine.allocation
abbrev wrapper := QuadraticJetRootsMachine.wrapper
abbrev charge := QuadraticJetRootsMachine.charge

/-- The record allocation phase is separate from its outer-list cell allocation. -/
inductive Configuration (F : Type*) where
  | start (samples : List (Pair F))
  | scan (centers : List (Pair F)) (records : List (Record F)) (samples : List (Pair F))
  | jets (center : Pair F) (centers : List (Pair F)) (records : List (Record F))
      (samples : List (Pair F)) (payload : QuadraticJetRootsMachine.Input F)
      (state : QuadraticJetRootsMachine.Configuration F)
  | collect (center : Pair F) (candidates : List (List (Pair F)))
      (centers : List (Pair F)) (records : List (Record F)) (samples : List (Pair F))
  | save (record : Record F) (center : Pair F) (candidates : List (List (Pair F)))
      (centers : List (Pair F)) (records : List (Record F)) (samples : List (Pair F))
  | reverse (remaining output : List (Record F))
  | emit (records : Option (List (Record F)))
  | done (records : Option (List (Record F)))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Dispatch performs one all-jet step or one fixed allocation/control operation. -/
def step (parameter : F) (input : Input F) (D L : ℕ) :
    Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.scan input.alphabet [] xs, charge 4 0 0)
  | .scan (a :: as) out xs => some (.jets a as out xs
      ⟨input.alphabet, input.terms, a, input.order⟩ (.start xs), charge 6 0 0 + allocation 4)
  | .scan [] out _ => some (.reverse out [], charge 2 0 0)
  | .jets a as out xs payload s => match QuadraticJetRootsMachine.step parameter payload D L s with
      | some (t, c) => some (.jets a as out xs payload t, c + wrapper)
      | none => match s with
          | .done (some candidates) => some (.collect a candidates as out xs, charge 4 0 0)
          | .done none => some (.emit none, charge 2 0 0)
          | _ => none
  | .collect a (candidate :: candidates) as out xs =>
      some (.save (a, candidate) a candidates as out xs, charge 6 0 0)
  | .collect _ [] as out xs => some (.scan as out xs, charge 2 0 0)
  | .save record a candidates as out xs =>
      some (.collect a candidates as (record :: out) xs, charge 5 0 0)
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

end ReedSolomon.HiddenDerivative.QuadraticCenterRootsMachine
