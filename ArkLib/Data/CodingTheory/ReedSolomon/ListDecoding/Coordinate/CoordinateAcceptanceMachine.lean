/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.GuardRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateCandidateRefinement
/-!
# Actual coordinate canonical acceptance

The guard executes raw-coordinate arithmetic instructions, followed by the raw-coordinate
descent cursor and base-field candidate filter. Every child ledger and wrapper is retained.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticCanonicalAcceptanceMachine

namespace Guard
export HiddenDerivative.QuadraticCanonicalGuardMachine (Input Equation Configuration step)
end Guard

namespace Candidate
export CoordinateCandidateMachine (Configuration step)
end Candidate

/-- Suspended execution retains the exact child configuration and emitted base coefficients. -/
inductive Configuration (F : Type*)  where
  | start (previous : List (Guard.Equation F))
  | guard (inner : Guard.Configuration F)
  | candidate (inner : Candidate.Configuration F)
  | emit (result : Option (List F))
  | done (result : Option (List F))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Dispatch performs one child instruction or one bounded handoff, not an entire child run. -/
def step (a : F) (input : Guard.Input F) (w k A : ℕ)
    (rows : List (F × F)) : Configuration F → Option (Configuration F × ℕ)
  | .start ps => some (.guard (.start ps), 4)
  | .guard s => match Guard.step a input s with
      | some (t, c) => some (.guard t, c.total + 3)
      | none => match s with
          | .done false => some (.emit none, 3)
          | .done true => some (.candidate (.start input.coefficients), 4)
          | _ => none
  | .candidate s => match Candidate.step w k A rows s with
      | some (t, c) => some (.candidate t, c + 3)
      | none => match s with
          | .done out => some (.emit out, 3)
          | _ => none
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- Actual executable edges with all scalar-total charges. -/
inductive Trace (a : F) (input : Guard.Input F) (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace a input w k A rows 0 s 0 s
  | cons {n s t u c d} (head : step a input w k A rows s = some (t, c))
      (tail : Trace a input w k A rows n t d u) :
      Trace a input w k A rows (n + 1) s (c + d) u

/-- Concatenation preserves both instruction counts and actual charges. -/
theorem Trace.trans {a : F} {input : Guard.Input F} {w k A n m : ℕ}
    {rows : List (F × F)} {s t u : Configuration F} {c d : ℕ}
    (h : Trace a input w k A rows n s c t) (h' : Trace a input w k A rows m t d u) :
    Trace a input w k A rows (n + m) s (c + d) u := by
  induction h with
  | nil => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Host fuel exposes actual suspended state and accumulated work. -/
def runFuel (a : F) (input : Guard.Input F) (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step a input w k A rows s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input w k A rows n t; (r.1, c + r.2)

/-- Traces predict the exact interpreter endpoint and ledger. -/
theorem Trace.runFuel_eq {a : F} {input : Guard.Input F} {w k A n : ℕ}
    {rows : List (F × F)} {s t : Configuration F} {c : ℕ}
    (h : Trace a input w k A rows n s c t) :
    runFuel a input w k A rows n s = (t, c) := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.ListDecoding.QuadraticCanonicalAcceptanceMachine
