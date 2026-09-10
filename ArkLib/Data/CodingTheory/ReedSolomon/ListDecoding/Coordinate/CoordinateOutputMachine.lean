/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateAcceptanceRefinement
/-!
# Actual coordinate canonical output collection

Each record creates and pays for its five-field guard input once. The suspended acceptance
state retains this payload. Accepted base vectors are saved and reversed one list cell at a time.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticCanonicalOutputMachine

abbrev Record := HiddenDerivative.StageRootsMachine.Record

namespace Accept
export QuadraticCanonicalAcceptanceMachine (Configuration step)
end Accept

/-- The allocated five-field record retains original order and exact context roots. -/
def guardInput {F : Type*} (order : ℕ) (samples : List (F × F)) (record : Record (F × F)) :
    HiddenDerivative.QuadraticCanonicalGuardMachine.Input F :=
  ⟨record.coefficients, samples, order, record.center, record.context.separant⟩

/-- The current acceptance state and immutable unvisited/output lists are explicit. -/
inductive Configuration (F : Type*)  where
  | start (records : List (Record (F × F)))
  | scan (records : List (Record (F × F))) (saved : List (List F))
  | accept (record : Record (F × F))
      (records : List (Record (F × F))) (saved : List (List F))
      (payload : HiddenDerivative.QuadraticCanonicalGuardMachine.Input F)
      (inner : Accept.Configuration F)
  | save (coefficients : List F) (records : List (Record (F × F)))
      (saved : List (List F))
  | reverse (remaining output : List (List F))
  | emit (output : List (List F))
  | done (output : List (List F))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Only one actual callee instruction or bounded cursor/allocation operation is dispatched. -/
def step (a : F) (order : ℕ) (samples : List (F × F)) (w k A : ℕ)
    (rows : List (F × F)) : Configuration F → Option (Configuration F × ℕ)
  | .start rs => some (.scan rs [], 4)
  | .scan (r :: rs) out => some
      (.accept r rs out (guardInput order samples r) (.start r.context.previous), 17)
  | .scan [] out => some (.reverse out [], 3)
  | .accept r rs out payload s => match Accept.step a payload w k A rows s with
      | some (t, c) => some (.accept r rs out payload t, c + 3)
      | none => match s with
          | .done none => some (.scan rs out, 3)
          | .done (some cs) => some (.save cs rs out, 3)
          | _ => none
  | .save cs rs out => some (.scan rs (cs :: out), 4)
  | .reverse (cs :: rest) out => some (.reverse rest (cs :: out), 6)
  | .reverse [] out => some (.emit out, 3)
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- Actual executable edges with all scalar-total charges. -/
inductive Trace (a : F) (order : ℕ) (samples : List (F × F)) (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace a order samples w k A rows 0 s 0 s
  | cons {n s t u c d} (head : step a order samples w k A rows s = some (t, c))
      (tail : Trace a order samples w k A rows n t d u) :
      Trace a order samples w k A rows (n + 1) s (c + d) u

/-- Concatenation preserves both instruction counts and actual charges. -/
theorem Trace.trans {a : F} {order : ℕ} {samples : List (F × F)} {w k A n m : ℕ}
    {rows : List (F × F)} {s t u : Configuration F} {c d : ℕ}
    (h : Trace a order samples w k A rows n s c t) (h' : Trace a order samples w k A rows m t d u) :
    Trace a order samples w k A rows (n + m) s (c + d) u := by
  induction h with
  | nil => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Host fuel exposes actual suspended state and accumulated work. -/
def runFuel (a : F) (order : ℕ) (samples : List (F × F)) (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step a order samples w k A rows s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a order samples w k A rows n t; (r.1, c + r.2)

/-- Traces predict the exact interpreter endpoint and ledger. -/
theorem Trace.runFuel_eq {a : F} {order : ℕ} {samples : List (F × F)} {w k A n : ℕ}
    {rows : List (F × F)} {s t : Configuration F} {c : ℕ}
    (h : Trace a order samples w k A rows n s c t) :
    runFuel a order samples w k A rows n s = (t, c) := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.ListDecoding.QuadraticCanonicalOutputMachine
