/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.CentersMachine
public import ArkLib.Data.MvPolynomial.CoordinateChainMachine
/-!
# Coordinate stage-root generation

The actual coordinate chain emits ordered stages. Each active stage calls the coordinate center
loop with a retained input record. Contexts, pending records, outer cells and output reversal are
explicit. Invalid or missing stages and child failures retain the source failure tags. All child
instructions, initialization roots and input payloads are charged.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticStageRootsMachine

open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Term (F : Type*) := MvPolynomial.EvaluationMachine.Term (Pair F)
abbrev Stage (F : Type*) := MvPolynomial.SeparantChainMachine.Stage (Pair F)
abbrev Context (F : Type*) := StageRootsMachine.Context (Pair F)
abbrev Record (F : Type*) := StageRootsMachine.Record (Pair F)
abbrev Input (F : Type*) := StageRootsMachine.Input (Pair F)
abbrev charge := QuadraticCenterRootsMachine.charge
abbrev wrapper := QuadraticCenterRootsMachine.wrapper
abbrev allocation := QuadraticCenterRootsMachine.allocation

/-- Every child instruction and every context, prefix, record and output cell is explicit. -/
inductive Configuration (F : Type*) where
  | start (samples : List (Pair F))
  | chain (samples : List (Pair F)) (state : MvPolynomial.QuadraticChainMachine.Configuration F)
  | scan (stages : List (Stage F)) (previous : List (List (Term F)))
      (out : List (Record F)) (samples : List (Pair F))
  | select (stage : Stage F) (stages : List (Stage F))
      (previous nextPrevious : List (List (Term F))) (out : List (Record F))
      (samples : List (Pair F))
  | roots (context : Context F) (r : ℕ) (stages : List (Stage F))
      (previous : List (List (Term F))) (out : List (Record F)) (samples : List (Pair F))
      (payload : QuadraticCenterRootsMachine.Input F)
      (state : QuadraticCenterRootsMachine.Configuration F)
  | collect (context : Context F) (candidates : List (QuadraticCenterRootsMachine.Record F))
      (stages : List (Stage F)) (previous : List (List (Term F)))
      (out : List (Record F)) (samples : List (Pair F))
  | save (record : Record F) (context : Context F)
      (candidates : List (QuadraticCenterRootsMachine.Record F)) (stages : List (Stage F))
      (previous : List (List (Term F))) (out : List (Record F)) (samples : List (Pair F))
  | reverse (remaining output : List (Record F))
  | emit (out : Option (List (Record F)))
  | done (out : Option (List (Record F)))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Closed dispatch uses only actual child steps, record reads, and bounded allocations. -/
def step (a : F) (input : Input F) (D L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs =>
      some (.chain xs (MvPolynomial.QuadraticChainMachine.initial input.terms),
        charge 3 0 0 + allocation 4)
  | .chain xs s => match MvPolynomial.QuadraticChainMachine.step a s with
      | some (t, c) => some (.chain xs t, c + wrapper)
      | none => match s with
          | .done stages => some (.scan stages [] [] xs, charge 4 0 0)
          | _ => none
  | .scan (stage :: stages) pre out xs =>
      some (.select stage stages pre (stage.equation :: pre) out xs, charge 8 0 0)
  | .scan [] _ out _ => some (.reverse out [], charge 2 0 0)
  | .select stage stages pre nextPre out xs => match stage.selected with
      | none => some (.scan stages nextPre out xs, charge 3 0 0)
      | some (0, _) => some (.emit none, charge 3 1 0)
      | some (r + 1, _) => match stages with
          | [] => some (.emit none, charge 4 2 0)
          | next :: stages =>
              some (.roots ⟨stage, pre, next.equation⟩ r (next :: stages) nextPre out xs
                ⟨input.alphabet, stage.equation, r⟩ (.start xs), charge 12 2 0 + allocation 3)
  | .roots context r stages pre out xs payload s =>
      match QuadraticCenterRootsMachine.step a payload D L s with
      | some (t, c) => some (.roots context r stages pre out xs payload t, c + wrapper)
      | none => match s with
          | .done (some candidates) =>
              some (.collect context candidates stages pre out xs, charge 5 0 0)
          | .done none => some (.emit none, charge 2 0 0)
          | _ => none
  | .collect context ((a, cs) :: candidates) stages pre out xs =>
      some (.save ⟨context, a, cs⟩ context candidates stages pre out xs, charge 8 0 0)
  | .collect _ [] stages pre out xs => some (.scan stages pre out xs, charge 3 0 0)
  | .save record context candidates stages pre out xs =>
      some (.collect context candidates stages pre (record :: out) xs, charge 6 0 0)
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

end ReedSolomon.HiddenDerivative.QuadraticStageRootsMachine
