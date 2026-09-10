/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticResidualSample
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualBatchMachine
/-!
# Coordinate residual batches with retained sample payloads

The point cursor, point/value pair allocation, list-cell save, reversal and final emission are
explicit. Entry constructs the five-field sample payload once and retains it in the suspended
call state. Every actual lowered sample instruction retains its ledger plus an outer wrapper.
Point and value coordinates are already materialized and shared; pair allocation writes two
handles, and the existing save/reverse charges cover new list cells. Duplicate points are kept.
No bulk map, zip, reversal or input conversion runs. This node excludes matrix/system/root
execution, input preparation, host fuel administration and bit costs.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualBatch

open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add cost_zero_add cost_add_zero)
open QuadraticResidualSample (administrative wrapper)

abbrev Pair (F : Type*) := F × F
abbrev Entry (F : Type*) := Pair F × Pair F
abbrev Input (F : Type*) := ResidualBatchMachine.Input (Pair F)

/-- Write each of the five retained sample-input fields once, in addition to entry reads. -/
def inputRecord : Cost := ⟨{ data := 5 }, 0⟩

inductive Configuration (F : Type*) where
  | start (points : List (Pair F))
  | scan (remaining : List (Pair F)) (reversed : List (Entry F))
  | enter (point : Pair F) (remaining : List (Pair F)) (reversed : List (Entry F))
  | call (point : Pair F) (remaining : List (Pair F)) (reversed : List (Entry F))
      (payload : QuadraticResidualSample.Input F) (state : QuadraticResidualSample.Configuration F)
  | pack (point value : Pair F) (remaining : List (Pair F)) (reversed : List (Entry F))
  | save (entry : Entry F) (remaining : List (Pair F)) (reversed : List (Entry F))
  | reverse (remaining result : List (Entry F))
  | done (result : List (Entry F))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Dispatch advances one sample instruction or performs one local allocation/handoff. -/
def step (a : F) (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start ps => some (.scan ps [], administrative ResidualBatchMachine.startCost)
  | .scan (u :: ps) rev => some (.enter u ps rev, administrative ResidualBatchMachine.takeCost)
  | .scan [] rev => some (.reverse rev [], administrative ResidualBatchMachine.beginReverseCost)
  | .enter u ps rev =>
      some (.call u ps rev (ResidualBatchMachine.sampleInput input u) .start,
        administrative ResidualBatchMachine.entryCost + inputRecord)
  | .call u ps rev payload s => match QuadraticResidualSample.step a payload s with
      | some (t, c) => some (.call u ps rev payload t, c + wrapper)
      | none => match s with
          | .done v => some (.pack u v ps rev, administrative ResidualBatchMachine.returnCost)
          | _ => none
  | .pack u v ps rev => some (.save (u, v) ps rev, administrative ResidualBatchMachine.pairCost)
  | .save p ps rev => some (.scan ps (p :: rev), administrative ResidualBatchMachine.saveCost)
  | .reverse (p :: ps) out =>
      some (.reverse ps (p :: out), administrative ResidualBatchMachine.reverseCost)
  | .reverse [] out => some (.done out, administrative ResidualBatchMachine.emitCost)
  | .done _ => none

/-- Trace edges are actual successors carrying their complete primitive ledgers. -/
inductive Trace (a : F) (input : Input F) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a input 0 s 0 s
  | cons {n s u t c d} (head : step a input s = some (u, c))
      (tail : Trace a input n u d t) : Trace a input (n + 1) s (c + d) t

/-- One executed allocation or handoff. -/
theorem single {a : F} {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step a input s = some (t, c)) : Trace a input 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Compose concrete sample runs and batch control phases. -/
theorem Trace.trans {a : F} {input : Input F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a input n s c u) (h' : Trace a input m u d t) :
    Trace a input (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel exposes suspended child configurations instead of invoking a whole sample run. -/
def runFuel (a : F) (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a input s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input n t; (r.1, c + r.2)

/-- Trace and interpreter agree on the same endpoint and accumulated charge. -/
theorem Trace.runFuel_eq {a : F} {input : Input F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a input n s c t) : runFuel a input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticResidualBatch
