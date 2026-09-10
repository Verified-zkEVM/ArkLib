/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSystemMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticBatch
public import ArkLib.Data.Matrix.QuadraticVandermondeMachine
public import ArkLib.Data.Matrix.QuadraticForwardEchelonMachine
/-!
# Coordinate residual systems with retained children

The driver advances actual residual-batch, Vandermonde and forward-echelon instructions. Start
materializes the four-field batch input once; every sampling step uses that retained payload.
Returned sample and row roots pass directly to the next child without conversion. All child
charges and outputs remain counted, with an outer dispatch and two root accesses per instruction.
Input preparation, coefficient solving, interpreter administration and bit time are excluded.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualSystemMachine

open Matrix
open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Input := QuadraticResidualBatch.Input
abbrev Pivot (F : Type*) := ForwardEchelonMachine.Pivot (Pair F)
abbrev Row (F : Type*) := ForwardEchelonMachine.Row (Pair F)
abbrev administrative := QuadraticPivotMachine.administrative
abbrev wrapper := QuadraticPivotMachine.rowWrapper

/-- Write the four immutable batch-input fields in addition to the source handoff. -/
def inputRecord : Cost := ⟨{ data := 4 }, 0⟩

inductive Configuration (F : Type*) where
  | start (points : List (Pair F))
  | sample (payload : Input F) (state : QuadraticResidualBatch.Configuration F)
  | matrix (state : QuadraticVandermondeMachine.Configuration F)
  | echelon (state : QuadraticForwardEchelonMachine.Configuration F)
  | done (pivots : List (Pivot F)) (rest : List (Row F))
  | rejected

variable {F : Type*} [Field F] [DecidableEq F]

/-- One actual retained child instruction or direct materialized-root handoff. -/
def step (a : F) (input : Input F) (L : ℕ) :
    Configuration F → Option (Configuration F × Cost)
  | .start ps =>
      some (.sample ⟨input.coefficients, input.terms, input.center, input.order⟩ (.start ps),
        administrative ResidualSystemMachine.startCost + inputRecord)
  | .sample payload s => match QuadraticResidualBatch.step a payload s with
      | some (t, c) => some (.sample payload t, c + wrapper)
      | none => match s with
          | .done ps => some (.matrix (.ready (.start ps)),
              administrative ResidualSystemMachine.sampleReturnCost)
          | _ => none
  | .matrix s => match QuadraticVandermondeMachine.step a L s with
      | some (t, c) => some (.matrix t, c + wrapper)
      | none => match s with
          | .ready (.done rs) => some (.echelon (.ready (.loop 0 L rs [])),
              administrative ResidualSystemMachine.matrixReturnCost)
          | _ => none
  | .echelon s => match QuadraticForwardEchelonMachine.step a s with
      | some (t, c) => some (.echelon t, c + wrapper)
      | none => match s with
          | .ready (.done ps rs) => some (.done ps rs,
              administrative ResidualSystemMachine.returnCost)
          | .ready .rejected => some (.rejected, administrative ResidualSystemMachine.returnCost)
          | _ => none
  | .done _ _ | .rejected => none

/-- Concrete executable edges accumulate their full ledger. -/
inductive Trace (a : F) (input : Input F) (L : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a input L 0 s 0 s
  | cons {n s u t c d} (head : step a input L s = some (u, c)) (tail : Trace a input L n u d t) :
      Trace a input L (n + 1) s (c + d) t

/-- A single executed transition. -/
theorem single {a : F} {input : Input F} {L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step a input L s = some (t, c)) : Trace a input L 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Concatenate concrete lowered traces. -/
theorem Trace.trans {a : F} {input : Input F} {L n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a input L n s c u) (h' : Trace a input L m u d t) :
    Trace a input L (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances individual base instructions and preserves suspended call state. -/
def runFuel (a : F) (input : Input F) (L : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a input L s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input L n t; (r.1, c + r.2)

/-- The exact trace is the same run and accumulated cost. -/
theorem Trace.runFuel_eq {a : F} {input : Input F} {L n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a input L n s c t) : runFuel a input L n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.QuadraticResidualSystemMachine
