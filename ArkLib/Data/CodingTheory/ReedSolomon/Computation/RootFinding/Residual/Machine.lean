/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualCoefficientMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticSystemMachine
public import ArkLib.Data.Matrix.QuadraticBackSubstitutionMachine
/-!
# Coordinate residual coefficient recovery

The driver retains actual system and back-substitution children. It materializes the four-field
system payload once, preserves every child charge and wrapper, and creates each zero seed cell
explicitly. The source seed ledger retains its scalar-result handle and list/root writes; two
additional writes allocate coordinate slots and a second literal completes the pair zero.
Successful return pays the extra option/root slot. No bulk conversion or zero-vector operation
runs. Input preparation, interpreter administration and bit time are excluded.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualCoefficientMachine

open Matrix
open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add cost_zero_add cost_add_zero)

abbrev Pair (F : Type*) := F × F
abbrev Input := QuadraticResidualSystemMachine.Input
abbrev Pivot (F : Type*) := ForwardEchelonMachine.Pivot (Pair F)
abbrev Row (F : Type*) := ForwardEchelonMachine.Row (Pair F)
abbrev wrapper := QuadraticPivotMachine.rowWrapper

/-- Retain source administrative work and its explicit literal charges. -/
def administrative (c : ResidualCoefficientMachine.Cost) : Cost :=
  ⟨{ control := c.matrix.row.control, data := c.matrix.row.data,
     output := c.matrix.row.output, constants := c.constants }, c.matrix.natural⟩

/-- Additional materialized slots beyond source bundled writes. -/
def allocation (n : ℕ) : Cost := ⟨{ data := n }, 0⟩

/-- Allocate two coordinate slots and supply the additional imaginary-zero literal. -/
def seedExtra : Cost := ⟨{ data := 2, constants := 1 }, 0⟩

inductive Configuration (F : Type*) where
  | start (points : List (Pair F))
  | system (payload : Input F) (state : QuadraticResidualSystemMachine.Configuration F)
  | initialize (pivots : List (Pivot F)) (rest : List (Row F)) (remaining : ℕ)
      (seed : List (Pair F))
  | backsub (state : QuadraticBackSubstitutionMachine.Configuration F)
  | emit (result : Option (List (Pair F)))
  | done (result : Option (List (Pair F)))

variable {F : Type*} [Field F] [DecidableEq F]

/-- One retained child instruction, explicit seed allocation, or result handoff. -/
def step (a : F) (input : Input F) (L : ℕ) :
    Configuration F → Option (Configuration F × Cost)
  | .start xs =>
      some (.system ⟨input.coefficients, input.terms, input.center, input.order⟩ (.start xs),
        administrative ResidualCoefficientMachine.entryCost + allocation 4)
  | .system payload s => match QuadraticResidualSystemMachine.step a payload L s with
      | some (t, c) => some (.system payload t, c + wrapper)
      | none => match s with
          | .done ps rs => some (.initialize ps rs L [],
              administrative ResidualCoefficientMachine.systemReturnCost)
          | .rejected => some (.emit none, administrative ResidualCoefficientMachine.returnCost)
          | _ => none
  | .initialize ps rs (n + 1) zs =>
      some (.initialize ps rs n ((0, 0) :: zs),
        administrative ResidualCoefficientMachine.initializeCost + seedExtra)
  | .initialize ps rs 0 zs => some (.backsub (.ready (.check rs ps zs)),
      administrative ResidualCoefficientMachine.initializeDoneCost)
  | .backsub s => match QuadraticBackSubstitutionMachine.step a s with
      | some (t, c) => some (.backsub t, c + wrapper)
      | none => match s with
          | .ready (.done xs) => some (.emit (some xs),
              administrative ResidualCoefficientMachine.returnCost + allocation 1)
          | .ready .inconsistent | .ready .rejected =>
              some (.emit none, administrative ResidualCoefficientMachine.returnCost)
          | _ => none
  | .emit out => some (.done out, administrative ResidualCoefficientMachine.emitCost)
  | .done _ => none

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

end ReedSolomon.HiddenDerivative.QuadraticResidualCoefficientMachine
