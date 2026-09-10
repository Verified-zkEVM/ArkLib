/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Semantics
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualZeroMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterShiftMachine
/-!
# Closed acceptance and translation of one regular lift

The actual lift is checked by the actual residual-zero machine in its local coordinate. Only
accepted local candidates enter the actual change-of-center machine. All nested arithmetic,
constants, equality tests, center negation, wrappers and final output are retained in the cost.
Initial jet materialization, sample preparation, enumeration and scalar bit costs are separate.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.RegularRootMachine

open Polynomial Matrix

abbrev Input := RegularLiftMachine.Input
abbrev Cost := RegularLiftMachine.Cost
abbrev totalCost := RegularLiftMachine.totalCost
abbrev withCoefficients := @RegularLiftMachine.withCoefficients
abbrev wrapperCost := RegularLiftMachine.wrapperCost

/-- Preserve the complete zero-check ledger, including all sample emissions and comparisons. -/
def zeroCost (c : ResidualZeroMachine.Cost) : Cost :=
  ⟨⟨⟨c.machine.additions, c.machine.multiplications, c.machine.control, c.machine.data,
    c.machine.output⟩, 0, 0, c.equalities, c.machine.natural⟩, 0⟩
/-- Preserve translation arithmetic, its explicit center negation and preparation constants. -/
def shiftCost (c : CenterShiftMachine.Cost) : Cost :=
  ⟨⟨⟨c.machine.additions, c.machine.multiplications, c.machine.control, c.machine.data,
    c.machine.output⟩, 0, c.negations, 0, c.machine.natural⟩, c.constants⟩
/-- Read the materialized sample root and initialize the lift. -/
def startCost : Cost := ⟨⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Retain the local candidate and initialize its residual check on the shared samples. -/
def liftReturnCost : Cost := ⟨⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Branch on the checked Boolean and initialize translation from retained local coefficients. -/
def zeroReturnCost : Cost := ⟨⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Read a returned tag and retain the final payload. -/
def returnCost : Cost := ⟨⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Emit a tagged global coefficient-vector root. -/
def emitCost : Cost := ⟨⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩, 0⟩

/-- Callees share immutable input roots; the local vector persists until translation. -/
inductive Configuration (F : Type*) where
  | start (samples : List F)
  | lift (samples : List F) (state : RegularLiftMachine.Configuration F)
  | check (cs : List F) (state : ResidualZeroMachine.Configuration F)
  | shift (cs : List F) (state : CenterShiftMachine.Configuration F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent rules require actual successful checking before translation can begin. -/
inductive Step (input : Input F) (D L : ℕ) :
    Configuration F → Cost → Configuration F → Prop where
  | start {xs} : Step input D L (.start xs) startCost (.lift xs (.start xs))
  | lift {xs s t c} (h : RegularLiftMachine.Step input D L s c t) :
      Step input D L (.lift xs s) (c + wrapperCost 1) (.lift xs t)
  | liftReturn {xs cs} : Step input D L (.lift xs (.done (some cs))) liftReturnCost
      (.check cs (.start xs))
  | liftReject {xs} : Step input D L (.lift xs (.done none)) returnCost (.emit none)
  | check {cs s t c} (h : ResidualZeroMachine.Step (withCoefficients input cs) s c t) :
      Step input D L (.check cs s) (zeroCost c + wrapperCost 1) (.check cs t)
  | accepted {cs} : Step input D L (.check cs (.done true)) zeroReturnCost (.shift cs .start)
  | rejected {cs} : Step input D L (.check cs (.done false)) zeroReturnCost (.emit none)
  | shift {cs s t c} (h : CenterShiftMachine.Step ⟨cs, input.center, D⟩ s c t) :
      Step input D L (.shift cs s) (shiftCost c + wrapperCost 1) (.shift cs t)
  | shifted {cs out} : Step input D L (.shift cs (.done out)) returnCost (.emit out)
  | emit {out} : Step input D L (.emit out) emitCost (.done out)

/-- Dispatch delegates exactly one primitive transition of the active callee. -/
def step (input : Input F) (D L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.lift xs (.start xs), startCost)
  | .lift xs s => match RegularLiftMachine.step input D L s with
      | some (t, c) => some (.lift xs t, c + wrapperCost 1)
      | none => match s with
          | .done (some cs) => some (.check cs (.start xs), liftReturnCost)
          | .done none => some (.emit none, returnCost)
          | _ => none
  | .check cs s => match ResidualZeroMachine.step (withCoefficients input cs) s with
      | some (t, c) => some (.check cs t, zeroCost c + wrapperCost 1)
      | none => match s with
          | .done true => some (.shift cs .start, zeroReturnCost)
          | .done false => some (.emit none, zeroReturnCost)
          | _ => none
  | .shift cs s => match CenterShiftMachine.step ⟨cs, input.center, D⟩ s with
      | some (t, c) => some (.shift cs t, shiftCost c + wrapperCost 1)
      | none => match s with
          | .done out => some (.emit out, returnCost)
          | _ => none
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Each rule has its executable successor and charge. -/
theorem Step.step_eq {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step input D L s c t) : step input D L s = some (t, c) := by
  cases h with
  | lift h => simp [step, h.step_eq]
  | check h => simp [step, h.step_eq]
  | shift h => simp [step, h.step_eq]
  | _ => rfl

/-- Every interpreter transition belongs to the independent operational semantics. -/
theorem step_sound {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step input D L s = some (t, c)) : Step input D L s c t := by
  cases s with
  | lift xs s =>
      cases hs : RegularLiftMachine.step input D L s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.lift (RegularLiftMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i out
          cases out <;> cases h <;> constructor
  | check cs s =>
      cases hs : ResidualZeroMachine.step (withCoefficients input cs) s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.check (ResidualZeroMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i out
          cases out <;> cases h <;> constructor
  | shift cs s =>
      cases hs : CenterShiftMachine.step ⟨cs, input.center, D⟩ s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.shift (CenterShiftMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          cases h; constructor
  | done out => simp [step] at h
  | _ => cases h; constructor

/-- Every local and nested charge is accumulated along actual traces. -/
inductive Trace (input : Input F) (D L : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input D L 0 s 0 s
  | cons {n s u t c d} (head : Step input D L s c u) (tail : Trace input D L n u d t) :
      Trace input D L (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [ResidualCoefficientMachine.cost_add, PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add, Nat.add_assoc]

omit [DecidableEq F] in
/-- Trace concatenation preserves lengths and full costs. -/
theorem Trace.trans {input : Input F} {D L n m : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Trace input D L n s c t) (h' : Trace input D L m t d u) :
    Trace input D L (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- Fuel exhaustion returns the actual suspended pipeline configuration. -/
def runFuel (input : Input F) (D L : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input D L s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input D L n t; (result.1, c + result.2)

/-- The interpreter refines an actual trace prefix with identical charges. -/
theorem runFuel_refines (input : Input F) (D L fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input D L n s (runFuel input D L fuel s).2
      (runFuel input D L fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input D L s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Completed output and charges are stable under surplus host fuel. -/
theorem Trace.runFuel_done {input : Input F} {D L n : ℕ} {s : Configuration F} {c : Cost}
    {out : Option (List F)} (h : Trace input D L n s c (.done out)) (extra : ℕ) :
    runFuel input D L (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

omit [DecidableEq F] in
/-- Lift actual lift transitions while retaining every callee cost field. -/
theorem lift_lift (input : Input F) (D L : ℕ) (xs : List F)
    {n : ℕ} {s t : RegularLiftMachine.Configuration F} {c : Cost}
    (h : RegularLiftMachine.Trace input D L n s c t) :
    Trace input D L n (.lift xs s) (c + wrapperCost n) (.lift xs t) := by
  induction h with
  | nil s => simpa [wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (D := D) (L := L) (.lift xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.lift head) ih

omit [DecidableEq F] in
/-- Lift actual check transitions while retaining every callee cost field. -/
theorem lift_check (input : Input F) (D L : ℕ) (cs : List F)
    {n : ℕ} {s t : ResidualZeroMachine.Configuration F} {c : ResidualZeroMachine.Cost}
    (h : ResidualZeroMachine.Trace (withCoefficients input cs) n s c t) :
    Trace input D L n (.check cs s) (zeroCost c + wrapperCost n) (.check cs t) := by
  induction h with
  | nil s => simpa [wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
      zeroCost] using
      Trace.nil (input := input) (D := D) (L := L) (.check cs s)
  | @cons n s u t c d head tail ih =>
      have heq : (zeroCost c + wrapperCost 1) + (zeroCost d + wrapperCost n) =
          zeroCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
          zeroCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.check head) ih

omit [DecidableEq F] in
/-- Lift actual shift transitions while retaining every callee cost field. -/
theorem lift_shift (input : Input F) (D L : ℕ) (cs : List F)
    {n : ℕ} {s t : CenterShiftMachine.Configuration F} {c : CenterShiftMachine.Cost}
    (h : CenterShiftMachine.Trace ⟨cs, input.center, D⟩ n s c t) :
    Trace input D L n (.shift cs s) (shiftCost c + wrapperCost n) (.shift cs t) := by
  induction h with
  | nil s => simpa [wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
      shiftCost] using
      Trace.nil (input := input) (D := D) (L := L) (.shift cs s)
  | @cons n s u t c d head tail ih =>
      have heq : (shiftCost c + wrapperCost 1) + (shiftCost d + wrapperCost n) =
          shiftCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
          shiftCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.shift head) ih

end ReedSolomon.HiddenDerivative.RegularRootMachine
