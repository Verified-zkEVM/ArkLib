/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.RegularRootSemantics
public import ArkLib.Data.List.PrefixAxesMachine
/-!
# Closed enumeration and execution of all initial jets at one center

A cursor counts the supplied alphabet, another allocates the repeated axis bounds, and actual
prefix-axis and Cartesian machines enumerate the tuples. Each tuple enters actual jet preparation
and actual accepted-root execution. Successes allocate output cells; explicit reversal preserves
tuple order. There is no callback, bulk conversion or implicit field enumeration in dispatch.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.JetRootsMachine

open Polynomial Matrix

abbrev Cost := RegularRootMachine.Cost
abbrev totalCost := RegularRootMachine.totalCost
abbrev wrapperCost := RegularRootMachine.wrapperCost

/-- Materialized alphabet and equation context, shared by every jet execution. -/
structure Input (F : Type*) where
  alphabet : List F
  terms : List (MvPolynomial.EvaluationMachine.Term F)
  center : F
  order : ℕ

/-- Supply a prepared coefficient-vector root to the accepted-root callee. -/
def rootInput {F : Type*} (input : Input F) (cs : List F) : RegularRootMachine.Input F :=
  ⟨cs, input.terms, input.center, input.order⟩
/-- Retain all scalar-free enumeration cost fields. -/
def enumerationCost (c : List.CartesianProductMachine.Cost) : Cost :=
  ⟨⟨⟨0, 0, c.control, c.data, c.output⟩, 0, 0, 0, c.natural⟩, 0⟩
/-- Retain every preparation charge, including each allocated scalar zero. -/
def preparationCost (c : JetPreparationMachine.Cost) : Cost :=
  RegularRootMachine.shiftCost (CenterShiftMachine.preparationCost c)
/-- Fixed administrative instruction charge with explicit natural and output operations. -/
def charge (data natural output : ℕ) : Cost := ⟨⟨⟨0, 0, 1, data, output⟩, 0, 0, 0, natural⟩, 0⟩

/-- All materialization, callee, collection and reversal cursors are exposed. -/
inductive Configuration (F : Type*) where
  | start (samples : List F)
  | count (cursor : List F) (size : ℕ) (samples : List F)
  | bounds (remaining size : ℕ) (bounds : List ℕ) (samples : List F)
  | axes (samples : List F) (state : List.PrefixAxesMachine.Configuration F)
  | product (samples : List F) (state : List.CartesianProductMachine.Configuration F)
  | scan (jets results : List (List F)) (samples : List F)
  | prepare (jets results : List (List F)) (samples : List F)
      (state : JetPreparationMachine.Configuration F)
  | root (jets results : List (List F)) (samples cs : List F)
      (state : RegularRootMachine.Configuration F)
  | save (jets results : List (List F)) (samples candidate : List F)
  | reverse (remaining output : List (List F))
  | emit (result : Option (List (List F)))
  | done (result : Option (List (List F)))
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent rules expose each actual allocation and each delegated transition. -/
inductive Step (input : Input F) (D L : ℕ) :
    Configuration F → Cost → Configuration F → Prop where
  | start {xs} : Step input D L (.start xs) (charge 4 1 0) (.count input.alphabet 0 xs)
  | count {a as q xs} : Step input D L (.count (a :: as) q xs) (charge 4 1 0)
      (.count as (q + 1) xs)
  | counted {q xs} : Step input D L (.count [] q xs) (charge 4 1 0)
      (.bounds (input.order + 1) q [] xs)
  | bound {n q bs xs} : Step input D L (.bounds (n + 1) q bs xs) (charge 5 2 0)
      (.bounds n q (q :: bs) xs)
  | bounded {q bs xs} : Step input D L (.bounds 0 q bs xs) (charge 3 1 0)
      (.axes xs (.start bs))
  | axes {xs s t c} (h : List.PrefixAxesMachine.Step input.alphabet s c t) :
      Step input D L (.axes xs s) (enumerationCost c + wrapperCost 1) (.axes xs t)
  | axesDone {xs as} : Step input D L (.axes xs (.done (some as))) (charge 4 0 0)
      (.product xs (.start as))
  | axesFailed {xs} : Step input D L (.axes xs (.done none)) (charge 2 0 0) (.emit none)
  | product {xs s t c} (h : List.CartesianProductMachine.Step s c t) :
      Step input D L (.product xs s) (enumerationCost c + wrapperCost 1) (.product xs t)
  | productDone {xs jets} : Step input D L (.product xs (.done jets)) (charge 4 0 0)
      (.scan jets [] xs)
  | next {jet jets out xs} : Step input D L (.scan (jet :: jets) out xs) (charge 6 0 0)
      (.prepare jets out xs (.start D jet))
  | prepare {jets out xs s t c} (h : JetPreparationMachine.Step s c t) :
      Step input D L (.prepare jets out xs s) (preparationCost c + wrapperCost 1)
        (.prepare jets out xs t)
  | prepared {jets out xs cs} : Step input D L (.prepare jets out xs (.done (some cs)))
      (charge 5 0 0) (.root jets out xs cs (.start xs))
  | prepareFailed {jets out xs} : Step input D L (.prepare jets out xs (.done none))
      (charge 2 0 0) (.emit none)
  | root {jets out xs cs s t c} (h : RegularRootMachine.Step (rootInput input cs) D L s c t) :
      Step input D L (.root jets out xs cs s) (c + wrapperCost 1) (.root jets out xs cs t)
  | success {jets out xs cs candidate} :
      Step input D L (.root jets out xs cs (.done (some candidate))) (charge 2 0 0)
        (.save jets out xs candidate)
  | skipped {jets out xs cs} : Step input D L (.root jets out xs cs (.done none)) (charge 2 0 0)
      (.scan jets out xs)
  | save {jets out xs candidate} : Step input D L (.save jets out xs candidate) (charge 5 0 0)
      (.scan jets (candidate :: out) xs)
  | scanned {out xs} : Step input D L (.scan [] out xs) (charge 2 0 0) (.reverse out [])
  | reverse {a as out} : Step input D L (.reverse (a :: as) out) (charge 5 0 0)
      (.reverse as (a :: out))
  | reversed {out} : Step input D L (.reverse [] out) (charge 2 0 0) (.emit (some out))
  | emit {out} : Step input D L (.emit out) (charge 2 0 1) (.done out)

/-- No list-wide operation, polynomial conversion or full-run callback occurs in dispatch. -/
def step (input : Input F) (D L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.count input.alphabet 0 xs, charge 4 1 0)
  | .count (_ :: as) q xs => some (.count as (q + 1) xs, charge 4 1 0)
  | .count [] q xs => some (.bounds (input.order + 1) q [] xs, charge 4 1 0)
  | .bounds (n + 1) q bs xs => some (.bounds n q (q :: bs) xs, charge 5 2 0)
  | .bounds 0 _ bs xs => some (.axes xs (.start bs), charge 3 1 0)
  | .axes xs s => match List.PrefixAxesMachine.step input.alphabet s with
      | some (t, c) => some (.axes xs t, enumerationCost c + wrapperCost 1)
      | none => match s with
          | .done (some as) => some (.product xs (.start as), charge 4 0 0)
          | .done none => some (.emit none, charge 2 0 0)
          | _ => none
  | .product xs s => match List.CartesianProductMachine.step s with
      | some (t, c) => some (.product xs t, enumerationCost c + wrapperCost 1)
      | none => match s with
          | .done jets => some (.scan jets [] xs, charge 4 0 0)
          | _ => none
  | .scan (jet :: jets) out xs => some (.prepare jets out xs (.start D jet), charge 6 0 0)
  | .scan [] out _ => some (.reverse out [], charge 2 0 0)
  | .prepare jets out xs s => match JetPreparationMachine.step s with
      | some (t, c) => some (.prepare jets out xs t, preparationCost c + wrapperCost 1)
      | none => match s with
          | .done (some cs) => some (.root jets out xs cs (.start xs), charge 5 0 0)
          | .done none => some (.emit none, charge 2 0 0)
          | _ => none
  | .root jets out xs cs s => match RegularRootMachine.step (rootInput input cs) D L s with
      | some (t, c) => some (.root jets out xs cs t, c + wrapperCost 1)
      | none => match s with
          | .done (some candidate) => some (.save jets out xs candidate, charge 2 0 0)
          | .done none => some (.scan jets out xs, charge 2 0 0)
          | _ => none
  | .save jets out xs candidate => some (.scan jets (candidate :: out) xs, charge 5 0 0)
  | .reverse (a :: as) out => some (.reverse as (a :: out), charge 5 0 0)
  | .reverse [] out => some (.emit (some out), charge 2 0 0)
  | .emit out => some (.done out, charge 2 0 1)
  | .done _ => none

/-- Operational rules agree with executable dispatch and all charges. -/
theorem Step.step_eq {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step input D L s c t) : step input D L s = some (t, c) := by
  cases h with
  | axes h => simp [step, h.step_eq]
  | product h => simp [step, h.step_eq]
  | prepare h => simp [step, h.step_eq]
  | root h => simp [step, h.step_eq]
  | _ => rfl

/-- Every actual dispatch branch has an independent rule. -/
theorem step_sound {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step input D L s = some (t, c)) : Step input D L s c t := by
  cases s with
  | axes xs s =>
      cases hs : List.PrefixAxesMachine.step input.alphabet s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.axes (List.PrefixAxesMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i result
          cases result <;> cases h <;> constructor
  | product xs s =>
      cases hs : List.CartesianProductMachine.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.product (List.CartesianProductMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          cases h; constructor
  | prepare jets out xs s =>
      cases hs : JetPreparationMachine.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.prepare (JetPreparationMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i result
          cases result <;> cases h <;> constructor
  | root jets out xs cs s =>
      cases hs : RegularRootMachine.step (rootInput input cs) D L s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.root (RegularRootMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i result
          cases result <;> cases h <;> constructor
  | count as q xs => cases as <;> cases h <;> constructor
  | bounds n q bs xs => cases n <;> cases h <;> constructor
  | scan jets out xs => cases jets <;> cases h <;> constructor
  | reverse as out => cases as <;> cases h <;> constructor
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
    {out : Option (List (List F))} (h : Trace input D L n s c (.done out)) (extra : ℕ) :
    runFuel input D L (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]


omit [DecidableEq F] in
/-- Lift actual axes transitions, preserving every nested charge. -/
theorem lift_axes (input : Input F) (D L : ℕ) (xs : List F)
    {n : ℕ} {s t : List.PrefixAxesMachine.Configuration F} {c : List.CartesianProductMachine.Cost}
    (h : List.PrefixAxesMachine.Trace input.alphabet n s c t) :
    Trace input D L n (.axes xs s) (enumerationCost c + wrapperCost n) (.axes xs t) := by
  induction h with
  | nil s => simpa [wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
      enumerationCost] using
      Trace.nil (input := input) (D := D) (L := L) (.axes xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (enumerationCost c + wrapperCost 1) + (enumerationCost d + wrapperCost n) =
          enumerationCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
          enumerationCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.axes head) ih

omit [DecidableEq F] in
/-- Lift actual product transitions, preserving every nested charge. -/
theorem lift_product (input : Input F) (D L : ℕ) (xs : List F)
    {n : ℕ} {s t : List.CartesianProductMachine.Configuration F}
    {c : List.CartesianProductMachine.Cost}
    (h : List.CartesianProductMachine.Trace n s c t) :
    Trace input D L n (.product xs s) (enumerationCost c + wrapperCost n) (.product xs t) := by
  induction h with
  | nil s => simpa [wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
      enumerationCost] using
      Trace.nil (input := input) (D := D) (L := L) (.product xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (enumerationCost c + wrapperCost 1) + (enumerationCost d + wrapperCost n) =
          enumerationCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
          enumerationCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.product head) ih

omit [DecidableEq F] in
/-- Lift actual prepare transitions, preserving every nested charge. -/
theorem lift_prepare (input : Input F) (D L : ℕ) (jets out : List (List F)) (xs : List F)
    {n : ℕ} {s t : JetPreparationMachine.Configuration F} {c : JetPreparationMachine.Cost}
    (h : JetPreparationMachine.Trace n s c t) :
    Trace input D L n (.prepare jets out xs s) (preparationCost c + wrapperCost n)
      (.prepare jets out xs t) := by
  induction h with
  | nil s => simpa [wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
      preparationCost, RegularRootMachine.shiftCost,
      CenterShiftMachine.preparationCost] using
      Trace.nil (input := input) (D := D) (L := L) (.prepare jets out xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (preparationCost c + wrapperCost 1) + (preparationCost d + wrapperCost n) =
          preparationCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
          preparationCost, RegularRootMachine.shiftCost,
          CenterShiftMachine.preparationCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.prepare head) ih

omit [DecidableEq F] in
/-- Lift actual root transitions, preserving every nested charge. -/
theorem lift_root (input : Input F) (D L : ℕ) (jets out : List (List F)) (xs cs : List F)
    {n : ℕ} {s t : RegularRootMachine.Configuration F} {c : Cost}
    (h : RegularRootMachine.Trace (rootInput input cs) D L n s c t) :
    Trace input D L n (.root jets out xs cs s) (c + wrapperCost n) (.root jets out xs cs t) := by
  induction h with
  | nil s => simpa [wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (D := D) (L := L) (.root jets out xs cs s)
  | @cons n s u t c d head tail ih =>
      have heq : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.root head) ih

end ReedSolomon.HiddenDerivative.JetRootsMachine
