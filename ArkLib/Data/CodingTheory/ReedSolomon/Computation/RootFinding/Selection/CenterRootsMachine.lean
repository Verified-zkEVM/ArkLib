/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetRootsSemantics
/-!
# Closed root enumeration across all supplied centers

The shared alphabet is scanned as the center list. Each center runs the actual all-jet machine.
Successful global vectors are paired with their center and stored by separate pair/cell allocation
transitions. An explicit reversal preserves center and jet order. Duplicates across centers remain
for a subsequent canonical guard; field/sample preparation and outer stage loops are separate.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CenterRootsMachine

open Polynomial Matrix

abbrev Cost := JetRootsMachine.Cost
abbrev totalCost := JetRootsMachine.totalCost
abbrev wrapperCost := JetRootsMachine.wrapperCost
abbrev charge := JetRootsMachine.charge
abbrev Record (F : Type*) := F × List F

/-- Supplied alphabet and equation roots shared by every center execution. -/
structure Input (F : Type*) where
  alphabet : List F
  terms : List (MvPolynomial.EvaluationMachine.Term F)
  order : ℕ

/-- Retain the actual center in the all-jet callee's immutable input registers. -/
def centerInput {F : Type*} (input : Input F) (center : F) : JetRootsMachine.Input F :=
  ⟨input.alphabet, input.terms, center, input.order⟩

/-- The record allocation phase is separate from its outer-list cell allocation. -/
inductive Configuration (F : Type*) where
  | start (samples : List F)
  | scan (centers : List F) (records : List (Record F)) (samples : List F)
  | jets (center : F) (centers : List F) (records : List (Record F)) (samples : List F)
      (state : JetRootsMachine.Configuration F)
  | collect (center : F) (candidates : List (List F)) (centers : List F)
      (records : List (Record F)) (samples : List F)
  | save (record : Record F) (center : F) (candidates : List (List F)) (centers : List F)
      (records : List (Record F)) (samples : List F)
  | reverse (remaining output : List (Record F))
  | emit (records : Option (List (Record F)))
  | done (records : Option (List (Record F)))
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Every all-jet transition and every pair/cell allocation has an independent rule. -/
inductive Step (input : Input F) (D L : ℕ) :
    Configuration F → Cost → Configuration F → Prop where
  | start {xs} : Step input D L (.start xs) (charge 4 0 0) (.scan input.alphabet [] xs)
  | next {a as out xs} : Step input D L (.scan (a :: as) out xs) (charge 6 0 0)
      (.jets a as out xs (.start xs))
  | jets {a as out xs s t c} (h : JetRootsMachine.Step (centerInput input a) D L s c t) :
      Step input D L (.jets a as out xs s) (c + wrapperCost 1) (.jets a as out xs t)
  | returned {a as out xs candidates} :
      Step input D L (.jets a as out xs (.done (some candidates))) (charge 4 0 0)
        (.collect a candidates as out xs)
  | failed {a as out xs} : Step input D L (.jets a as out xs (.done none)) (charge 2 0 0)
      (.emit none)
  | pair {a candidate candidates as out xs} :
      Step input D L (.collect a (candidate :: candidates) as out xs) (charge 6 0 0)
        (.save (a, candidate) a candidates as out xs)
  | save {record a candidates as out xs} :
      Step input D L (.save record a candidates as out xs) (charge 5 0 0)
        (.collect a candidates as (record :: out) xs)
  | collected {a as out xs} : Step input D L (.collect a [] as out xs) (charge 2 0 0)
      (.scan as out xs)
  | scanned {out xs} : Step input D L (.scan [] out xs) (charge 2 0 0) (.reverse out [])
  | reverse {a as out} : Step input D L (.reverse (a :: as) out) (charge 5 0 0)
      (.reverse as (a :: out))
  | reversed {out} : Step input D L (.reverse [] out) (charge 2 0 0) (.emit (some out))
  | emit {out} : Step input D L (.emit out) (charge 2 0 1) (.done out)

/-- Dispatch performs one all-jet step or one fixed allocation/control operation. -/
def step (input : Input F) (D L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.scan input.alphabet [] xs, charge 4 0 0)
  | .scan (a :: as) out xs => some (.jets a as out xs (.start xs), charge 6 0 0)
  | .scan [] out _ => some (.reverse out [], charge 2 0 0)
  | .jets a as out xs s => match JetRootsMachine.step (centerInput input a) D L s with
      | some (t, c) => some (.jets a as out xs t, c + wrapperCost 1)
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
  | .reverse [] out => some (.emit (some out), charge 2 0 0)
  | .emit out => some (.done out, charge 2 0 1)
  | .done _ => none

/-- Independent rules agree with the actual successor and complete charge. -/
theorem Step.step_eq {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step input D L s c t) : step input D L s = some (t, c) := by
  cases h with
  | jets h => simp [step, h.step_eq]
  | _ => rfl

/-- Every dispatch branch is covered by the independent rules. -/
theorem step_sound {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step input D L s = some (t, c)) : Step input D L s c t := by
  cases s with
  | jets a as out xs s =>
      cases hs : JetRootsMachine.step (centerInput input a) D L s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.jets (JetRootsMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i result
          cases result <;> cases h <;> constructor
  | scan as out xs => cases as <;> cases h <;> constructor
  | collect a candidates as out xs => cases candidates <;> cases h <;> constructor
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
    {out : Option (List (Record F))} (h : Trace input D L n s c (.done out)) (extra : ℕ) :
    runFuel input D L (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]


omit [DecidableEq F] in
/-- Every inner all-jet transition retains its nested costs and one caller dispatch. -/
theorem lift_jets (input : Input F) (D L : ℕ) (a : F) (as : List F)
    (out : List (Record F)) (xs : List F) {n : ℕ}
    {s t : JetRootsMachine.Configuration F} {c : Cost}
    (h : JetRootsMachine.Trace (centerInput input a) D L n s c t) :
    Trace input D L n (.jets a as out xs s) (c + wrapperCost n) (.jets a as out xs t) := by
  induction h with
  | nil s => simpa [wrapperCost, JetRootsMachine.wrapperCost, RegularRootMachine.wrapperCost,
      RegularLiftMachine.wrapperCost, DirectCoefficientMachine.wrapperCost,
      ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (D := D) (L := L) (.jets a as out xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, JetRootsMachine.wrapperCost, RegularRootMachine.wrapperCost,
          RegularLiftMachine.wrapperCost, DirectCoefficientMachine.wrapperCost,
          ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.jets head) ih

end ReedSolomon.HiddenDerivative.CenterRootsMachine
