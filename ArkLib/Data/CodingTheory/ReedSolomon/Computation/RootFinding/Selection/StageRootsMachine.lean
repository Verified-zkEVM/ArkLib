/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.SeparantChainMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CenterRootsBounds
/-!
# Charged root enumeration over emitted separant stages

The driver runs the chain machine, visits its literal ordered records, and runs the center machine
at each active order. Earlier equations are retained in a reversed immutable list. A context is
allocated once per stage and shared by that stage's separately allocated candidate records.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.StageRootsMachine

open Matrix

abbrev Term := MvPolynomial.EvaluationMachine.Term
abbrev Stage := MvPolynomial.SeparantChainMachine.Stage
abbrev Cost := CenterRootsMachine.Cost
abbrev totalCost := CenterRootsMachine.totalCost
abbrev wrapperCost := CenterRootsMachine.wrapperCost
abbrev charge := CenterRootsMachine.charge

/-- Immutable guard context, created once at the current stage. Earlier equations are reversed. -/
structure Context (F : Type*) where
  stage : Stage F
  previous : List (List (Term F))
  separant : List (Term F)
  deriving DecidableEq, Repr

/-- A context root, center, and already materialized global coefficient-vector root. -/
structure Record (F : Type*) where
  context : Context F
  center : F
  coefficients : List F
  deriving DecidableEq, Repr

/-- The original maximum order is retained for the downstream guard; child orders are selected. -/
structure Input (F : Type*) where
  alphabet : List F
  terms : List (Term F)
  order : ℕ

/-- Stage input retains its actual sparse equation without trimming or jet re-enumeration. -/
def centerInput {F : Type*} (input : Input F) (stage : Stage F) (r : ℕ) :
    CenterRootsMachine.Input F := ⟨input.alphabet, stage.equation, r⟩

/-- Retain all chain arithmetic, comparison, traversal and output charges. -/
def chainCost (c : MvPolynomial.SeparantChainMachine.Cost) : Cost :=
  ⟨⟨⟨c.work.additions, c.work.multiplications, c.work.control, c.work.data, c.work.output⟩,
    0, 0, c.equalities, c.work.natural⟩, 0⟩

/-- Every child instruction and every context, prefix, record and output cell is explicit. -/
inductive Configuration (F : Type*) where
  | start (samples : List F)
  | chain (samples : List F) (state : MvPolynomial.SeparantChainMachine.Configuration F)
  | scan (stages : List (Stage F)) (previous : List (List (Term F)))
      (out : List (Record F)) (samples : List F)
  | select (stage : Stage F) (stages : List (Stage F))
      (previous nextPrevious : List (List (Term F))) (out : List (Record F)) (samples : List F)
  | roots (context : Context F) (r : ℕ) (stages : List (Stage F))
      (previous : List (List (Term F))) (out : List (Record F)) (samples : List F)
      (state : CenterRootsMachine.Configuration F)
  | collect (context : Context F) (candidates : List (CenterRootsMachine.Record F))
      (stages : List (Stage F)) (previous : List (List (Term F)))
      (out : List (Record F)) (samples : List F)
  | save (record : Record F) (context : Context F)
      (candidates : List (CenterRootsMachine.Record F)) (stages : List (Stage F))
      (previous : List (List (Term F))) (out : List (Record F)) (samples : List F)
  | reverse (remaining output : List (Record F))
  | emit (out : Option (List (Record F)))
  | done (out : Option (List (Record F)))
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent rules expose each callee dispatch and each allocation. -/
inductive Step (input : Input F) (D L : ℕ) :
    Configuration F → Cost → Configuration F → Prop where
  | start {xs} : Step input D L (.start xs) (charge 3 0 0)
      (.chain xs (MvPolynomial.SeparantChainMachine.initial input.terms))
  | chain {xs s t c} (h : MvPolynomial.SeparantChainMachine.step s = some (t, c)) :
      Step input D L (.chain xs s) (chainCost c + wrapperCost 1) (.chain xs t)
  | chained {xs stages} : Step input D L (.chain xs (.done stages)) (charge 4 0 0)
      (.scan stages [] [] xs)
  | next {stage stages pre out xs} :
      Step input D L (.scan (stage :: stages) pre out xs) (charge 8 0 0)
        (.select stage stages pre (stage.equation :: pre) out xs)
  | terminal {stage stages pre nextPre out xs} (h : stage.selected = none) :
      Step input D L (.select stage stages pre nextPre out xs) (charge 3 0 0)
        (.scan stages nextPre out xs)
  | invalid {stage stages pre nextPre out xs e} (h : stage.selected = some (0, e)) :
      Step input D L (.select stage stages pre nextPre out xs) (charge 3 1 0) (.emit none)
  | missing {stage pre nextPre out xs r e} (h : stage.selected = some (r + 1, e)) :
      Step input D L (.select stage [] pre nextPre out xs) (charge 4 2 0) (.emit none)
  | active {stage next stages pre nextPre out xs r e}
      (h : stage.selected = some (r + 1, e)) :
      Step input D L (.select stage (next :: stages) pre nextPre out xs) (charge 12 2 0)
        (.roots ⟨stage, pre, next.equation⟩ r (next :: stages) nextPre out xs (.start xs))
  | roots {context r stages pre out xs s t c}
      (h : CenterRootsMachine.Step (centerInput input context.stage r) D L s c t) :
      Step input D L (.roots context r stages pre out xs s) (c + wrapperCost 1)
        (.roots context r stages pre out xs t)
  | returned {context r stages pre out xs candidates} :
      Step input D L (.roots context r stages pre out xs (.done (some candidates))) (charge 5 0 0)
        (.collect context candidates stages pre out xs)
  | failed {context r stages pre out xs} :
      Step input D L (.roots context r stages pre out xs (.done none)) (charge 2 0 0) (.emit none)
  | record {context a cs candidates stages pre out xs} :
      Step input D L (.collect context ((a, cs) :: candidates) stages pre out xs) (charge 8 0 0)
        (.save ⟨context, a, cs⟩ context candidates stages pre out xs)
  | save {record context candidates stages pre out xs} :
      Step input D L (.save record context candidates stages pre out xs) (charge 6 0 0)
        (.collect context candidates stages pre (record :: out) xs)
  | collected {context stages pre out xs} :
      Step input D L (.collect context [] stages pre out xs) (charge 3 0 0)
        (.scan stages pre out xs)
  | scanned {pre out xs} :
      Step input D L (.scan [] pre out xs) (charge 2 0 0) (.reverse out [])
  | reverse {a as out} : Step input D L (.reverse (a :: as) out) (charge 5 0 0)
      (.reverse as (a :: out))
  | reversed {out} : Step input D L (.reverse [] out) (charge 2 0 0) (.emit (some out))
  | emit {out} : Step input D L (.emit out) (charge 2 0 1) (.done out)

/-- Closed dispatch uses only actual child steps, record reads, and bounded allocations. -/
def step (input : Input F) (D L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs =>
      some (.chain xs (MvPolynomial.SeparantChainMachine.initial input.terms), charge 3 0 0)
  | .chain xs s => match MvPolynomial.SeparantChainMachine.step s with
      | some (t, c) => some (.chain xs t, chainCost c + wrapperCost 1)
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
                (.start xs), charge 12 2 0)
  | .roots context r stages pre out xs s =>
      match CenterRootsMachine.step (centerInput input context.stage r) D L s with
      | some (t, c) => some (.roots context r stages pre out xs t, c + wrapperCost 1)
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
  | .reverse [] out => some (.emit (some out), charge 2 0 0)
  | .emit out => some (.done out, charge 2 0 1)
  | .done _ => none

/-- Independent rules agree with dispatch and its complete primitive charge. -/
theorem Step.step_eq {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step input D L s c t) : step input D L s = some (t, c) := by
  cases h with
  | chain h => simp [step, h]
  | roots h => simp [step, h.step_eq]
  | terminal h => simp [step, h]
  | invalid h => simp [step, h]
  | missing h => simp [step, h]
  | active h => simp [step, h]
  | _ => rfl

/-- Every dispatch branch has a corresponding independent transition rule. -/
theorem step_sound {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step input D L s = some (t, c)) : Step input D L s c t := by
  cases s with
  | chain xs s =>
      cases hs : MvPolynomial.SeparantChainMachine.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.chain hs
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          cases h
          exact Step.chained
  | roots context r stages pre out xs s =>
      cases hs : CenterRootsMachine.step (centerInput input context.stage r) D L s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.roots (CenterRootsMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i result
          cases result <;> cases h <;> constructor
  | select stage stages pre nextPre out xs =>
      cases hs : stage.selected with
      | none =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.terminal hs
      | some pair =>
          rcases pair with ⟨i, e⟩
          cases i with
          | zero =>
              simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact Step.invalid hs
          | succ r =>
              cases stages <;> simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
              all_goals rcases h with ⟨rfl, rfl⟩
              · exact Step.missing hs
              · exact Step.active hs
  | scan stages pre out xs => cases stages <;> cases h <;> constructor
  | collect context candidates stages pre out xs =>
      cases candidates with
      | nil => cases h; constructor
      | cons pair candidates => rcases pair with ⟨a, cs⟩; cases h; constructor
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


/-- Every center transition retains its full cost and a fixed caller dispatch. -/
theorem lift_roots (input : Input F) (D L : ℕ) (context : Context F) (r : ℕ)
    (stages : List (Stage F)) (pre : List (List (Term F))) (out : List (Record F)) (xs : List F)
    {n : ℕ} {s t : CenterRootsMachine.Configuration F} {c : Cost}
    (h : CenterRootsMachine.Trace (centerInput input context.stage r) D L n s c t) :
    Trace input D L n (.roots context r stages pre out xs s) (c + wrapperCost n)
      (.roots context r stages pre out xs t) := by
  induction h with
  | nil s => simpa [wrapperCost, CenterRootsMachine.wrapperCost, JetRootsMachine.wrapperCost,
      RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (D := D) (L := L) (.roots context r stages pre out xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, CenterRootsMachine.wrapperCost, JetRootsMachine.wrapperCost,
          RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.roots head) ih

/-- Each chain instruction retains every primitive category and its parent dispatch. -/
theorem lift_chain (input : Input F) (D L : ℕ) (xs : List F)
    {n : ℕ} {s t : MvPolynomial.SeparantChainMachine.Configuration F}
    {c : MvPolynomial.SeparantChainMachine.Cost}
    (h : MvPolynomial.SeparantChainMachine.Trace n s c t) :
    Trace input D L n (.chain xs s) (chainCost c + wrapperCost n) (.chain xs t) := by
  induction h with
  | nil s => simpa [chainCost, wrapperCost, CenterRootsMachine.wrapperCost,
      JetRootsMachine.wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (D := D) (L := L) (.chain xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (chainCost c + wrapperCost 1) + (chainCost d + wrapperCost n) =
          chainCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [chainCost, wrapperCost, CenterRootsMachine.wrapperCost,
          JetRootsMachine.wrapperCost, RegularRootMachine.wrapperCost,
          RegularLiftMachine.wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.chain head.step_eq) ih

end ReedSolomon.HiddenDerivative.StageRootsMachine
