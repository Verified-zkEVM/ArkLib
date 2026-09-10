/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectCoefficientRefinement
/-!
# Closed regular lifting loop

Every stage executes the direct coefficient machine and then the indexed update machine. Stage
counters, update-index arithmetic, callee wrappers, failures and the final output are charged.
The fixed-width initial coefficient vector and shared sample list are materialized inputs.
The emitted candidate still needs a full residual identity check before acceptance as a root.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.RegularLiftMachine

open Polynomial Matrix

abbrev Input := DirectCoefficientMachine.Input
abbrev Cost := DirectCoefficientMachine.Cost
abbrev totalCost := DirectCoefficientMachine.totalCost
abbrev withCoefficients := @DirectCoefficientMachine.withCoefficients
abbrev updateCost := DirectCoefficientMachine.updateCost
abbrev wrapperCost := DirectCoefficientMachine.wrapperCost

/-- Read input roots, set the first residual order and compute the remaining-stage counter. -/
def startCost : Cost := ⟨⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 2⟩, 0⟩
/-- Test/decrement remaining stages and initialize a direct coefficient call. -/
def stageCost : Cost := ⟨⟨⟨0, 0, 1, 6, 0⟩, 0, 0, 0, 2⟩, 0⟩
/-- Read gamma and vector roots, form `D-(k+r)` and initialize the actual update. -/
def directReturnCost : Cost := ⟨⟨⟨0, 0, 1, 6, 0⟩, 0, 0, 0, 2⟩, 0⟩
/-- Retain the updated vector and advance the residual order. -/
def updateReturnCost : Cost := ⟨⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 1⟩, 0⟩
/-- Test exhausted stages and retain the completed vector for emission. -/
def finishCost : Cost := ⟨⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 1⟩, 0⟩
/-- Retain a failed stage's tag. -/
def rejectCost : Cost := ⟨⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Emit the tagged candidate-vector root. -/
def emitCost : Cost := ⟨⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩, 0⟩

/-- Current vector, samples and counters persist across the two actual callees. -/
inductive Configuration (F : Type*) where
  | start (samples : List F)
  | loop (next remaining : ℕ) (cs samples : List F)
  | direct (next remaining : ℕ) (cs samples : List F)
      (state : DirectCoefficientMachine.Configuration F)
  | update (next remaining : ℕ) (samples : List F) (gamma : F)
      (state : CoefficientUpdateMachine.Configuration F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Operational rules retain every direct-solve and coefficient-update transition. -/
inductive Step (input : Input F) (D L : ℕ) :
    Configuration F → Cost → Configuration F → Prop where
  | start {xs} : Step input D L (.start xs) startCost
      (.loop 1 (D - input.order) input.coefficients xs)
  | finish {k cs xs} : Step input D L (.loop k 0 cs xs) finishCost (.emit (some cs))
  | stage {k n cs xs} : Step input D L (.loop k (n + 1) cs xs) stageCost
      (.direct k n cs xs (.start xs))
  | direct {k n cs xs s t c}
      (h : DirectCoefficientMachine.Step (withCoefficients input cs) (D + 1) L k s c t) :
      Step input D L (.direct k n cs xs s) (c + wrapperCost 1) (.direct k n cs xs t)
  | directReturn {k n cs xs gamma} :
      Step input D L (.direct k n cs xs (.done (some gamma))) directReturnCost
        (.update k n xs gamma (.start cs (D - (k + input.order))))
  | directReject {k n cs xs} :
      Step input D L (.direct k n cs xs (.done none)) rejectCost (.emit none)
  | update {k n xs gamma s t c} (h : CoefficientUpdateMachine.Step gamma s c t) :
      Step input D L (.update k n xs gamma s) (updateCost c + wrapperCost 1)
        (.update k n xs gamma t)
  | updateReturn {k n xs gamma cs} :
      Step input D L (.update k n xs gamma (.done (some cs))) updateReturnCost
        (.loop (k + 1) n cs xs)
  | updateReject {k n xs gamma} :
      Step input D L (.update k n xs gamma (.done none)) rejectCost (.emit none)
  | emit {out} : Step input D L (.emit out) emitCost (.done out)

/-- Each dispatch performs one callee step or one fixed administrative instruction. -/
def step (input : Input F) (D L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.loop 1 (D - input.order) input.coefficients xs, startCost)
  | .loop _ 0 cs _ => some (.emit (some cs), finishCost)
  | .loop k (n + 1) cs xs => some (.direct k n cs xs (.start xs), stageCost)
  | .direct k n cs xs s =>
      match DirectCoefficientMachine.step (withCoefficients input cs) (D + 1) L k s with
      | some (t, c) => some (.direct k n cs xs t, c + wrapperCost 1)
      | none => match s with
          | .done (some gamma) => some
              (.update k n xs gamma (.start cs (D - (k + input.order))), directReturnCost)
          | .done none => some (.emit none, rejectCost)
          | _ => none
  | .update k n xs gamma s => match CoefficientUpdateMachine.step gamma s with
      | some (t, c) => some (.update k n xs gamma t, updateCost c + wrapperCost 1)
      | none => match s with
          | .done (some cs) => some (.loop (k + 1) n cs xs, updateReturnCost)
          | .done none => some (.emit none, rejectCost)
          | _ => none
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Every rule agrees with the executable successor and charge. -/
theorem Step.step_eq {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step input D L s c t) : step input D L s = some (t, c) := by
  cases h with
  | direct h => simp [step, h.step_eq]
  | update h => simp [step, h.step_eq]
  | _ => rfl

/-- No interpreter transition escapes the independent rules. -/
theorem step_sound {input : Input F} {D L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step input D L s = some (t, c)) : Step input D L s c t := by
  cases s with
  | direct k n cs xs s =>
      cases hs : DirectCoefficientMachine.step (withCoefficients input cs) (D + 1) L k s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.direct (DirectCoefficientMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i out
          cases out <;> cases h <;> constructor
  | update k n xs gamma s =>
      cases hs : CoefficientUpdateMachine.step gamma s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.update (CoefficientUpdateMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i out
          cases out <;> cases h <;> constructor
  | loop k n cs xs => cases n <;> cases h <;> constructor
  | done out => simp [step] at h
  | _ => cases h; constructor

/-- Traces sum charges over actual transitions. -/
inductive Trace (input : Input F) (D L : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input D L 0 s 0 s
  | cons {n s u t c d} (head : Step input D L s c u) (tail : Trace input D L n u d t) :
      Trace input D L (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [ResidualCoefficientMachine.cost_add, PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add, Nat.add_assoc]

omit [DecidableEq F] in
/-- Concatenate stage traces without losing charges. -/
theorem Trace.trans {input : Input F} {D L n m : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Trace input D L n s c t) (h' : Trace input D L m t d u) :
    Trace input D L (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- Host fuel suspends the current stage instead of fabricating a candidate. -/
def runFuel (input : Input F) (D L : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input D L s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input D L n t; (result.1, c + result.2)

/-- Every run is an actual trace prefix with identical full cost. -/
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

/-- A completed trace consumes no additional work with surplus fuel. -/
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
/-- Lift every transition of an actual direct solve. -/
theorem lift_direct (input : Input F) (D L k remaining : ℕ) (cs xs : List F)
    {n : ℕ} {s t : DirectCoefficientMachine.Configuration F} {c : Cost}
    (h : DirectCoefficientMachine.Trace (withCoefficients input cs) (D + 1) L k n s c t) :
    Trace input D L n (.direct k remaining cs xs s) (c + wrapperCost n)
      (.direct k remaining cs xs t) := by
  induction h with
  | nil s => simpa [wrapperCost, DirectCoefficientMachine.wrapperCost,
      ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (D := D) (L := L) (.direct k remaining cs xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, DirectCoefficientMachine.wrapperCost,
          ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.direct head) ih

omit [DecidableEq F] in
/-- Lift the actual scalar update after a successful solve. -/
theorem lift_update (input : Input F) (D L k remaining : ℕ) (xs : List F) (gamma : F)
    {n : ℕ} {s t : CoefficientUpdateMachine.Configuration F} {c : CoefficientUpdateMachine.Cost}
    (h : CoefficientUpdateMachine.Trace gamma n s c t) :
    Trace input D L n (.update k remaining xs gamma s) (updateCost c + wrapperCost n)
      (.update k remaining xs gamma t) := by
  induction h with
  | nil s => simpa [updateCost, DirectCoefficientMachine.updateCost, wrapperCost,
      DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (D := D) (L := L) (.update k remaining xs gamma s)
  | @cons n s u t c d head tail ih =>
      have heq : (updateCost c + wrapperCost 1) + (updateCost d + wrapperCost n) =
          updateCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [updateCost, DirectCoefficientMachine.updateCost, wrapperCost,
          DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.update head) ih

end ReedSolomon.HiddenDerivative.RegularLiftMachine
