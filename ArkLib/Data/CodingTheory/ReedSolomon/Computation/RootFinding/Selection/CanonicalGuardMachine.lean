/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualWitnessSemantics
/-!
# Closed canonical-stage and center guard

Given global candidate coefficients, the driver executes residual-zero checks for the supplied
earlier equations, then executes the first-nonzero witness search for the current separant.
It accepts exactly when the selected witness equals the candidate's supplied center. Each
callee advances one instruction per driver step. Scalar comparison, cursor operations, all
nested costs and final Boolean emission are charged. The equation chain, candidate, sample
list and their representations are supplied; constructing them belongs to the outer decoder.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CanonicalGuardMachine

open Polynomial MvPolynomial

abbrev Equation (F : Type*) := List (EvaluationMachine.Term F)

/-- Shared immutable candidate and sampling inputs; all coefficients are in global coordinates. -/
structure Input (F : Type*) where
  coefficients : List F
  samples : List F
  order : ℕ
  center : F
  separant : Equation F

/-- Global residual evaluation uses zero translation, not the candidate's regular center. -/
def residualInput {F : Type*} [Zero F] (input : Input F) (terms : Equation F) :
    ResidualBatchMachine.Input F := ⟨input.coefficients, terms, 0, input.order⟩

/-- Each zero-check call retains its equation and the unvisited chain tail. -/
inductive Configuration (F : Type*) where
  | start (previous : List (Equation F))
  | scan (previous : List (Equation F))
  | zero (equation : Equation F) (remaining : List (Equation F))
      (state : ResidualZeroMachine.Configuration F)
  | witness (state : ResidualWitnessMachine.Configuration F)
  | emit (accepted : Bool)
  | done (accepted : Bool)
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Independent rules expose earlier-identity acceptance and the final scalar-center test. -/
inductive Step (input : Input F) : Configuration F → ℕ → Configuration F → Prop where
  | start {ps} : Step input (.start ps) 4 (.scan ps)
  | take {q ps} : Step input (.scan (q :: ps)) 6 (.zero q ps (.start input.samples))
  | empty : Step input (.scan []) 6 (.witness (.start input.samples))
  | zero {q ps s t c} (h : ResidualZeroMachine.Step (residualInput input q) s c t) :
      Step input (.zero q ps s) (c.total + 3) (.zero q ps t)
  | passed {q ps} : Step input (.zero q ps (.done true)) 3 (.scan ps)
  | failed {q ps} : Step input (.zero q ps (.done false)) 3 (.emit false)
  | witness {s t c}
      (h : ResidualWitnessMachine.Step (residualInput input input.separant) s c t) :
      Step input (.witness s) (c.total + 3) (.witness t)
  | absent : Step input (.witness (.done none)) 3 (.emit false)
  | selected {u} : Step input (.witness (.done (some u))) 8 (.emit (decide (u = input.center)))
  | emit {b} : Step input (.emit b) 4 (.done b)

/-- Closed dispatch; neither a whole residual evaluation nor a chain predicate is a primitive. -/
def step (input : Input F) : Configuration F → Option (Configuration F × ℕ)
  | .start ps => some (.scan ps, 4)
  | .scan [] => some (.witness (.start input.samples), 6)
  | .scan (q :: ps) => some (.zero q ps (.start input.samples), 6)
  | .zero q ps s => match ResidualZeroMachine.step (residualInput input q) s with
      | some (t, c) => some (.zero q ps t, c.total + 3)
      | none => match s with
          | .done true => some (.scan ps, 3)
          | .done false => some (.emit false, 3)
          | _ => none
  | .witness s => match ResidualWitnessMachine.step (residualInput input input.separant) s with
      | some (t, c) => some (.witness t, c.total + 3)
      | none => match s with
          | .done none => some (.emit false, 3)
          | .done (some u) => some (.emit (decide (u = input.center)), 8)
          | _ => none
  | .emit b => some (.done b, 4)
  | .done _ => none

/-- Each independent instruction has its executable successor and complete charge. -/
theorem Step.step_eq {input : Input F} {s t : Configuration F} {c : ℕ}
    (h : Step input s c t) : step input s = some (t, c) := by
  cases h with
  | zero h => simp [step, h.step_eq]
  | witness h => simp [step, h.step_eq]
  | _ => rfl

/-- Every executed branch is covered by an operational rule. -/
theorem step_sound {input : Input F} {s t : Configuration F} {c : ℕ}
    (h : step input s = some (t, c)) : Step input s c t := by
  cases s with
  | start ps => cases h; constructor
  | scan ps => cases ps <;> cases h <;> constructor
  | emit b => cases h; constructor
  | done b => simp [step] at h
  | zero q ps s =>
      cases hs : ResidualZeroMachine.step (residualInput input q) s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.zero (ResidualZeroMachine.step_sound hs)
      | none =>
          cases s with
          | done b => cases b <;> cases h <;> constructor
          | _ => simp [step, hs] at h
  | witness s =>
      cases hs : ResidualWitnessMachine.step (residualInput input input.separant) s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.witness (ResidualWitnessMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases out <;> cases h <;> constructor
          | _ => simp [step, hs] at h

/-- Finite traces sum every callee category before adding actual caller work. -/
inductive Trace (input : Input F) : ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace input 0 s 0 s
  | cons {n s u t c d} (head : Step input s c u) (tail : Trace input n u d t) :
      Trace input (n + 1) s (c + d) t

/-- Concatenation retains instruction counts and scalar primitive work. -/
theorem Trace.trans {input : Input F} {n m : ℕ} {s t u : Configuration F} {c d : ℕ}
    (h : Trace input n s c t) (h' : Trace input m t d u) :
    Trace input (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Fuel exhaustion returns the current phase; all completed work remains in the ledger. -/
def runFuel (input : Input F) : ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step input s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel input n t; (r.1, c + r.2)

/-- Arbitrary runs refine cost-preserving operational trace prefixes. -/
theorem runFuel_refines (input : Input F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input n s (runFuel input fuel s).2 (runFuel input fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Surplus fuel leaves a completed execution and its cost unchanged. -/
theorem Trace.runFuel_done {input : Input F} {n : ℕ} {s : Configuration F} {c : ℕ}
    {b : Bool} (h : Trace input n s c (.done b)) (extra : ℕ) :
    runFuel input (n + extra) s = (.done b, c) := by
  generalize ht : Configuration.done b = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

private theorem total_add (a b : ResidualZeroMachine.Cost) :
    (a + b).total = a.total + b.total := by
  simp only [ResidualZeroMachine.Cost.total, ResidualZeroMachine.cost_add,
    JetHornerMachine.Cost.total, JetHornerMachine.cost_add]
  omega

/-- The identity checker advances one actual instruction, with its full caller charge. -/
theorem lift_zero (input : Input F) (q : Equation F) (ps : List (Equation F))
    {n : ℕ} {s t : ResidualZeroMachine.Configuration F} {c : ResidualZeroMachine.Cost}
    (h : ResidualZeroMachine.Trace (residualInput input q) n s c t) :
    Trace input n (.zero q ps s) (c.total + 3 * n) (.zero q ps t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.zero head) ih using 1
      rw [total_add]
      omega

/-- The ordered witness checker also preserves its entire primitive ledger. -/
theorem lift_witness (input : Input F)
    {n : ℕ} {s t : ResidualWitnessMachine.Configuration F} {c : ResidualWitnessMachine.Cost}
    (h : ResidualWitnessMachine.Trace (residualInput input input.separant) n s c t) :
    Trace input n (.witness s) (c.total + 3 * n) (.witness t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.witness head) ih using 1
      rw [total_add]
      omega

end ReedSolomon.HiddenDerivative.CanonicalGuardMachine
