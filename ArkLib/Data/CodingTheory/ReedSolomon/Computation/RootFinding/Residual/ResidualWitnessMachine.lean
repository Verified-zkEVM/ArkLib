/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualZeroMachine
/-!
# The first nonzero sampled residual

The closed batch evaluator computes every supplied sample. A charged cursor then returns the
first point with nonzero value, or none if all values vanish. In particular this is an ordered
witness, not an arbitrary existential choice. The intended root-enumeration consumer uses it
to choose one regular center per candidate without pairwise comparison of candidate lists.

All batch categories, scalar comparisons, cursor operations and tagged emission are counted.
Point enumeration, input construction and scalar bit costs remain separate obligations.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualWitnessMachine

open Polynomial MvPolynomial

abbrev Input := ResidualBatchMachine.Input
abbrev Cost := ResidualZeroMachine.Cost
abbrev batchCost := ResidualZeroMachine.batchCost
abbrev wrapperCost := ResidualZeroMachine.wrapperCost
abbrev entryCost := ResidualZeroMachine.entryCost
abbrev handoffCost := ResidualZeroMachine.handoffCost
abbrev checkCost := ResidualZeroMachine.checkCost
abbrev emptyCost := ResidualZeroMachine.emptyCost

/-- Read the result, allocate its optional payload and emit the tagged scalar. -/
def emitCost : Cost := ⟨⟨0, 0, 1, 3, 0, 1⟩, 0⟩

/-- Actual batch states are retained until their emitted list can be scanned. -/
inductive Configuration (F : Type*) where
  | start (points : List F)
  | batch (state : ResidualBatchMachine.Configuration F)
  | scan (remaining : List (F × F))
  | emit (result : Option F)
  | done (result : Option F)
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- A successful branch exposes the nonzero scalar comparison that justifies its witness. -/
inductive Step (input : Input F) : Configuration F → Cost → Configuration F → Prop where
  | enter {ps} : Step input (.start ps) entryCost (.batch (.start ps))
  | batch {s t c} (h : ResidualBatchMachine.Step input s c t) :
      Step input (.batch s) (batchCost c + wrapperCost 1) (.batch t)
  | handoff {ps} : Step input (.batch (.done ps)) handoffCost (.scan ps)
  | zero {u v ps} (h : v = 0) : Step input (.scan ((u, v) :: ps)) checkCost (.scan ps)
  | nonzero {u v ps} (h : v ≠ 0) :
      Step input (.scan ((u, v) :: ps)) checkCost (.emit (some u))
  | empty : Step input (.scan []) emptyCost (.emit none)
  | emit {out} : Step input (.emit out) emitCost (.done out)

/-- Each call advances a single batch instruction or tests one already materialized value. -/
def step (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start ps => some (.batch (.start ps), entryCost)
  | .batch s => match ResidualBatchMachine.step input s with
      | some (t, c) => some (.batch t, batchCost c + wrapperCost 1)
      | none => match s with
          | .done ps => some (.scan ps, handoffCost)
          | _ => none
  | .scan [] => some (.emit none, emptyCost)
  | .scan ((u, v) :: ps) =>
      if v = 0 then some (.scan ps, checkCost) else some (.emit (some u), checkCost)
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Independent rules agree with executable dispatch, including its equality branch. -/
theorem Step.step_eq {input : Input F} {s t : Configuration F} {c : Cost}
    (h : Step input s c t) : step input s = some (t, c) := by
  cases h with
  | batch h => simp [step, h.step_eq]
  | zero h => simp [step, h]
  | nonzero h => simp [step, h]
  | _ => rfl

/-- Every executed instruction has the same charge in the operational semantics. -/
theorem step_sound {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step input s = some (t, c)) : Step input s c t := by
  cases s with
  | start ps => cases h; exact Step.enter
  | emit out => cases h; exact Step.emit
  | done out => simp [step] at h
  | scan ps =>
      cases ps with
      | nil => cases h; exact Step.empty
      | cons p ps =>
          rcases p with ⟨u, v⟩
          by_cases hv : v = 0
          · simp only [step, hv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact Step.zero hv
          · simp only [step, hv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact Step.nonzero hv
  | batch s =>
      cases hs : ResidualBatchMachine.step input s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.batch (ResidualBatchMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.handoff

/-- Finite executions preserve every nested cost category. -/
inductive Trace (input : Input F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input 0 s 0 s
  | cons {n s u t c d} (head : Step input s c u) (tail : Trace input n u d t) :
      Trace input (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [ResidualZeroMachine.cost_add, JetHornerMachine.cost_add, Nat.add_assoc]

omit [DecidableEq F] in
/-- Concatenation adds lengths and the complete primitive ledger. -/
theorem Trace.trans {input : Input F} {n m : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Trace input n s c t) (h' : Trace input m t d u) :
    Trace input (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- Insufficient fuel returns the suspended configuration, not a guessed witness. -/
def runFuel (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input n t; (result.1, c + result.2)

/-- Every partial interpreter run refines a trace with identical charges. -/
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

/-- Completed traces remain unchanged under surplus fuel. -/
theorem Trace.runFuel_done {input : Input F} {n : ℕ} {s : Configuration F} {c : Cost}
    {out : Option F} (h : Trace input n s c (.done out)) (extra : ℕ) :
    runFuel input (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

/-- Proof-only ordered search; the interpreter instead executes individual comparisons. -/
def scanSpec : List (F × F) → Option F
  | [] => none
  | (u, v) :: ps => if v = 0 then scanSpec ps else some u
/-- Exact number of scan transitions, including tagged emission. -/
def scanSteps : List (F × F) → ℕ
  | [] => 2
  | (_, v) :: ps => if v = 0 then scanSteps ps + 1 else 2
/-- Exact scan charge depends on the position of the first nonzero value. -/
def scanCost : List (F × F) → Cost
  | [] => emptyCost + emitCost
  | (_, v) :: ps => if v = 0 then checkCost + scanCost ps else checkCost + emitCost

/-- The ordered search executes with its exact charge and transition count. -/
theorem scan_trace (input : Input F) (ps : List (F × F)) :
    Trace input (scanSteps ps) (.scan ps) (scanCost ps) (.done (scanSpec ps)) := by
  induction ps with
  | nil =>
      simpa [scanSteps, scanCost, scanSpec] using
        Trace.cons (Step.empty (input := input)) (Trace.cons Step.emit (Trace.nil (.done none)))
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      by_cases hv : v = 0
      · simpa [scanSteps, scanCost, scanSpec, hv] using Trace.cons (Step.zero hv) ih
      · simpa [scanSteps, scanCost, scanSpec, hv] using
          Trace.cons (Step.nonzero (input := input) (ps := ps) hv)
            (Trace.cons Step.emit (Trace.nil (.done (some u))))

/-- The scan visits at most every supplied pair once. -/
theorem scanSteps_le (ps : List (F × F)) : scanSteps ps ≤ ps.length + 2 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      by_cases hv : v = 0
      · simp only [scanSteps, if_pos hv, List.length_cons]; omega
      · simp [scanSteps, hv]

omit [DecidableEq F] in
/-- Every actual batch transition is retained, together with its caller dispatch. -/
theorem lift_batch_trace (input : Input F) {n : ℕ}
    {s t : ResidualBatchMachine.Configuration F} {c : JetHornerMachine.Cost}
    (h : ResidualBatchMachine.Trace input n s c t) :
    Trace input n (.batch s) (batchCost c + wrapperCost n) (.batch t) := by
  induction h with
  | nil s => simpa [batchCost, wrapperCost, ResidualZeroMachine.batchCost,
      ResidualZeroMachine.wrapperCost] using Trace.nil (input := input) (.batch s)
  | @cons n s u t c d head tail ih =>
      have heq : (batchCost c + wrapperCost 1) + (batchCost d + wrapperCost n) =
          batchCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [batchCost, wrapperCost, ResidualZeroMachine.batchCost,
          ResidualZeroMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.batch head) ih

/-- Uniform host fuel includes the longest possible scan. -/
def fuel (input : Input F) (n : ℕ) : ℕ := ResidualBatchMachine.fuel input n + n + 4
/-- Ordered witness specification, with none precisely for an all-zero sample list. -/
def result (input : Input F) (ps : List F) : Option F :=
  scanSpec (ResidualBatchMachine.outputSpec input ps)
/-- Polynomial work bound; the complete batch cost remains visible. -/
def workBound (input : Input F) (n : ℕ) : ℕ :=
  (ResidualBatchMachine.cost input n).total + 3 * ResidualBatchMachine.fuel input n + 6 * n + 16

private theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [ResidualZeroMachine.Cost.total, ResidualZeroMachine.cost_add,
    JetHornerMachine.Cost.total, JetHornerMachine.cost_add]
  omega

/-- The search overhead is linear, including comparisons and optional-result allocation. -/
theorem scanCost_total_le (ps : List (F × F)) : (scanCost ps).total ≤ 6 * ps.length + 7 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      by_cases hv : v = 0
      · simp only [scanCost, if_pos hv, total_add]
        change 6 + (scanCost ps).total ≤ 6 * (ps.length + 1) + 7
        omega
      · simp only [scanCost, if_neg hv, total_add]
        change 11 ≤ 6 * (ps.length + 1) + 7
        omega

/-- The actual composed execution returns the first nonzero sample with a bound on that run. -/
theorem witness_runFuel (input : Input F) (ps : List F) :
    ∃ c, runFuel input (fuel input ps.length) (.start ps) =
      (.done (result input ps), c) ∧ c.total ≤ workBound input ps.length := by
  obtain ⟨n, hn, ht⟩ := ResidualBatchMachine.runFuel_refines input
    (ResidualBatchMachine.fuel input ps.length) (.start ps)
  rw [ResidualBatchMachine.batch_runFuel] at ht
  have hb := lift_batch_trace input ht
  have htrace := Trace.cons Step.enter (hb.trans (Trace.cons Step.handoff
    (scan_trace input (ResidualBatchMachine.outputSpec input ps))))
  have hs := scanSteps_le (ResidualBatchMachine.outputSpec input ps)
  have hc := scanCost_total_le (ResidualBatchMachine.outputSpec input ps)
  have hlen : (ResidualBatchMachine.outputSpec input ps).length = ps.length := by
    simp [ResidualBatchMachine.outputSpec]
  rw [hlen] at hs hc
  have hbudget : n + (scanSteps (ResidualBatchMachine.outputSpec input ps) + 1) + 1 ≤
      fuel input ps.length := by dsimp [fuel]; omega
  have hrun := htrace.runFuel_done (fuel input ps.length -
    (n + (scanSteps (ResidualBatchMachine.outputSpec input ps) + 1) + 1))
  rw [Nat.add_sub_of_le hbudget] at hrun
  refine ⟨_, hrun, ?_⟩
  simp only [total_add]
  dsimp only [workBound]
  simp only [batchCost, wrapperCost, entryCost, handoffCost, ResidualZeroMachine.batchCost,
    ResidualZeroMachine.wrapperCost, ResidualZeroMachine.entryCost, ResidualZeroMachine.handoffCost,
    ResidualZeroMachine.Cost.total, JetHornerMachine.Cost.total] at hc ⊢
  omega

end ReedSolomon.HiddenDerivative.ResidualWitnessMachine
