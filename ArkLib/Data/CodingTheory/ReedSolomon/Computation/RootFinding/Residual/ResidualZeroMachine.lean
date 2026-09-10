/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualBatchMachine
/-!
# Closed residual-zero checking

The actual batch machine first emits its point-value pairs. A second phase scans their values,
charging one equality-to-zero test per visited pair and stopping at the first nonzero value.
Exhaustion returns true. Both outcomes have a separately charged Boolean emission.

All batch arithmetic, data, natural-operation and output costs are retained. Outer dispatches,
handoffs, pair reads and equality tests are added explicitly. Retained registers are shared;
zero is a literal in the inherited model. Host fuel, input preparation, point enumeration,
bit costs and solving remain outside this subroutine. The full-residual refinement requires
explicit degree and distinct-sample hypotheses; this machine does not check prefix degree.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualZeroMachine

open PolynomialDifferential
open Polynomial MvPolynomial CompPoly

abbrev Input := ResidualBatchMachine.Input

/-- Preserve all batch categories and separately count scalar equality tests. -/
@[ext] structure Cost where
  machine : JetHornerMachine.Cost
  equalities : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0⟩⟩
instance : Add Cost := ⟨fun a b ↦ ⟨a.machine + b.machine, a.equalities + b.equalities⟩⟩
@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.machine + b.machine, a.equalities + b.equalities⟩ := rfl

/-- Total primitive charge includes the additional field equalities. -/
def Cost.total (c : Cost) : ℕ := c.machine.total + c.equalities
/-- Embed every batch charge, including its nested scalar emissions. -/
def batchCost (c : JetHornerMachine.Cost) : Cost := ⟨c, 0⟩
/-- Each outer delegation reads and writes the batch state root. -/
def wrapperCost (n : ℕ) : Cost := ⟨⟨0, 0, n, 2 * n, 0, 0⟩, 0⟩
/-- Read the materialized point-list root and initialize the callee state. -/
def entryCost : Cost := ⟨⟨0, 0, 1, 3, 0, 0⟩, 0⟩
/-- Read the emitted pair-list root and initialize its scan cursor. -/
def handoffCost : Cost := ⟨⟨0, 0, 1, 2, 0, 0⟩, 0⟩
/-- Read a cell and its value, test against zero, and update cursor or result payload. -/
def checkCost : Cost := ⟨⟨0, 0, 1, 4, 0, 0⟩, 1⟩
/-- Read the exhausted cursor and select true. -/
def emptyCost : Cost := ⟨⟨0, 0, 1, 1, 0, 0⟩, 0⟩
/-- Read and emit the Boolean result. -/
def emitCost : Cost := ⟨⟨0, 0, 1, 2, 0, 1⟩, 0⟩

/-- The actual batch configuration is retained during delegated execution. -/
inductive Configuration (F : Type*) where
  | start (samples : List F)
  | batch (state : ResidualBatchMachine.Configuration F)
  | scan (remaining : List (F × F))
  | emit (result : Bool)
  | done (result : Bool)
  deriving DecidableEq, Repr

variable {F : Type*}

section Semiring

variable [CommSemiring F] [DecidableEq F]

/-- Independent operational rules expose the branch condition of every scalar test. -/
inductive Step (input : Input F) : Configuration F → Cost → Configuration F → Prop where
  | enter {ps} : Step input (.start ps) entryCost (.batch (.start ps))
  | batch {s t c} (h : ResidualBatchMachine.Step input s c t) :
      Step input (.batch s) (batchCost c + wrapperCost 1) (.batch t)
  | handoff {ps} : Step input (.batch (.done ps)) handoffCost (.scan ps)
  | zero {u v ps} (h : v = 0) : Step input (.scan ((u, v) :: ps)) checkCost (.scan ps)
  | nonzero {u v ps} (h : v ≠ 0) : Step input (.scan ((u, v) :: ps)) checkCost (.emit false)
  | empty : Step input (.scan []) emptyCost (.emit true)
  | emit {b} : Step input (.emit b) emitCost (.done b)

/-- Closed dispatch performs one batch step or one scalar test, never a bulk evaluator or `all`. -/
def step (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start ps => some (.batch (.start ps), entryCost)
  | .batch s => match ResidualBatchMachine.step input s with
      | some (t, c) => some (.batch t, batchCost c + wrapperCost 1)
      | none => match s with
          | .done ps => some (.scan ps, handoffCost)
          | _ => none
  | .scan [] => some (.emit true, emptyCost)
  | .scan ((_, v) :: ps) =>
      if v = 0 then some (.scan ps, checkCost) else some (.emit false, checkCost)
  | .emit b => some (.done b, emitCost)
  | .done _ => none

/-- Every independent transition has its stated executable successor and charge. -/
theorem Step.step_eq {input : Input F} {s t : Configuration F} {c : Cost}
    (h : Step input s c t) : step input s = some (t, c) := by
  cases h with
  | batch h => simp [step, h.step_eq]
  | zero h => simp [step, h]
  | nonzero h => simp [step, h]
  | _ => rfl

/-- Every executable branch is justified by an independent rule. -/
theorem step_sound {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step input s = some (t, c)) : Step input s c t := by
  cases s with
  | start ps => cases h; exact Step.enter
  | emit b => cases h; exact Step.emit
  | done b => simp [step] at h
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

/-- Traces retain all charges from actual transitions. -/
inductive Trace (input : Input F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input 0 s 0 s
  | cons {n s u t c d} (head : Step input s c u) (tail : Trace input n u d t) :
      Trace input (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [cost_add, JetHornerMachine.cost_add, Nat.add_assoc]

omit [DecidableEq F] in
/-- Concatenation preserves exact transition count and primitive charges. -/
theorem Trace.trans {input : Input F} {n m : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Trace input n s c t) (h' : Trace input m t d u) :
    Trace input (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- Insufficient fuel exposes the actual phase rather than fabricating a Boolean result. -/
def runFuel (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input n t; (result.1, c + result.2)

/-- Every interpreter result refines an actual cost-preserving trace. -/
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

/-- Extra host fuel leaves completed traces and their charged costs unchanged. -/
theorem Trace.runFuel_done {input : Input F} {n : ℕ} {s : Configuration F} {c : Cost}
    {b : Bool} (h : Trace input n s c (.done b)) (extra : ℕ) :
    runFuel input (n + extra) s = (.done b, c) := by
  generalize ht : Configuration.done b = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

/-- Proof-only Boolean scan specification with early exit. -/
def scanSpec : List (F × F) → Bool
  | [] => true
  | (_, v) :: ps => if v = 0 then scanSpec ps else false
/-- Exact number of transitions used by the scan, including emission. -/
def scanSteps : List (F × F) → ℕ
  | [] => 2
  | (_, v) :: ps => if v = 0 then scanSteps ps + 1 else 2
/-- Exact scan charges depend on the first nonzero value, not the full list length. -/
def scanCost : List (F × F) → Cost
  | [] => emptyCost + emitCost
  | (_, v) :: ps => if v = 0 then checkCost + scanCost ps else checkCost + emitCost

/-- Every scan terminates and emits its specified Boolean with the exact early-exit cost. -/
theorem scan_trace (input : Input F) (ps : List (F × F)) :
    Trace input (scanSteps ps) (.scan ps) (scanCost ps) (.done (scanSpec ps)) := by
  induction ps with
  | nil =>
      simpa [scanSteps, scanCost, scanSpec] using
        Trace.cons (Step.empty (input := input)) (Trace.cons Step.emit (Trace.nil (.done true)))
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      by_cases hv : v = 0
      · simpa [scanSteps, scanCost, scanSpec, hv] using Trace.cons (Step.zero hv) ih
      · simpa [scanSteps, scanCost, scanSpec, hv] using
          Trace.cons (Step.nonzero (input := input) (ps := ps) hv)
            (Trace.cons Step.emit (Trace.nil (.done false)))

/-- Scan fuel is bounded by one test per pair, an exhaustion branch, and emission. -/
theorem scanSteps_le (ps : List (F × F)) : scanSteps ps ≤ ps.length + 2 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      by_cases hv : v = 0
      · simp only [scanSteps, if_pos hv, List.length_cons]
        omega
      · simp [scanSteps, hv]

/-- The emitted Boolean is true exactly when all sampled second coordinates vanish. -/
theorem scanSpec_eq_true_iff (ps : List (F × F)) :
    scanSpec ps = true ↔ ∀ p ∈ ps, p.2 = 0 := by
  induction ps with
  | nil => simp [scanSpec]
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      by_cases hv : v = 0 <;> simp [scanSpec, hv, ih]

omit [DecidableEq F] in
/-- Lift each actual batch transition, preserving all nested fields and outputs. -/
theorem lift_batch_trace (input : Input F) {n : ℕ}
    {s t : ResidualBatchMachine.Configuration F} {c : JetHornerMachine.Cost}
    (h : ResidualBatchMachine.Trace input n s c t) :
    Trace input n (.batch s) (batchCost c + wrapperCost n) (.batch t) := by
  induction h with
  | nil s => simpa [batchCost, wrapperCost] using Trace.nil (input := input) (.batch s)
  | @cons n s u t c d head tail ih =>
      have heq : (batchCost c + wrapperCost 1) + (batchCost d + wrapperCost n) =
          batchCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [batchCost, wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.batch head) ih

omit [DecidableEq F] in
private theorem full_batch_trace (input : Input F) (ps : List F) :
    ResidualBatchMachine.Trace input (ResidualBatchMachine.fuel input ps.length) (.start ps)
      (ResidualBatchMachine.cost input ps.length)
      (.done (ResidualBatchMachine.outputSpec input ps)) := by
  have ht := ResidualBatchMachine.Trace.cons ResidualBatchMachine.Step.start
    (ResidualBatchMachine.scan_trace input ps [])
  convert ht using 1
  · simp [ResidualBatchMachine.fuel]
  · ext <;> simp [ResidualBatchMachine.cost, ResidualBatchMachine.scaleCost,
      ResidualBatchMachine.startCost, ResidualBatchMachine.beginReverseCost,
      ResidualBatchMachine.emitCost] <;> omega
  · simp

/-- Uniform supplied host fuel covers the complete batch and the longest possible scan. -/
def fuel (input : Input F) (n : ℕ) : ℕ := ResidualBatchMachine.fuel input n + n + 4
/-- Mathematical Boolean result; dispatch never evaluates this bulk specification. -/
def result (input : Input F) (ps : List F) : Bool :=
  scanSpec (ResidualBatchMachine.outputSpec input ps)
/-- Exact full charge, including the value-dependent early-exit scan. -/
def cost (input : Input F) (ps : List F) : Cost := entryCost +
  (batchCost (ResidualBatchMachine.cost input ps.length) +
    wrapperCost (ResidualBatchMachine.fuel input ps.length)) +
  handoffCost + scanCost (ResidualBatchMachine.outputSpec input ps)

/-- Actual execution always terminates with the specified Boolean and complete primitive charge. -/
theorem zero_runFuel (input : Input F) (ps : List F) :
    runFuel input (fuel input ps.length) (.start ps) =
      (.done (result input ps), cost input ps) := by
  have hb := lift_batch_trace input (full_batch_trace input ps)
  have ht := Trace.cons Step.enter (hb.trans (Trace.cons Step.handoff
    (scan_trace input (ResidualBatchMachine.outputSpec input ps))))
  have hs := scanSteps_le (ResidualBatchMachine.outputSpec input ps)
  have hlen : (ResidualBatchMachine.outputSpec input ps).length = ps.length := by
    simp [ResidualBatchMachine.outputSpec]
  rw [hlen] at hs
  have hrun := ht.runFuel_done (fuel input ps.length -
    (ResidualBatchMachine.fuel input ps.length +
      (scanSteps (ResidualBatchMachine.outputSpec input ps) + 1) + 1))
  have heq : ResidualBatchMachine.fuel input ps.length +
      (scanSteps (ResidualBatchMachine.outputSpec input ps) + 1) + 1 +
      (fuel input ps.length - (ResidualBatchMachine.fuel input ps.length +
        (scanSteps (ResidualBatchMachine.outputSpec input ps) + 1) + 1)) =
      fuel input ps.length := by
    dsimp [fuel]
    omega
  rw [heq] at hrun
  simpa only [result, cost, cost_assoc] using hrun

/-- Boolean correctness for every supplied sample list, allowing duplicates and empty lists. -/
theorem result_eq_true_iff (input : Input F) (ps : List F) :
    result input ps = true ↔ ∀ u ∈ ps, ResidualBatchMachine.sampleValue input u = 0 := by
  simp [result, scanSpec_eq_true_iff, ResidualBatchMachine.outputSpec]

private theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [Cost.total, cost_add, JetHornerMachine.Cost.total, JetHornerMachine.cost_add]
  omega

/-- The scan adds at most a linear number of charged tests and administrative operations. -/
theorem scanCost_total_le (ps : List (F × F)) : (scanCost ps).total ≤ 6 * ps.length + 6 := by
  induction ps with
  | nil => simp [scanCost, Cost.total, emptyCost, emitCost, JetHornerMachine.Cost.total]
  | cons p ps ih =>
      rcases p with ⟨u, v⟩
      by_cases hv : v = 0
      · simp only [scanCost, if_pos hv, total_add]
        change 6 + (scanCost ps).total ≤ 6 * (ps.length + 1) + 6
        omega
      · simp [scanCost, hv, Cost.total, checkCost, emitCost, JetHornerMachine.Cost.total]
        omega

/-- Bound retains the complete batch cost and adds only wrappers and the linear zero scan. -/
theorem cost_total_le (input : Input F) (ps : List F) :
    (cost input ps).total ≤ (ResidualBatchMachine.cost input ps.length).total +
      3 * ResidualBatchMachine.fuel input ps.length + 6 * ps.length + 15 := by
  have hs := scanCost_total_le (ResidualBatchMachine.outputSpec input ps)
  have hlen : (ResidualBatchMachine.outputSpec input ps).length = ps.length := by
    simp [ResidualBatchMachine.outputSpec]
  rw [hlen] at hs
  simp only [Cost.total, JetHornerMachine.Cost.total] at hs
  simp only [cost, total_add]
  simp only [batchCost, wrapperCost, entryCost, handoffCost, Cost.total,
    JetHornerMachine.Cost.total]
  omega

/-- The primitive bound holds for the actual terminating run. -/
theorem zero_cost_le (input : Input F) (ps : List F) :
    (runFuel input (fuel input ps.length) (.start ps)).2.total ≤
      (ResidualBatchMachine.cost input ps.length).total +
        3 * ResidualBatchMachine.fuel input ps.length + 6 * ps.length + 15 := by
  rw [zero_runFuel]
  exact cost_total_le input ps

end Semiring

section Concrete

variable [Field F] [DecidableEq F] {r D L : ℕ}

/-- Degree-bounded distinct samples identify the actual Boolean with full residual zero.
The sample list is supplied and certified; this executes no enumeration or prefix-degree test. -/
theorem zero_runFuel_iff_residual_zero
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (cs : List F) (terms : List (EvaluationMachine.Term F)) (samples : List F)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (points : Fin L ↪ F) (hpoints : samples = List.ofFn (fun i ↦ points i))
    (hdegree : P.natDegree ≤ D) (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨cs, terms, center, r⟩
    ∃ b, runFuel input (fuel input samples.length) (.start samples) =
      (.done b, cost input samples) ∧
      (b = true ↔ effectiveResidual Q center P = 0) := by
  dsimp only
  refine ⟨result ⟨cs, terms, center, r⟩ samples, zero_runFuel _ _, ?_⟩
  rw [result_eq_true_iff, effectiveResidual_eq_zero_iff_samples Q center P hdegree hweight points]
  simp only [hpoints, List.mem_ofFn, forall_exists_index]
  constructor
  · intro h i
    have hi := h (points i) i rfl
    rw [ResidualBatchMachine.sampleValue_eq_effectiveResidual Q center (points i) P cs terms hP hQ,
      eval_effectiveResidual_eq_jet] at hi
    exact hi
  · intro h u i hi
    subst u
    rw [ResidualBatchMachine.sampleValue_eq_effectiveResidual Q center (points i) P cs terms hP hQ,
      eval_effectiveResidual_eq_jet]
    exact h i

end Concrete

end ReedSolomon.HiddenDerivative.ResidualZeroMachine
