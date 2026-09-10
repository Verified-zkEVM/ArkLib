/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualBatchMachine
public import ArkLib.Data.Matrix.VandermondeMachine
public import ArkLib.Data.Matrix.ForwardEchelonMachine
/-!
# From residual samples to materialized echelon equations

The machine executes a residual batch, constructs its augmented Vandermonde rows, and reduces
those rows to forward-echelon form. Each suspended callee advances by one actual transition.
The returned lists pass directly to the next stage; no map, zip, matrix conversion, or abstract
solver is executed at a handoff. All callee charges and emissions remain counted, with additional
wrapper dispatch, root access, and final output charges.

The input consists of materialized polynomial data, points, and a supplied column count. The
output consists of indexed pivots and residual rows, not a solved coefficient vector. Input
preparation, point enumeration, back-substitution, scalar bit costs, and interpreter bookkeeping
are separate obligations. The semantic row specifications are used only in proofs.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualSystemMachine

open Polynomial Matrix

abbrev Input := ResidualBatchMachine.Input
abbrev Cost := PivotEliminationMachine.Cost
abbrev Pivot := ForwardEchelonMachine.Pivot
abbrev Row := PivotSelectionMachine.Row
abbrev totalCost := PivotSelectionMachine.totalCost

/-- Embed every sampling charge into the larger linear-algebra cost vector. -/
def samplingCost (c : JetHornerMachine.Cost) : Cost :=
  ⟨⟨c.additions, c.multiplications, c.control, c.data, c.output⟩, 0, 0, 0, c.natural⟩

@[simp] theorem samplingCost_zero : samplingCost 0 = 0 := rfl
@[simp] theorem samplingCost_add (c d : JetHornerMachine.Cost) :
    samplingCost (c + d) = samplingCost c + samplingCost d := rfl

/-- One outer dispatch and two suspended-state root accesses per callee transition. -/
def wrapperCost (n : ℕ) : Cost := ⟨⟨0, 0, n, 2 * n, 0⟩, 0, 0, 0, 0⟩
/-- Read the immutable input and point roots and initialize the batch state. -/
def startCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩
/-- Read the emitted pairs and column count and initialize matrix construction. -/
def sampleReturnCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩
/-- Read rows and width and initialize the column, remaining width, and empty pivot accumulator. -/
def matrixReturnCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
/-- Read the two output roots and emit the outer tagged result. -/
def returnCost : Cost := ⟨⟨0, 0, 1, 3, 1⟩, 0, 0, 0, 0⟩

/-- The caller stores actual suspended configurations, not extensional callee functions. -/
inductive Configuration (F : Type*) where
  | start (points : List F)
  | sample (state : ResidualBatchMachine.Configuration F)
  | matrix (state : VandermondeMachine.Configuration F)
  | echelon (state : ForwardEchelonMachine.Configuration F)
  | done (pivots : List (Pivot F)) (rest : List (Row F))
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent rules account for every delegated transition and every data handoff. -/
inductive Step (input : Input F) (L : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | start {ps} : Step input L (.start ps) startCost (.sample (.start ps))
  | sample {s t c} (h : ResidualBatchMachine.Step input s c t) :
      Step input L (.sample s) (samplingCost c + wrapperCost 1) (.sample t)
  | samples {ps} : Step input L (.sample (.done ps)) sampleReturnCost (.matrix (.start ps))
  | matrix {s t c} (h : VandermondeMachine.Step L s c t) :
      Step input L (.matrix s) (c + wrapperCost 1) (.matrix t)
  | rows {rs} : Step input L (.matrix (.done rs)) matrixReturnCost (.echelon (.loop 0 L rs []))
  | echelon {s t c} (h : ForwardEchelonMachine.Step s c t) :
      Step input L (.echelon s) (c + wrapperCost 1) (.echelon t)
  | done {ps rs} : Step input L (.echelon (.done ps rs)) returnCost (.done ps rs)
  | reject : Step input L (.echelon .rejected) returnCost .rejected

/-- Closed dispatch delegates one transition at a time, with no whole-callee execution primitive. -/
def step (input : Input F) (L : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start ps => some (.sample (.start ps), startCost)
  | .sample s => match ResidualBatchMachine.step input s with
      | some (t, c) => some (.sample t, samplingCost c + wrapperCost 1)
      | none => match s with
          | .done ps => some (.matrix (.start ps), sampleReturnCost)
          | _ => none
  | .matrix s => match VandermondeMachine.step L s with
      | some (t, c) => some (.matrix t, c + wrapperCost 1)
      | none => match s with
          | .done rs => some (.echelon (.loop 0 L rs []), matrixReturnCost)
          | _ => none
  | .echelon s => match ForwardEchelonMachine.step s with
      | some (t, c) => some (.echelon t, c + wrapperCost 1)
      | none => match s with
          | .done ps rs => some (.done ps rs, returnCost)
          | .rejected => some (.rejected, returnCost)
          | _ => none
  | .done _ _ | .rejected => none

/-- Every operational rule executes with its stated cost. -/
theorem Step.step_eq {input : Input F} {L : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step input L s c t) : step input L s = some (t, c) := by
  cases h with
  | sample h => simp [step, h.step_eq]
  | matrix h => simp [step, h.step_eq]
  | echelon h => simp [step, h.step_eq]
  | _ => rfl

/-- No executable branch escapes the independent rules. -/
theorem step_sound {input : Input F} {L : ℕ} {s t : Configuration F} {c : Cost}
    (h : step input L s = some (t, c)) : Step input L s c t := by
  cases s with
  | start ps => cases h; constructor
  | done ps rs => simp [step] at h
  | rejected => simp [step] at h
  | sample s =>
      cases hs : ResidualBatchMachine.step input s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.sample (ResidualBatchMachine.step_sound hs)
      | none =>
          cases s with
          | done ps => cases h; exact Step.samples
          | _ => simp [step, hs] at h
  | matrix s =>
      cases hs : VandermondeMachine.step L s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.matrix (VandermondeMachine.step_sound hs)
      | none =>
          cases s with
          | done rs => cases h; exact Step.rows
          | _ => simp [step, hs] at h
  | echelon s =>
      cases hs : ForwardEchelonMachine.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.echelon (ForwardEchelonMachine.step_sound hs)
      | none =>
          cases s with
          | done ps rs => cases h; exact Step.done
          | rejected => cases h; exact Step.reject
          | _ => simp [step, hs] at h

/-- A finite execution with all primitive charges accumulated. -/
inductive Trace (input : Input F) (L : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input L 0 s 0 s
  | cons {n s u t c d} (head : Step input L s c u) (tail : Trace input L n u d t) :
      Trace input L (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

omit [DecidableEq F] in
/-- Concatenating stages preserves the full cost, including internal outputs. -/
theorem Trace.trans {input : Input F} {L n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace input L n s c u) (h' : Trace input L m u d t) :
    Trace input L (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel bounds dispatch iterations, exposing partial states when exhausted. -/
def runFuel (input : Input F) (L : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input L s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input L n t; (result.1, c + result.2)

/-- The interpreter always has a trace with exactly its observed accumulated cost. -/
theorem runFuel_refines (input : Input F) (L fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input L n s (runFuel input L fuel s).2 (runFuel input L fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input L s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

private theorem Trace.runFuel_add {input : Input F} {L n : ℕ}
    {s t : Configuration F} {c : Cost} (h : Trace input L n s c t) (extra : ℕ) :
    runFuel input L (n + extra) s =
      ((runFuel input L extra t).1, c + (runFuel input L extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [cost_assoc]

/-- Additional fuel leaves a completed result and its charges unchanged. -/
theorem Trace.runFuel_done {input : Input F} {L n : ℕ} {s : Configuration F} {c : Cost}
    {ps : List (Pivot F)} {rs : List (Row F)}
    (h : Trace input L n s c (.done ps rs)) (extra : ℕ) :
    runFuel input L (n + extra) s = (.done ps rs, c) := by
  have hd : runFuel input L extra (.done ps rs) = (.done ps rs, (0 : Cost)) := by
    cases extra <;> rfl
  rw [h.runFuel_add, hd]
  simp

omit [DecidableEq F] in
/-- Each sample transition is delegated with all cost components and one wrapper dispatch. -/
theorem lift_samples (input : Input F) (L : ℕ) {n : ℕ}
    {s t : ResidualBatchMachine.Configuration F} {c : JetHornerMachine.Cost}
    (h : ResidualBatchMachine.Trace input n s c t) :
    Trace input L n (.sample s) (samplingCost c + wrapperCost n) (.sample t) := by
  induction h with
  | nil s => simpa [samplingCost, wrapperCost] using
      Trace.nil (input := input) (L := L) (.sample s)
  | @cons n s u t c d head tail ih =>
      have hc : (samplingCost c + wrapperCost 1) + (samplingCost d + wrapperCost n) =
          samplingCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [samplingCost, wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.sample head) ih

omit [DecidableEq F] in
/-- Matrix construction retains every arithmetic, allocation, reversal and output charge. -/
theorem lift_matrix (input : Input F) (L : ℕ) {n : ℕ}
    {s t : VandermondeMachine.Configuration F} {c : Cost}
    (h : VandermondeMachine.Trace L n s c t) :
    Trace input L n (.matrix s) (c + wrapperCost n) (.matrix t) := by
  induction h with
  | nil s => simpa [wrapperCost] using Trace.nil (input := input) (L := L) (.matrix s)
  | @cons n s u t c d head tail ih =>
      have hc : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.matrix head) ih

omit [DecidableEq F] in
/-- Elimination remains the actual closed echelon machine, including its nested callees. -/
theorem lift_echelon (input : Input F) (L : ℕ) {n : ℕ}
    {s t : ForwardEchelonMachine.Configuration F} {c : Cost}
    (h : ForwardEchelonMachine.Trace n s c t) :
    Trace input L n (.echelon s) (c + wrapperCost n) (.echelon t) := by
  induction h with
  | nil s => simpa [wrapperCost] using Trace.nil (input := input) (L := L) (.echelon s)
  | @cons n s u t c d head tail ih =>
      have hc : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.echelon head) ih

/-- A host-fuel bound formed from all three callee bounds and four administrative transitions. -/
def fuel (input : Input F) (L n : ℕ) : ℕ :=
  ResidualBatchMachine.fuel input n + VandermondeMachine.constructionFuel L n +
    ForwardEchelonMachine.budget n L + 4

/-- A primitive-work bound preserving sample work, matrix work, and every delegated dispatch. -/
def workBound (input : Input F) (L n : ℕ) : ℕ :=
  (ResidualBatchMachine.cost input n).total + 72 * (n + 1) * (L + 1) +
    4 * ForwardEchelonMachine.budget n L +
    3 * (ResidualBatchMachine.fuel input n + VandermondeMachine.constructionFuel L n) + 19

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, PivotSelectionMachine.totalCost, PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add]
  omega

private theorem total_sampling (c : JetHornerMachine.Cost) :
    totalCost (samplingCost c) = c.total := by
  simp only [totalCost, PivotSelectionMachine.totalCost, samplingCost, JetHornerMachine.Cost.total]
  omega

private theorem total_wrapper (n : ℕ) : totalCost (wrapperCost n) = 3 * n := by
  simp [totalCost, PivotSelectionMachine.totalCost, wrapperCost]
  omega

omit [DecidableEq F] in
/-- Complete execution gives echelon equations equivalent to the sampled Vandermonde system.
The number of rows is preserved, including zero-coefficient rows with nonzero RHS. -/
theorem computation_trace (input : Input F) (L : ℕ) (points : List F) :
    ∃ ps rest steps c, Trace input L steps (.start points) c (.done ps rest) ∧
      ForwardEchelonMachine.Echelon L 0 ps rest ∧ ps.length + rest.length = points.length ∧
      (∀ x, ForwardEchelonMachine.Solutions ps rest x ↔
        PivotSelectionMachine.Satisfies
          (VandermondeMachine.rowsSpec L (ResidualBatchMachine.outputSpec input points)) x) ∧
      steps ≤ fuel input L points.length ∧ totalCost c ≤ workBound input L points.length := by
  classical
  let samples := ResidualBatchMachine.outputSpec input points
  let rows := VandermondeMachine.rowsSpec L samples
  have hslen : samples.length = points.length := by simp [samples, ResidualBatchMachine.outputSpec]
  have hrlen : rows.length = points.length := by
    simp [rows, VandermondeMachine.rowsSpec_length, hslen]
  obtain ⟨ns, hns, hs⟩ := ResidualBatchMachine.runFuel_refines input
    (ResidualBatchMachine.fuel input points.length) (.start points)
  rw [ResidualBatchMachine.batch_runFuel] at hs
  obtain ⟨cm, hm, hcm⟩ := VandermondeMachine.construction_runFuel L samples
  obtain ⟨nm, hnm, ht⟩ := VandermondeMachine.runFuel_refines L
    (VandermondeMachine.constructionFuel L samples.length) (.start samples)
  rw [hm] at ht
  obtain ⟨ps, rest, ce, he, hinv, hcount, hsol, hce⟩ :=
    ForwardEchelonMachine.evaluation_runFuel L rows
      (VandermondeMachine.rowsSpec_rectangular L samples)
  obtain ⟨ne, hne, het⟩ := ForwardEchelonMachine.runFuel_refines
    (ForwardEchelonMachine.budget rows.length L) (.loop 0 L rows [])
  rw [he] at het
  have h := Trace.cons Step.start ((lift_samples input L hs).trans
    (Trace.cons Step.samples ((lift_matrix input L ht).trans
      (Trace.cons Step.rows ((lift_echelon input L het).trans
        (Trace.cons Step.done (Trace.nil _)))))))
  refine ⟨ps, rest, _, _, h, hinv, hcount.trans hrlen, hsol, ?_, ?_⟩
  · simp only [fuel]
    rw [hslen] at hnm
    rw [hrlen] at hne
    omega
  · simp only [total_add, total_sampling, total_wrapper]
    change 4 + ((ResidualBatchMachine.cost input points.length).total + 3 * ns +
      (4 + (totalCost cm + 3 * nm + (6 + (totalCost ce + 3 * ne + (5 + 0)))))) ≤ _
    rw [hslen] at hnm hcm
    rw [hrlen] at hne hce
    change totalCost cm ≤ 72 * (points.length + 1) * (L + 1) at hcm
    change totalCost ce ≤ ForwardEchelonMachine.budget points.length L at hce
    unfold workBound
    omega

/-- The actual interpreter returns solution-equivalent echelon equations within the proved cost. -/
theorem computation_runFuel (input : Input F) (L : ℕ) (points : List F) :
    ∃ ps rest c, runFuel input L (fuel input L points.length) (.start points) =
      (.done ps rest, c) ∧ ForwardEchelonMachine.Echelon L 0 ps rest ∧
      ps.length + rest.length = points.length ∧
      (∀ x, ForwardEchelonMachine.Solutions ps rest x ↔
        PivotSelectionMachine.Satisfies
          (VandermondeMachine.rowsSpec L (ResidualBatchMachine.outputSpec input points)) x) ∧
      totalCost c ≤ workBound input L points.length := by
  obtain ⟨ps, rest, steps, c, ht, hi, hn, hs, hf, hc⟩ := computation_trace input L points
  have h := ht.runFuel_done (fuel input L points.length - steps)
  rw [Nat.add_sub_of_le hf] at h
  exact ⟨ps, rest, c, h, hi, hn, hs, hc⟩

end ReedSolomon.HiddenDerivative.ResidualSystemMachine
