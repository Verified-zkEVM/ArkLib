/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.StagesMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.CentersRefinement
public import ArkLib.Data.MvPolynomial.CoordinateChainRefinement
/-!
# Same-execution coordinate stage records

All original equations, selected indices, previous-equation order, separants, centers and complete
coefficient lists remain in the emitted records. The constant factor bounds the entire source
execution, including all invalid-stage and child failure paths, without compounding by stages.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticStageRootsMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)
open MvPolynomial.QuadraticNormalizeMachine (mapTerms)
open MvPolynomial.QuadraticChainMachine (mapStage mapStages)

/-- Preserve the order of the retained previous-equation list. -/
def mapEquations {K J : Type*} (f : K → J)
    (ps : List (List (MvPolynomial.EvaluationMachine.Term K))) :=
  ps.map (mapTerms f)
/-- Preserve the entire immutable stage context. -/
def mapContext {K J : Type*} (f : K → J) (c : StageRootsMachine.Context K) :
    StageRootsMachine.Context J :=
  ⟨mapStage f c.stage, mapEquations f c.previous, mapTerms f c.separant⟩
/-- Preserve context, center and complete global coefficient vector. -/
def mapRecord {K J : Type*} (f : K → J) (r : StageRootsMachine.Record K) :
    StageRootsMachine.Record J := ⟨mapContext f r.context, f r.center, r.coefficients.map f⟩
/-- Preserve emitted order and duplicates. -/
def mapRecords {K J : Type*} (f : K → J) (rs : List (StageRootsMachine.Record K)) :=
  rs.map (mapRecord f)
/-- Represent all supplied stage-driver inputs without executing a conversion. -/
def mapInput {K J : Type*} (f : K → J) (input : StageRootsMachine.Input K) :
    StageRootsMachine.Input J := ⟨input.alphabet.map f, mapTerms f input.terms, input.order⟩

/-- Preserve all contexts, source cursors and retained coordinate child input records. -/
def represent {K F : Type*} [One K] (a : F) (f : K → Pair F)
    (input : StageRootsMachine.Input K) (D : ℕ) :
    StageRootsMachine.Configuration K → Configuration F
  | .start xs => .start (xs.map f)
  | .chain xs s => .chain (xs.map f) (MvPolynomial.QuadraticChainMachine.represent f s)
  | .scan ss pre out xs => .scan (mapStages f ss) (mapEquations f pre) (mapRecords f out) (xs.map f)
  | .select stage ss pre nextPre out xs => .select (mapStage f stage) (mapStages f ss)
      (mapEquations f pre) (mapEquations f nextPre) (mapRecords f out) (xs.map f)
  | .roots ctx r ss pre out xs s => .roots (mapContext f ctx) r (mapStages f ss)
      (mapEquations f pre) (mapRecords f out) (xs.map f)
      (QuadraticCenterRootsMachine.mapInput f (StageRootsMachine.centerInput input ctx.stage r))
      (QuadraticCenterRootsMachine.represent a f
        (StageRootsMachine.centerInput input ctx.stage r) D s)
  | .collect ctx cs ss pre out xs => .collect (mapContext f ctx)
      (QuadraticCenterRootsMachine.mapRecords f cs) (mapStages f ss)
      (mapEquations f pre) (mapRecords f out) (xs.map f)
  | .save rec ctx cs ss pre out xs => .save (mapRecord f rec) (mapContext f ctx)
      (QuadraticCenterRootsMachine.mapRecords f cs) (mapStages f ss)
      (mapEquations f pre) (mapRecords f out) (xs.map f)
  | .reverse rs out => .reverse (mapRecords f rs) (mapRecords f out)
  | .emit out => .emit (out.map (mapRecords f))
  | .done out => .done (out.map (mapRecords f))

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Raw stage inputs survive their coordinate round trip. -/
theorem encode_decode_input (a : F) (input : Input F) :
    mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input := by
  cases input
  simp [mapInput, mapTerms, MvPolynomial.QuadraticNormalizeMachine.mapTerm,
    List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

/-- Every actual chain instruction keeps its full ledger plus the outer wrapper. -/
theorem chain_trace {a : F} {input : Input F} {D L n : ℕ} (xs : List (Pair F))
    {s t : MvPolynomial.QuadraticChainMachine.Configuration F} {c : Cost}
    (h : MvPolynomial.QuadraticChainMachine.Trace a n s c t) :
    ∃ d, Trace a input D L n (.chain xs s) d (.chain xs t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Each center-loop instruction retains its prepared input and complete nested charge. -/
theorem roots_trace {a : F} {input : Input F} {payload : QuadraticCenterRootsMachine.Input F}
    {D L n : ℕ} (ctx : Context F) (r : ℕ) (ss : List (Stage F))
    (pre : List (List (Term F))) (out : List (Record F)) (xs : List (Pair F))
    {s t : QuadraticCenterRootsMachine.Configuration F} {c : Cost}
    (h : QuadraticCenterRootsMachine.Trace a payload D L n s c t) :
    ∃ d, Trace a input D L n (.roots ctx r ss pre out xs payload s) d
      (.roots ctx r ss pre out xs payload t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- A single absolute constant covers all original stage-generation edges. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (input : StageRootsMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : StageRootsMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : StageRootsMachine.Cost}, StageRootsMachine.Step input D L s c t →
      ∃ n d, Trace a (mapInput encode input) D L n (represent a encode input D s) d
        (represent a encode input D t) ∧ n + d.total ≤ 4294967296 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | start => exact ⟨1, charge 3 0 0 + allocation 4, single rfl, by decide⟩
  | chain h =>
      obtain ⟨n, c, hc, hb⟩ := MvPolynomial.QuadraticChainMachine.dispatch_lowering h
      obtain ⟨d, hd, he⟩ := chain_trace (input := mapInput encode input) (D := D) (L := L) _ hc
      exact ⟨n, d, hd, by omega⟩
  | chained => exact ⟨1, charge 4 0 0, single rfl, by decide⟩
  | next => exact ⟨1, charge 8 0 0, single rfl, by decide⟩
  | terminal h => exact ⟨1, charge 3 0 0,
      single (by simp [step, represent, mapStage, h]), by decide⟩
  | invalid h => exact ⟨1, charge 3 1 0,
      single (by simp [step, represent, mapStage, h]), by decide⟩
  | missing h => exact ⟨1, charge 4 2 0,
      single (by simp [step, represent, mapStage, mapStages, h]), by decide⟩
  | active h => exact ⟨1, charge 12 2 0 + allocation 3,
      single (by simp [step, represent, mapStage, mapStages, mapContext, mapInput,
        mapEquations, mapTerms, h, QuadraticCenterRootsMachine.mapInput,
        StageRootsMachine.centerInput, MvPolynomial.QuadraticNormalizeMachine.mapTerm,
        QuadraticCenterRootsMachine.represent]), by decide⟩
  | roots h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticCenterRootsMachine.step_lowering a ha _ D L h
      obtain ⟨d, hd, he⟩ := roots_trace (input := mapInput encode input) _ _ _ _ _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | returned => exact ⟨1, charge 5 0 0, single rfl, by decide⟩
  | failed => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | record => exact ⟨1, charge 8 0 0, single rfl, by decide⟩
  | save => exact ⟨1, charge 6 0 0, single rfl, by decide⟩
  | collected => exact ⟨1, charge 3 0 0, single rfl, by decide⟩
  | scanned => exact ⟨1, charge 2 0 0, single rfl, by decide⟩
  | reverse => exact ⟨1, charge 5 0 0, single rfl, by decide⟩
  | reversed => exact ⟨1, charge 2 0 0 + allocation 1, single rfl, by decide⟩
  | emit => exact ⟨1, charge 2 0 1, single rfl, by decide⟩

/-- Compose the fixed factor over total source steps, with no per-iteration exponentiation. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (input : StageRootsMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : StageRootsMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : StageRootsMachine.Cost}, StageRootsMachine.Trace input D L n s c t →
      ∃ steps d, Trace a (mapInput encode input) D L steps (represent a encode input D s) d
        (represent a encode input D t) ∧ steps + d.total ≤ 4294967296 * n := by
  let := fieldOfNonsquare a ha
  intro n s t c h
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering a ha input D L head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- A finite source run reaches the identical represented candidate or failure. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a)
    (input : StageRootsMachine.Input (QuadraticAlgebra F a 0)) (D L fuel : ℕ)
    (s : StageRootsMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ steps d, runFuel a (mapInput encode input) D L steps (represent a encode input D s) =
      (represent a encode input D (StageRootsMachine.runFuel input D L fuel s).1, d) ∧
      steps + d.total ≤ 4294967296 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := StageRootsMachine.runFuel_refines input D L fuel s
  obtain ⟨steps, d, hd, hb⟩ := trace_lowering a ha input D L ht
  exact ⟨steps, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Completed source execution transfers directly to already materialized coordinate inputs. -/
theorem start_run_lowering (a : F) (ha : ¬IsSquare a) (input : Input F) (D L fuel : ℕ)
    (samples : List (Pair F))
    (out : Option (List (StageRootsMachine.Record (QuadraticAlgebra F a 0))))
    (sourceCost : StageRootsMachine.Cost) :
    letI := fieldOfNonsquare a ha
    StageRootsMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L fuel
      (.start (samples.map (ArithmeticMachine.decode a))) = (.done out, sourceCost) →
    ∃ steps c, runFuel a input D L steps (.start samples) =
      (.done (out.map (mapRecords encode)), c) ∧ steps + c.total ≤ 4294967296 * fuel := by
  let := fieldOfNonsquare a ha
  intro hs
  obtain ⟨steps, c, hr, hb⟩ := run_lowering a ha (mapInput (ArithmeticMachine.decode a) input)
    D L fuel (.start (samples.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hi := encode_decode_input a input
  change mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input at hi
  rw [hi] at hr
  have hp : (samples.map (ArithmeticMachine.decode a)).map encode = samples := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨steps, c, ?_, hb⟩
  simpa only [represent, hp] using hr

end ReedSolomon.HiddenDerivative.QuadraticStageRootsMachine
