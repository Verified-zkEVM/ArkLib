/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.RootMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.LiftRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ZeroRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ShiftRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.RegularRootSemantics
/-!
# Same-execution accepted coordinate candidate

The whole lift, residual filter and translation lower to the same emitted option. Every child
instruction and retained payload is charged with a factor independent of degree and stage count.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticRegularRootMachine

open Polynomial QuadraticAlgebra CompPoly PolynomialDifferential
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

abbrev mapInput := @QuadraticResidualBatch.mapInput

/-- Preserve samples, candidate coefficients, every child state and all failure tags. -/
def represent {K F : Type*} [One K] (a : F) (f : K → Pair F)
    (input : RegularRootMachine.Input K) (D : ℕ) :
    RegularRootMachine.Configuration K → Configuration F
  | .start xs => .start (xs.map f)
  | .lift xs s => .lift (xs.map f) (mapInput f input)
      (QuadraticRegularLiftMachine.represent a f input s)
  | .check cs s => .check (mapInput f (RegularRootMachine.withCoefficients input cs))
      (QuadraticResidualZeroMachine.represent f (RegularRootMachine.withCoefficients input cs) s)
  | .shift cs s => .shift ⟨cs.map f, f input.center, D⟩
      (QuadraticCenterShiftMachine.represent f s)
  | .emit out => .emit (out.map (List.map f))
  | .done out => .done (out.map (List.map f))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Every lift child instruction preserves its full ledger and outer wrapper. -/
theorem lift_trace {a : F} {input : Input F} {payload : Input F} {D L n : ℕ}
    (xs : List (Pair F))
    {s t : QuadraticRegularLiftMachine.Configuration F} {c : Cost}
    (h : QuadraticRegularLiftMachine.Trace a payload D L n s c t) :
    ∃ d, Trace a input D L n (.lift xs payload s) d (.lift xs payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Every check child instruction preserves its full ledger and outer wrapper. -/
theorem check_trace {a : F} {input : Input F} {payload : Input F} {D L n : ℕ}
    {s t : QuadraticResidualZeroMachine.Configuration F} {c : Cost}
    (h : QuadraticResidualZeroMachine.Trace a payload n s c t) :
    ∃ d, Trace a input D L n (.check payload s) d (.check payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Every shift child instruction preserves its full ledger and outer wrapper. -/
theorem shift_trace {a : F} {input : Input F} {payload : QuadraticCenterShiftMachine.Input F}
    {D L n : ℕ}
    {s t : QuadraticCenterShiftMachine.Configuration F} {c : Cost}
    (h : QuadraticCenterShiftMachine.Trace a payload n s c t) :
    ∃ d, Trace a input D L n (.shift payload s) d (.shift payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- One fixed factor covers all source edges, including rejection and translation failure. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (input : RegularRootMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : RegularRootMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : RegularRootMachine.Cost}, RegularRootMachine.Step input D L s c t →
      ∃ n d, Trace a (mapInput encode input) D L n (represent a encode input D s) d
        (represent a encode input D t) ∧ n + d.total ≤ 67108864 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | start => exact ⟨1, administrative RegularRootMachine.startCost + allocation 4,
      single rfl, by decide⟩
  | lift h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticRegularLiftMachine.step_lowering a ha input D L h
      obtain ⟨d, hd, he⟩ := lift_trace (input := mapInput encode input) _ hc
      exact ⟨n, d, hd, by omega⟩
  | liftReturn => exact ⟨1, administrative RegularRootMachine.liftReturnCost + allocation 4,
      single rfl, by decide⟩
  | liftReject => exact ⟨1, administrative RegularRootMachine.returnCost, single rfl, by decide⟩
  | check h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticResidualZeroMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := check_trace (input := mapInput encode input) (D := D) (L := L) hc
      exact ⟨n, d, hd, by omega⟩
  | accepted => exact ⟨1, administrative RegularRootMachine.zeroReturnCost + allocation 3,
      single rfl, by decide⟩
  | rejected => exact ⟨1, administrative RegularRootMachine.zeroReturnCost, single rfl, by decide⟩
  | shift h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticCenterShiftMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := shift_trace (input := mapInput encode input) (D := D) (L := L) hc
      exact ⟨n, d, hd, by omega⟩
  | shifted => exact ⟨1, administrative RegularRootMachine.returnCost, single rfl, by decide⟩
  | emit => exact ⟨1, administrative RegularRootMachine.emitCost, single rfl, by decide⟩

/-- Compose the fixed factor over total source steps, with no per-iteration exponentiation. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (input : RegularRootMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : RegularRootMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : RegularRootMachine.Cost}, RegularRootMachine.Trace input D L n s c t →
      ∃ steps d, Trace a (mapInput encode input) D L steps (represent a encode input D s) d
        (represent a encode input D t) ∧ steps + d.total ≤ 67108864 * n := by
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
    (input : RegularRootMachine.Input (QuadraticAlgebra F a 0)) (D L fuel : ℕ)
    (s : RegularRootMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ steps d, runFuel a (mapInput encode input) D L steps (represent a encode input D s) =
      (represent a encode input D (RegularRootMachine.runFuel input D L fuel s).1, d) ∧
      steps + d.total ≤ 67108864 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := RegularRootMachine.runFuel_refines input D L fuel s
  obtain ⟨steps, d, hd, hb⟩ := trace_lowering a ha input D L ht
  exact ⟨steps, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Completed source execution transfers directly to already materialized coordinate inputs. -/
theorem start_run_lowering (a : F) (ha : ¬IsSquare a) (input : Input F) (D L fuel : ℕ)
    (samples : List (Pair F)) (out : Option (List (QuadraticAlgebra F a 0)))
    (sourceCost : RegularRootMachine.Cost) :
    letI := fieldOfNonsquare a ha
    RegularRootMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L fuel
      (.start (samples.map (ArithmeticMachine.decode a))) = (.done out, sourceCost) →
    ∃ steps c, runFuel a input D L steps (.start samples) =
      (.done (out.map (List.map encode)), c) ∧ steps + c.total ≤ 67108864 * fuel := by
  let := fieldOfNonsquare a ha
  intro hs
  obtain ⟨steps, c, hr, hb⟩ := run_lowering a ha (mapInput (ArithmeticMachine.decode a) input)
    D L fuel (.start (samples.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hi := QuadraticResidualBatch.encode_decode_input a input
  change mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input at hi
  rw [hi] at hr
  have hp : (samples.map (ArithmeticMachine.decode a)).map encode = samples := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨steps, c, ?_, hb⟩
  simpa only [represent, hp] using hr

/-- The same run implements the full lift/filter/translation option with physical width. -/
theorem computation_correct (a : F) (ha : ¬IsSquare a) (input : Input F) (D L : ℕ)
    (samples : List (Pair F))
    (Q : CPoly.CMvPolynomial (input.order + 2) (QuadraticAlgebra F a 0))
    (jet : Fin (input.order + 1) → QuadraticAlgebra F a 0) (points : Fin L ↪ QuadraticAlgebra F a 0)
    (hsamples : samples.map (ArithmeticMachine.decode a) = List.ofFn (fun i => points i))
    (hwidth : input.coefficients.length = D + 1)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial
      (mapInput (ArithmeticMachine.decode a) input).terms =
        MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : input.order ≤ D) (hlookup : D - input.order < L) :
    letI := fieldOfNonsquare a ha
    JetHornerMachine.coefficientPolynomial (input.coefficients.map (ArithmeticMachine.decode a)) =
      (effectiveInitialPrefix jet).toPoly →
    differentialWeightedDegree D (semanticEquation Q) < L →
    ∃ steps c out, runFuel a input D L steps (.start samples) = (.done out, c) ∧
      out.map (fun xs => JetHornerMachine.coefficientPolynomial
        (xs.map (ArithmeticMachine.decode a))) =
          (directRegularSolution Q (ArithmeticMachine.decode a input.center) jet D).map
            (unshift (ArithmeticMachine.decode a input.center)) ∧
      (∀ xs, out = some xs → xs.length = D + 1) ∧
      steps + c.total ≤ 67108864 * RegularRootMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) D L samples.length := by
  let := fieldOfNonsquare a ha
  intro hP hweight
  obtain ⟨out, sourceCost, hs, hspec, hlen, _⟩ := RegularRootMachine.computation_runFuel_correct Q
    (ArithmeticMachine.decode a input.center) jet
    (input.coefficients.map (ArithmeticMachine.decode a))
    (mapInput (ArithmeticMachine.decode a) input).terms points
    (samples.map (ArithmeticMachine.decode a)) hsamples (by simpa using hwidth)
    hP hQ hr hlookup hweight
  change RegularRootMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L
    (RegularRootMachine.fuel (mapInput (ArithmeticMachine.decode a) input) D L
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a))) = (.done out, sourceCost) at hs
  obtain ⟨steps, c, ht, hb⟩ := start_run_lowering a ha input D L _ samples out sourceCost hs
  refine ⟨steps, c, out.map (List.map encode), ht, ?_, ?_, ?_⟩
  · simpa [Option.map_map, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
      using hspec
  · intro xs hxs
    obtain ⟨ys, hy, rfl⟩ := Option.map_eq_some_iff.mp hxs
    simpa using hlen ys hy
  · simpa only [List.length_map] using hb

end ReedSolomon.HiddenDerivative.QuadraticRegularRootMachine
