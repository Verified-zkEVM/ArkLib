/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.GuardMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ZeroRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.WitnessRefinement
/-!
# Same-execution coordinate canonical guard

Each original guard edge lowers to actual residual and equality programs with one absolute
factor. The final Boolean is exactly the source guard's result, including all early exits.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticCanonicalGuardMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode delegated)

/-- Proof-only sparse-equation coefficient representation. -/
def mapEquation {K J : Type*} (f : K → J) (ts : CanonicalGuardMachine.Equation K) :
    CanonicalGuardMachine.Equation J := ts.map (fun t ↦ (f t.1, t.2))

def mapPrevious {K J : Type*} (f : K → J) (ps : List (CanonicalGuardMachine.Equation K)) :
    List (CanonicalGuardMachine.Equation J) := ps.map (mapEquation f)

/-- Proof-only representation of the five immutable outer input roots. -/
def mapInput {K J : Type*} (f : K → J) (input : CanonicalGuardMachine.Input K) :
    CanonicalGuardMachine.Input J :=
  ⟨input.coefficients.map f, input.samples.map f, input.order, f input.center,
    mapEquation f input.separant⟩

/-- Retain exactly the residual record built by each represented source launch. -/
def represent {K F : Type*} [Zero K] (f : K → Pair F) (input : CanonicalGuardMachine.Input K) :
    CanonicalGuardMachine.Configuration K → Configuration F
  | .start ps => .start (mapPrevious f ps)
  | .scan ps => .scan (mapPrevious f ps)
  | .zero q ps s =>
      .zero (QuadraticResidualBatch.mapInput f (CanonicalGuardMachine.residualInput input q))
        (mapPrevious f ps)
        (QuadraticResidualZeroMachine.represent f (CanonicalGuardMachine.residualInput input q) s)
  | .witness s => .witness
      (QuadraticResidualBatch.mapInput f (CanonicalGuardMachine.residualInput input input.separant))
      (QuadraticResidualWitnessMachine.represent f
        (CanonicalGuardMachine.residualInput input input.separant) s)
  | .emit b => .emit b
  | .done b => .done b

variable {F : Type*} [Field F] [DecidableEq F]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Preserve every zero-child instruction and its explicit outer wrapper. -/
theorem zero_trace {a : F} {input : Input F} {payload : QuadraticResidualBatch.Input F}
    (ps : List (Equation F)) {n : ℕ} {s t : QuadraticResidualZeroMachine.Configuration F}
    {c : Cost} (h : QuadraticResidualZeroMachine.Trace a payload n s c t) :
    ∃ d, Trace a input n (.zero payload ps s) d (.zero payload ps t) ∧
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

/-- Preserve the ordered witness child's actual instructions and retained payload. -/
theorem witness_trace {a : F} {input : Input F} {payload : QuadraticResidualBatch.Input F}
    {n : ℕ} {s t : QuadraticResidualWitnessMachine.Configuration F}
    {c : Cost} (h : QuadraticResidualWitnessMachine.Trace a payload n s c t) :
    ∃ d, Trace a input n (.witness payload s) d (.witness payload t) ∧
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

/-- The selected-center comparison executes its concrete retained-input arithmetic program. -/
theorem arithmetic_trace {a : F} {input : Input F} {payload : ArithmeticMachine.Input F}
    {n : ℕ} {s t : ArithmeticMachine.Configuration F} {c : ArithmeticMachine.Cost}
    (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a input n (.compare payload s) d (.compare payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨delegated c + d, .cons ?_ hd, ?_⟩
      · simp only [step, head.step_eq]
      · rw [total_add, delegated_total, he, base_total_add]
        omega

/-- An actual selected witness is compared in both coordinates before Boolean emission. -/
theorem selected_lowering (a : F) (input : Input F) (payload : QuadraticResidualBatch.Input F)
    (u : Pair F) (b : Bool)
    (hb : ArithmeticMachine.specification ⟨a, u, input.center⟩ .equal = .boolean b) :
    ∃ n c, Trace a input n (.witness payload (.done (some u))) c (.emit b) ∧
      n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace ⟨a, u, input.center⟩ .equal
  rw [hb] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (input := input) ht
  refine ⟨n + 1 + 1, compareLaunch + (c + returnCost),
    .cons rfl (hc.trans (single rfl)), ?_⟩
  have hm := ArithmeticMachine.cost_total_le .equal
  simp only [total_add, he]
  change n + 1 + 1 + (12 + ((ArithmeticMachine.cost .equal).total + 3 * n + 3)) ≤ 256
  omega

/-- Every original guard edge lowers with a single absolute constant. -/
theorem step_lowering {a : F} {input : CanonicalGuardMachine.Input (QuadraticAlgebra F a 0)}
    {s t : CanonicalGuardMachine.Configuration (QuadraticAlgebra F a 0)} {c : ℕ}
    (h : CanonicalGuardMachine.Step input s c t) :
    ∃ n d, Trace a (mapInput encode input) n (represent encode input s) d
      (represent encode input t) ∧ n + d.total ≤ 131072 := by
  cases h with
  | start => exact ⟨1, entryCost, single rfl, by decide⟩
  | take => exact ⟨1, residualLaunch, single rfl, by decide⟩
  | empty => exact ⟨1, residualLaunch, single rfl, by decide⟩
  | @zero q ps s t c h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticResidualZeroMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := zero_trace (input := mapInput encode input) (mapPrevious encode ps) hc
      exact ⟨n, d, hd, by omega⟩
  | passed => exact ⟨1, returnCost, single rfl, by decide⟩
  | failed => exact ⟨1, returnCost, single rfl, by decide⟩
  | witness h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticResidualWitnessMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := witness_trace (input := mapInput encode input) hc
      exact ⟨n, d, hd, by omega⟩
  | absent => exact ⟨1, returnCost, single rfl, by decide⟩
  | @selected u =>
      have hb : ArithmeticMachine.specification
          ⟨a, encode u, (mapInput encode input).center⟩ .equal =
          .boolean (decide (u = input.center)) := by
        by_cases hu : u = input.center
        · subst u
          simp [ArithmeticMachine.specification, mapInput, encode]
        · have hne : ¬(u.re = input.center.re ∧ u.im = input.center.im) := by
            intro h
            apply hu
            ext <;> simp [h.1, h.2]
          by_cases hr : u.re = input.center.re
          · have hi : u.im ≠ input.center.im := fun hi ↦ hne ⟨hr, hi⟩
            simp [ArithmeticMachine.specification, mapInput, encode, hu, hr, hi]
          · simp [ArithmeticMachine.specification, mapInput, encode, hu, hr]
      obtain ⟨n, d, hd, hb⟩ := selected_lowering a (mapInput encode input) _ (encode u) _ hb
      exact ⟨n, d, hd, by omega⟩
  | emit => exact ⟨1, emitCost, single rfl, by decide⟩

/-- The absolute factor applies once to the whole original execution, not at each list position. -/
theorem trace_lowering {a : F} {input : CanonicalGuardMachine.Input (QuadraticAlgebra F a 0)}
    {n : ℕ} {s t : CanonicalGuardMachine.Configuration (QuadraticAlgebra F a 0)} {c : ℕ}
    (h : CanonicalGuardMachine.Trace input n s c t) :
    ∃ k d, Trace a (mapInput encode input) k (represent encode input s) d
      (represent encode input t) ∧ k + d.total ≤ 131072 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Every finite source run has the same represented coordinate endpoint and bounded actual work. -/
theorem run_lowering (a : F) (input : CanonicalGuardMachine.Input (QuadraticAlgebra F a 0))
    (fuel : ℕ) (s : CanonicalGuardMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a (mapInput encode input) k (represent encode input s) =
      (represent encode input (CanonicalGuardMachine.runFuel input fuel s).1, d) ∧
      k + d.total ≤ 131072 * fuel := by
  obtain ⟨n, hn, ht⟩ := CanonicalGuardMachine.runFuel_refines input fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Raw coordinates return the exact source guard Boolean for the same previous equations. -/
theorem computation_correct (a : F) (input : Input F) (ps : List (Equation F)) :
    ∃ k c, runFuel a input k (.start ps) =
      (.done (CanonicalGuardMachine.result (mapInput (ArithmeticMachine.decode a) input)
        (mapPrevious (ArithmeticMachine.decode a) ps)), c) ∧
      k + c.total ≤ 131072 * CanonicalGuardMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input)
        (mapPrevious (ArithmeticMachine.decode a) ps) := by
  obtain ⟨k, c, hr, hb⟩ := run_lowering a (mapInput (ArithmeticMachine.decode a) input)
    (CanonicalGuardMachine.fuel (mapInput (ArithmeticMachine.decode a) input)
      (mapPrevious (ArithmeticMachine.decode a) ps))
    (.start (mapPrevious (ArithmeticMachine.decode a) ps))
  obtain ⟨sourceCost, hs, _hc⟩ := CanonicalGuardMachine.evaluation_runFuel
    (mapInput (ArithmeticMachine.decode a) input) (mapPrevious (ArithmeticMachine.decode a) ps)
  rw [hs] at hr
  have hi : mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input := by
    cases input
    simp [mapInput, mapEquation, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  have hp : mapPrevious encode (mapPrevious (ArithmeticMachine.decode a) ps) = ps := by
    simp [mapPrevious, mapEquation, List.map_map, Function.comp_def,
      encode, ArithmeticMachine.decode]
  rw [hi] at hr
  exact ⟨k, c, by simpa only [represent, hp] using hr, hb⟩

end ReedSolomon.HiddenDerivative.QuadraticCanonicalGuardMachine
