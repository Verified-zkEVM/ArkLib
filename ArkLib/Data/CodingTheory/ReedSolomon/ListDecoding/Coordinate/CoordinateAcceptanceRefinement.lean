/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateAcceptanceMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalAcceptanceMachine
/-!
# Same-execution coordinate acceptance

Actual coordinate guard traces and exact-cost base candidate traces compose with their caller
charges. A single absolute factor bounds the whole original trace's count and work.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticCanonicalAcceptanceMachine

open QuadraticAlgebra
open HiddenDerivative
open MvPolynomial.QuadraticEvaluationMachine (total_add)

local notation "enc" => CoordinateCandidateMachine.encode

/-- Proof-only representation of every suspended source state. -/
def represent {F : Type*} [CommSemiring F] (a : F)
    (input : CanonicalGuardMachine.Input (QuadraticAlgebra F a 0)) :
    CanonicalAcceptanceMachine.Configuration F a 0 → Configuration F
  | .start ps => .start (QuadraticCanonicalGuardMachine.mapPrevious enc ps)
  | .guard s => .guard (QuadraticCanonicalGuardMachine.represent enc input s)
  | .candidate s => .candidate (CoordinateCandidateMachine.represent s)
  | .emit out => .emit out
  | .done out => .done out

variable {F : Type*} [Field F] [DecidableEq F]

/-- Preserve every coordinate guard primitive plus its caller dispatch. -/
theorem guard_trace {a : F} {input : Guard.Input F} {w k A n : ℕ}
    {rows : List (F × F)} {s t : Guard.Configuration F}
    {c : MvPolynomial.QuadraticEvaluationMachine.Cost}
    (h : QuadraticCanonicalGuardMachine.Trace a input n s c t) :
    Trace a input w k A rows n (.guard s) (c.total + 3 * n) (.guard t) := by
  induction h with
  | nil => exact .nil _
  | @cons n s u t c d head tail ih =>
      convert Trace.cons (s := .guard s) (c := c.total + 3)
        (by simp only [step, head]) ih using 1
      rw [total_add]
      omega

/-- The raw candidate driver also advances by actual instructions and exact charges. -/
theorem candidate_trace {a : F} {input : Guard.Input F} {w k A n : ℕ}
    {rows : List (F × F)} {s t : Candidate.Configuration F} {c : ℕ}
    (h : CoordinateCandidateMachine.Trace w k A rows n s c t) :
    Trace a input w k A rows n (.candidate s) (c + 3 * n) (.candidate t) := by
  induction h with
  | nil => exact .nil _
  | @cons n s u t c d head tail ih =>
      convert Trace.cons (s := .candidate s) (c := c + 3)
        (by simp only [step, head]) ih using 1
      omega

/-- Each original edge lowers to actual child instructions with one fixed factor. -/
theorem step_lowering {a : F}
    {input : CanonicalGuardMachine.Input (QuadraticAlgebra F a 0)} {w k A : ℕ}
    {rows : List (F × F)} {s t : CanonicalAcceptanceMachine.Configuration F a 0} {c : ℕ}
    (h : CanonicalAcceptanceMachine.Step input w k A rows s c t) :
    ∃ n d, Trace a (QuadraticCanonicalGuardMachine.mapInput enc input) w k A rows n
      (represent a input s) d (represent a input t) ∧ n + d ≤ 524288 * (1 + c) := by
  cases h with
  | guard h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticCanonicalGuardMachine.step_lowering h
      exact ⟨n, c.total + 3 * n, guard_trace hc, by omega⟩
  | @candidate s t c h =>
      refine ⟨1, c + 3 + 0, .cons ?_ (.nil _), ?_⟩
      · simp only [represent, step, CoordinateCandidateMachine.step_lowering h]
      · omega
  | start => exact ⟨1, 4, .cons rfl (.nil _), by decide⟩
  | reject => exact ⟨1, 3, .cons rfl (.nil _), by decide⟩
  | passed => exact ⟨1, 4, .cons rfl (.nil _), by decide⟩
  | returned => exact ⟨1, 3, .cons rfl (.nil _), by decide⟩
  | emit => exact ⟨1, 3, .cons rfl (.nil _), by decide⟩

/-- The factor is applied once to the source trace's total count and work. -/
theorem trace_lowering {a : F}
    {input : CanonicalGuardMachine.Input (QuadraticAlgebra F a 0)} {w k A n : ℕ}
    {rows : List (F × F)} {s t : CanonicalAcceptanceMachine.Configuration F a 0} {c : ℕ}
    (h : CanonicalAcceptanceMachine.Trace input w k A rows n s c t) :
    ∃ m d, Trace a (QuadraticCanonicalGuardMachine.mapInput enc input) w k A rows m
      (represent a input s) d (represent a input t) ∧ m + d ≤ 524288 * (n + c) := by
  induction h with
  | nil => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      exact ⟨n + m, c + d, hc.trans hd, by omega⟩

/-- Arbitrary fuel prefixes preserve the represented endpoint of the same source execution. -/
theorem run_lowering (a : F)
    (input : CanonicalGuardMachine.Input (QuadraticAlgebra F a 0)) (w k A fuel : ℕ)
    (rows : List (F × F)) (s : CanonicalAcceptanceMachine.Configuration F a 0) :
    ∃ n d, runFuel a (QuadraticCanonicalGuardMachine.mapInput enc input) w k A rows n
      (represent a input s) =
      (represent a input (CanonicalAcceptanceMachine.runFuel input w k A rows fuel s).1, d) ∧
      n + d ≤ 524288 *
        (fuel + (CanonicalAcceptanceMachine.runFuel input w k A rows fuel s).2) := by
  obtain ⟨m, hm, ht⟩ := CanonicalAcceptanceMachine.runFuel_refines input w k A fuel rows s
  obtain ⟨n, d, hd, hb⟩ := trace_lowering ht
  exact ⟨n, d, hd.runFuel_eq, by omega⟩

/-- Raw inputs return the exact canonical acceptance answer with the same bounded actual run. -/
theorem computation_correct (a : F) (input : Guard.Input F) (ps : List (Guard.Equation F))
    (w k A : ℕ) (rows : List (F × F)) (hwidth : input.coefficients.length = w) :
    let sourceInput := QuadraticCanonicalGuardMachine.mapInput (ArithmeticMachine.decode a) input
    let sourcePs := QuadraticCanonicalGuardMachine.mapPrevious (ArithmeticMachine.decode a) ps
    ∃ n c, runFuel a input w k A rows n (.start ps) =
      (.done (CanonicalAcceptanceMachine.result sourceInput sourcePs w k A rows), c) ∧
      n + c ≤ 524288 * (CanonicalAcceptanceMachine.fuel sourceInput sourcePs w k rows.length +
        CanonicalAcceptanceMachine.workBound sourceInput sourcePs w k rows.length) := by
  dsimp only
  let si := QuadraticCanonicalGuardMachine.mapInput (ArithmeticMachine.decode a) input
  let sp := QuadraticCanonicalGuardMachine.mapPrevious (ArithmeticMachine.decode a) ps
  have hw : si.coefficients.length = w := by
    simpa [si, QuadraticCanonicalGuardMachine.mapInput] using hwidth
  obtain ⟨c, hc, hb⟩ := CanonicalAcceptanceMachine.evaluation_runFuel si sp w k A rows hw
  obtain ⟨n, d, hd, he⟩ := run_lowering a si w k A
    (CanonicalAcceptanceMachine.fuel si sp w k rows.length) rows (.start sp)
  rw [hc] at hd he
  have hi : QuadraticCanonicalGuardMachine.mapInput enc si = input := by
    cases input
    simp [si, QuadraticCanonicalGuardMachine.mapInput, QuadraticCanonicalGuardMachine.mapEquation,
      List.map_map, Function.comp_def, CoordinateCandidateMachine.encode, ArithmeticMachine.decode]
  have hp : QuadraticCanonicalGuardMachine.mapPrevious enc sp = ps := by
    simp [sp, QuadraticCanonicalGuardMachine.mapPrevious,
      QuadraticCanonicalGuardMachine.mapEquation,
      List.map_map, Function.comp_def, CoordinateCandidateMachine.encode, ArithmeticMachine.decode]
  rw [hi] at hd
  refine ⟨n, d, by simpa only [represent, hp] using hd, ?_⟩
  change n + d ≤ 524288 * (CanonicalAcceptanceMachine.fuel si sp w k rows.length +
    CanonicalAcceptanceMachine.workBound si sp w k rows.length)
  dsimp only at he
  omega

end ReedSolomon.ListDecoding.QuadraticCanonicalAcceptanceMachine
