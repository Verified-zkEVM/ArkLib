/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ZeroMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticBatchSpec
/-!
# Same-execution coordinate residual acceptance

The emitted Boolean is exactly the source residual test. Each source edge lowers with one
absolute factor, independent of sample count, and every delegated base instruction is charged.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualZeroMachine

open QuadraticAlgebra Polynomial MvPolynomial CompPoly
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

abbrev mapInput := @QuadraticResidualBatch.mapInput
abbrev mapEntries := @QuadraticResidualBatch.mapEntries

/-- Preserve samples, residual order, acceptance tags and retained child input. -/
def represent {K F : Type*} (f : K → Pair F) (input : ResidualZeroMachine.Input K) :
    ResidualZeroMachine.Configuration K → Configuration F
  | .start ps => .start (ps.map f)
  | .batch s => .batch (mapInput f input) (QuadraticResidualBatch.represent f input s)
  | .scan ps => .scan (mapEntries f ps)
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

/-- Every arithmetic instruction executes with its retained equality input. -/
theorem arithmetic_trace {a : F} {input : Input F} (ps : List (Entry F))
    {payload : ArithmeticMachine.Input F} {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a input n (.check ps payload s) d (.check ps payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨delegated c + d, .cons ?_ hd, ?_⟩
      · simp only [step, head.step_eq]
      · rw [total_add, delegated_total, he, base_total_add]
        omega

/-- Every batch instruction preserves its full cost plus the outer dispatch. -/
theorem batch_trace {a : F} {input payload : Input F} {n : ℕ}
    {s t : QuadraticResidualBatch.Configuration F} {c : Cost}
    (h : QuadraticResidualBatch.Trace a payload n s c t) :
    ∃ d, Trace a input n (.batch payload s) d (.batch payload t) ∧
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

/-- Both coordinates are tested before the actual Boolean controls the scan. -/
theorem check_lowering (a : F) (input : Input F) (u v : Pair F) (ps : List (Entry F))
    (b : Bool) (hb : ArithmeticMachine.specification ⟨a, v, (0, 0)⟩ .equal = .boolean b) :
    ∃ n c, Trace a input n (.scan ((u, v) :: ps)) c (checked ps b) ∧
      n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace ⟨a, v, (0, 0)⟩ .equal
  rw [hb] at ht
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (input := input) ps ht
  refine ⟨n + 1 + 1, launch + (c + administrative ResidualZeroMachine.checkCost),
    .cons rfl (hc.trans (single rfl)), ?_⟩
  have hm := ArithmeticMachine.cost_total_le .equal
  simp only [total_add, he]
  change n + 1 + 1 + (13 + ((ArithmeticMachine.cost .equal).total + 3 * n + 5)) ≤ 256
  omega

/-- Every source acceptance edge lowers with one absolute constant. -/
theorem step_lowering {a : F} {input : ResidualZeroMachine.Input (QuadraticAlgebra F a 0)}
    {s t : ResidualZeroMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : ResidualZeroMachine.Cost} (h : ResidualZeroMachine.Step input s c t) :
    ∃ n d, Trace a (mapInput encode input) n (represent encode input s) d
      (represent encode input t) ∧ n + d.total ≤ 32768 := by
  have small {s t : Configuration F}
      (h : ∃ n d, Trace a (mapInput encode input) n s d t ∧ n + d.total ≤ 256) :
      ∃ n d, Trace a (mapInput encode input) n s d t ∧ n + d.total ≤ 32768 := by
    obtain ⟨n, d, hd, hb⟩ := h
    exact ⟨n, d, hd, by omega⟩
  cases h with
  | enter => exact ⟨1, administrative ResidualZeroMachine.entryCost + allocation 4,
      single rfl, by decide⟩
  | batch h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticResidualBatch.step_lowering h
      obtain ⟨d, hd, he⟩ := batch_trace (input := mapInput encode input) hc
      exact ⟨n, d, hd, by omega⟩
  | handoff => exact ⟨1, administrative ResidualZeroMachine.handoffCost, single rfl, by decide⟩
  | zero hv =>
      subst hv
      apply small
      exact check_lowering a _ _ _ _ true (by simp [ArithmeticMachine.specification, encode])
  | @nonzero u v ps hv =>
      have hz : ¬(v.re = 0 ∧ v.im = 0) := by
        intro h
        apply hv
        ext <;> simp [h.1, h.2]
      apply small
      apply check_lowering a _ _ _ _ false
      by_cases hr : v.re = 0
      · have hi : v.im ≠ 0 := fun hi => hz ⟨hr, hi⟩
        simp [ArithmeticMachine.specification, encode, hr, hi]
      · simp [ArithmeticMachine.specification, encode, hr]
  | empty => exact ⟨1, administrative ResidualZeroMachine.emptyCost, single rfl, by decide⟩
  | emit => exact ⟨1, administrative ResidualZeroMachine.emitCost, single rfl, by decide⟩

/-- A constant factor applies once to the whole source execution. -/
theorem trace_lowering {a : F} {input : ResidualZeroMachine.Input (QuadraticAlgebra F a 0)}
    {n : ℕ} {s t : ResidualZeroMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : ResidualZeroMachine.Cost} (h : ResidualZeroMachine.Trace input n s c t) :
    ∃ k d, Trace a (mapInput encode input) k (represent encode input s) d
      (represent encode input t) ∧ k + d.total ≤ 32768 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Finite source runs have identical represented endpoints and bounded actual work. -/
theorem run_lowering (a : F) (input : ResidualZeroMachine.Input (QuadraticAlgebra F a 0))
    (fuel : ℕ) (s : ResidualZeroMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a (mapInput encode input) k (represent encode input s) =
      (represent encode input (ResidualZeroMachine.runFuel input fuel s).1, d) ∧
      k + d.total ≤ 32768 * fuel := by
  obtain ⟨n, hn, ht⟩ := ResidualZeroMachine.runFuel_refines input fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Raw coordinate execution returns exactly the source Boolean, including empty samples. -/
theorem computation_correct (a : F) (input : Input F) (ps : List (Pair F)) :
    ∃ k c, runFuel a input k (.start ps) =
      (.done (ResidualZeroMachine.result (mapInput (ArithmeticMachine.decode a) input)
        (ps.map (ArithmeticMachine.decode a))), c) ∧
      k + c.total ≤ 32768 * ResidualZeroMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) ps.length := by
  obtain ⟨k, c, hr, hb⟩ := run_lowering a (mapInput (ArithmeticMachine.decode a) input)
    (ResidualZeroMachine.fuel (mapInput (ArithmeticMachine.decode a) input)
      (ps.map (ArithmeticMachine.decode a)).length) (.start (ps.map (ArithmeticMachine.decode a)))
  rw [ResidualZeroMachine.zero_runFuel] at hr
  have hi := QuadraticResidualBatch.encode_decode_input a input
  change mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input at hi
  rw [hi] at hr
  have hp : (ps.map (ArithmeticMachine.decode a)).map encode = ps := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨k, c, ?_, by simpa only [List.length_map] using hb⟩
  simpa only [represent, hp] using hr

end ReedSolomon.HiddenDerivative.QuadraticResidualZeroMachine
