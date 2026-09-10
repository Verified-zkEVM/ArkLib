/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.ShiftMachine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.PreparationRefinement
public import ArkLib.Data.Polynomial.QuadraticJetHornerRefinement
/-!
# Same-execution coordinate translation

Base negation, coordinate Horner and coordinate preparation implement each original transition.
The fixed factor bounds the complete trace and preserves every output and failure tag.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticCenterShiftMachine

open QuadraticAlgebra Polynomial
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Represent the supplied coefficient, center and degree registers. -/
def mapInput {K J : Type*} (f : K → J) (input : CenterShiftMachine.Input K) :
    CenterShiftMachine.Input J := ⟨input.coefficients.map f, f input.center, input.degree⟩

/-- Preserve every point, callee state and output tag. -/
def represent {K F : Type*} (f : K → Pair F) :
    CenterShiftMachine.Configuration K → Configuration F
  | .start => .start
  | .jet x s => .jet (f x) (.ready (QuadraticJetHornerMachine.mapState f s))
  | .prepare s => .prepare (QuadraticJetPreparationMachine.mapState f s)
  | .done out => .done (out.map (List.map f))

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Raw materialized inputs survive the coordinate round trip. -/
theorem encode_decode_input (a : F) (input : Input F) :
    mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input := by
  cases input
  simp [mapInput, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Every arithmetic instruction executes with its retained negation input. -/
theorem arithmetic_trace {a : F} {input : Input F} {payload : ArithmeticMachine.Input F}
    {n : ℕ} {s t : ArithmeticMachine.Configuration F}
    {c : ArithmeticMachine.Cost} (h : ArithmeticMachine.Trace payload n s c t) :
    ∃ d, Trace a input n (.negate payload s) d (.negate payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨delegated c + d, .cons ?_ hd, ?_⟩
      · simp only [step, head.step_eq]
      · rw [total_add, delegated_total, he, base_total_add]
        omega

/-- Every jet instruction retains its actual point and complete ledger. -/
theorem jet_trace {a : F} {input : Input F} {x : Pair F} {n : ℕ}
    {s t : QuadraticJetHornerMachine.Configuration F} {c : Cost}
    (h : QuadraticJetHornerMachine.Trace a x n s c t) :
    ∃ d, Trace a input n (.jet x s) d (.jet x t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Preparation steps retain both coordinate literals and all output allocations. -/
theorem preparation_trace {a : F} {input : Input F} {n : ℕ}
    {s t : QuadraticJetPreparationMachine.Configuration F} {c : Cost}
    (h : QuadraticJetPreparationMachine.Trace n s c t) :
    ∃ d, Trace a input n (.prepare s) d (.prepare t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Actual base negation emits the point installed into the Horner child. -/
theorem entry_lowering (a : F) (input : CenterShiftMachine.Input (QuadraticAlgebra F a 0)) :
    ∃ n c, Trace a (mapInput encode input) n .start c
      (.jet (encode (-input.center))
        (.ready (.initialize (input.coefficients.map encode) (input.degree + 1) []))) ∧
      n + c.total ≤ 256 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace
    ⟨a, encode input.center, encode input.center⟩ .neg
  obtain ⟨c, hc, he⟩ := arithmetic_trace (a := a) (input := mapInput encode input) ht
  have hs : step a (mapInput encode input)
      (.negate ⟨a, encode input.center, encode input.center⟩
        (.done (ArithmeticMachine.specification
          ⟨a, encode input.center, encode input.center⟩ .neg))) =
      some (.jet (encode (-input.center))
        (.ready (.initialize (input.coefficients.map encode) (input.degree + 1) [])),
        administrative CenterShiftMachine.entryCost) := rfl
  refine ⟨n + 1 + 1, launch + (c + administrative CenterShiftMachine.entryCost),
    .cons rfl (hc.trans (single hs)), ?_⟩
  have hm := ArithmeticMachine.cost_total_le .neg
  simp only [total_add, he]
  change n + 1 + 1 + (7 + ((ArithmeticMachine.cost .neg).total + 3 * n + 7)) ≤ 256
  omega

/-- Every source edge lowers with an absolute constant independent of polynomial width. -/
theorem step_lowering {a : F} {input : CenterShiftMachine.Input (QuadraticAlgebra F a 0)}
    {s t : CenterShiftMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : CenterShiftMachine.Cost} (h : CenterShiftMachine.Step input s c t) :
    ∃ n d, Trace a (mapInput encode input) n (represent encode s) d
      (represent encode t) ∧ n + d.total ≤ 2048 := by
  cases h with
  | enter =>
      obtain ⟨n, c, hc, hb⟩ := entry_lowering a input
      exact ⟨n, c, hc, by omega⟩
  | jet h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticJetHornerMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := jet_trace (input := mapInput encode input) hc
      exact ⟨n, d, hd, by omega⟩
  | handoff => exact ⟨1, administrative CenterShiftMachine.handoffCost, single rfl, by decide⟩
  | prepare h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticJetPreparationMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := preparation_trace (a := a) (input := mapInput encode input) hc
      exact ⟨n, d, hd, by omega⟩
  | «return» => exact ⟨1, administrative CenterShiftMachine.returnCost, single rfl, by decide⟩

/-- The absolute factor applies once to the full source trace. -/
theorem trace_lowering {a : F} {input : CenterShiftMachine.Input (QuadraticAlgebra F a 0)}
    {n : ℕ} {s t : CenterShiftMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : CenterShiftMachine.Cost} (h : CenterShiftMachine.Trace input n s c t) :
    ∃ k d, Trace a (mapInput encode input) k (represent encode s) d
      (represent encode t) ∧ k + d.total ≤ 2048 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Finite source runs transfer with exactly represented partial or completed endpoints. -/
theorem run_lowering (a : F) (input : CenterShiftMachine.Input (QuadraticAlgebra F a 0))
    (fuel : ℕ) (s : CenterShiftMachine.Configuration (QuadraticAlgebra F a 0)) :
    ∃ k d, runFuel a (mapInput encode input) k (represent encode s) =
      (represent encode (CenterShiftMachine.runFuel input fuel s).1, d) ∧
      k + d.total ≤ 2048 * fuel := by
  obtain ⟨n, hn, ht⟩ := CenterShiftMachine.runFuel_refines input fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Materialized coordinate input returns the exact source translation and physical width. -/
theorem shift_correct (a : F) (input : Input F)
    (hwidth : input.coefficients.length = input.degree + 1) :
    ∃ k c out, runFuel a input k .start = (.done (some out), c) ∧
      out.length = input.degree + 1 ∧
      JetHornerMachine.coefficientPolynomial (out.map (ArithmeticMachine.decode a)) =
        (JetHornerMachine.coefficientPolynomial
          (input.coefficients.map (ArithmeticMachine.decode a))).comp
            (X - C (ArithmeticMachine.decode a input.center)) ∧
      k + c.total ≤ 2048 * CenterShiftMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) := by
  obtain ⟨out, hs, hlen, hpoly⟩ := CenterShiftMachine.shift_correct
    (mapInput (ArithmeticMachine.decode a) input) _ rfl (by simpa [mapInput] using hwidth)
  obtain ⟨k, c, hr, hb⟩ := run_lowering a (mapInput (ArithmeticMachine.decode a) input)
    (CenterShiftMachine.fuel (mapInput (ArithmeticMachine.decode a) input)) .start
  rw [hs, encode_decode_input] at hr
  have hout : (out.map encode).map (ArithmeticMachine.decode a) = out := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨k, c, out.map encode, hr, by simpa [mapInput] using hlen, ?_, hb⟩
  simpa only [hout, mapInput] using hpoly

end ReedSolomon.HiddenDerivative.QuadraticCenterShiftMachine
