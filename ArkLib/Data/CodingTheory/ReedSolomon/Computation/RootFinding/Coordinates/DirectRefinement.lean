/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.DirectMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.Refinement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectArithmeticRefinement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.DirectCoefficientRefinement
public import ArkLib.Data.Polynomial.QuadraticUpdateRefinement
/-!
# Same-execution coordinate direct coefficient refinement

Both recovery calls, the actual candidate update, charged lookups and scalar suffix preserve
source endpoints and failure branches. The absolute lowering factor applies once to total source
fuel; it is not multiplied per lifting iteration. Raw polynomial representations and original
degree/index/sample hypotheses identify the exact direct regular coefficient result.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticDirectCoefficientMachine

open Polynomial QuadraticAlgebra CompPoly PolynomialDifferential
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

abbrev mapInput := @QuadraticResidualBatch.mapInput

/-- Representation includes the exact recovery input and materialized update increment. -/
def represent {K F : Type*} [One K] (a : F) (f : K → Pair F)
    (input : DirectCoefficientMachine.Input K) :
    DirectCoefficientMachine.Configuration K → Configuration F
  | .start xs => .start (xs.map f)
  | .recover b cs xs s => .recover (b.map f) (xs.map f)
      (mapInput f (DirectCoefficientMachine.withCoefficients input cs))
      (QuadraticResidualCoefficientMachine.represent a f
        (DirectCoefficientMachine.withCoefficients input cs) s)
  | .lookup b xs j vs => .lookup (b.map f) (xs.map f) j (vs.map f)
  | .update b xs s => .update (f b) (xs.map f) (f 1) (.ready (QuadraticUpdateMachine.mapState f s))
  | .negate b one => .arithmetic (.ready (.negate (f b) (f one)))
  | .slope b one => .arithmetic (.ready (.slope (f b) (f one)))
  | .test b slope => .arithmetic (.ready (.test (f b) (f slope)))
  | .invert b slope => .arithmetic (.ready (.invert (f b) (f slope)))
  | .multiply b inv => .arithmetic (.ready (.multiply (f b) (f inv)))
  | .emit out => .arithmetic (.ready (.emit (out.map f)))
  | .done out => .done (out.map f)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Recoveries retain their constructed payload and every nested instruction charge. -/
theorem recovery_trace {a : F} {input payload : Input F} {w L k n : ℕ}
    (b : Option (Pair F)) (xs : List (Pair F))
    {s t : QuadraticResidualCoefficientMachine.Configuration F} {c : Cost}
    (h : QuadraticResidualCoefficientMachine.Trace a payload L n s c t) :
    ∃ d, Trace a input w L k n (.recover b xs payload s) d (.recover b xs payload t) ∧
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

/-- Update steps use the retained increment, including all prefix restoration and save costs. -/
theorem update_trace {a : F} {input : Input F} {w L k n : ℕ} (b gamma : Pair F)
    (xs : List (Pair F)) {s t : QuadraticUpdateMachine.Configuration F} {c : Cost}
    (h : QuadraticUpdateMachine.Trace a gamma n s c t) :
    ∃ d, Trace a input w L k n (.update b xs gamma s) d (.update b xs gamma t) ∧
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

/-- Every actual arithmetic child instruction retains its ledger and outer wrapper. -/
theorem arithmetic_trace {a : F} {input : Input F} {w L k n : ℕ}
    {s t : DirectArithmeticMachine.Configuration F} {c : Cost}
    (h : DirectArithmeticMachine.Trace a n s c t) :
    ∃ d, Trace a input w L k n (.arithmetic s) d (.arithmetic t) ∧
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

/-- The existing exact arithmetic-phase lowering lifts through this driver's wrapper. -/
theorem arithmetic_lowering (a : F) (ha : ¬IsSquare a) (input : Input F) (w L k : ℕ)
    {p q : DirectArithmeticMachine.Phase (QuadraticAlgebra F a 0)} :
    letI := fieldOfNonsquare a ha
    DirectArithmeticMachine.LocalStep p q →
    ∃ n d, Trace a input w L k n
      (.arithmetic (.ready (DirectArithmeticMachine.mapPhase encode p))) d
      (.arithmetic (.ready (DirectArithmeticMachine.mapPhase encode q))) ∧
      n + d.total ≤ 4194304 := by
  let := fieldOfNonsquare a ha
  intro h
  obtain ⟨n, c, hc, hb⟩ := DirectArithmeticMachine.local_step_lowering a ha h
  obtain ⟨d, hd, he⟩ := arithmetic_trace (input := input) (w := w) (L := L) (k := k) hc
  exact ⟨n, d, hd, by omega⟩

/-- Each original direct coefficient transition has the exact represented coordinate endpoint. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (input : DirectCoefficientMachine.Input (QuadraticAlgebra F a 0)) (w L k : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : DirectCoefficientMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : DirectCoefficientMachine.Cost}, DirectCoefficientMachine.Step input w L k s c t →
      ∃ n d, Trace a (mapInput encode input) w L k n (represent a encode input s) d
        (represent a encode input t) ∧ n + d.total ≤ 4194304 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | start =>
      exact ⟨1, administrative DirectCoefficientMachine.startCost + allocation 4,
      single rfl, by decide⟩
  | recover h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticResidualCoefficientMachine.step_lowering a ha _ L h
      obtain ⟨d, hd, he⟩ := recovery_trace (input := mapInput encode input) (w := w) (k := k) _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | recoverReturn =>
      exact ⟨1, administrative DirectCoefficientMachine.lookupCost, single rfl, by decide⟩
  | recoverReject =>
      exact ⟨1, administrative DirectCoefficientMachine.rejectCost, single rfl, by decide⟩
  | advance =>
      exact ⟨1, administrative DirectCoefficientMachine.advanceCost, single rfl, by decide⟩
  | empty =>
      exact ⟨1, administrative DirectCoefficientMachine.rejectCost, single rfl, by decide⟩
  | selectZero =>
      exact ⟨1, administrative DirectCoefficientMachine.selectZeroCost + oneExtra,
      single rfl, by decide⟩
  | selectOne =>
      exact ⟨1, administrative DirectCoefficientMachine.selectOneCost, single rfl, by decide⟩
  | update h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticUpdateMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := update_trace (input := mapInput encode input)
        (w := w) (L := L) (k := k) _ _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | updateReturn =>
      exact ⟨1, administrative DirectCoefficientMachine.updateReturnCost + allocation 5,
      single rfl, by decide⟩
  | updateReject =>
      exact ⟨1, administrative DirectCoefficientMachine.rejectCost, single rfl, by decide⟩
  | negate => exact arithmetic_lowering a ha _ w L k .negate
  | slope => exact arithmetic_lowering a ha _ w L k .slope
  | zero h => exact arithmetic_lowering a ha _ w L k (.zero h)
  | nonzero h => exact arithmetic_lowering a ha _ w L k (.nonzero h)
  | invert => exact arithmetic_lowering a ha _ w L k .invert
  | multiply => exact arithmetic_lowering a ha _ w L k .multiply
  | emit => exact ⟨2, (DirectArithmeticMachine.emitCost + wrapper) + returned,
      (single rfl).trans (single rfl), by decide⟩

/-- The absolute per-step factor applies once to the complete source trace. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (input : DirectCoefficientMachine.Input (QuadraticAlgebra F a 0)) (w L k : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : DirectCoefficientMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : DirectCoefficientMachine.Cost}, DirectCoefficientMachine.Trace input w L k n s c t →
      ∃ steps d, Trace a (mapInput encode input) w L k steps (represent a encode input s) d
        (represent a encode input t) ∧ steps + d.total ≤ 4194304 * n := by
  let := fieldOfNonsquare a ha
  intro n s t c h
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering a ha input w L k head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Any finite source run reaches its exact represented endpoint, including singular rejection. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a)
    (input : DirectCoefficientMachine.Input (QuadraticAlgebra F a 0)) (w L k fuel : ℕ)
    (s : DirectCoefficientMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ steps d, runFuel a (mapInput encode input) w L k steps (represent a encode input s) =
      (represent a encode input (DirectCoefficientMachine.runFuel input w L k fuel s).1, d) ∧
      steps + d.total ≤ 4194304 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := DirectCoefficientMachine.runFuel_refines input w L k fuel s
  obtain ⟨steps, d, hd, hb⟩ := trace_lowering a ha input w L k ht
  exact ⟨steps, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Raw inputs execute to the exact direct regular coefficient, including a singular slope's
failure tag. Both candidate degree bounds and all original index/sample premises are explicit. -/
theorem coefficient_correct (a : F) (ha : ¬IsSquare a) (input : Input F) (D w L k : ℕ)
    (samples : List (Pair F))
    (Q : CPoly.CMvPolynomial (input.order + 2) (QuadraticAlgebra F a 0))
    (P : CPolynomial (QuadraticAlgebra F a 0)) (points : Fin L ↪ QuadraticAlgebra F a 0)
    (hsamples : samples.map (ArithmeticMachine.decode a) = List.ofFn (fun i => points i))
    (hwidth : input.coefficients.length = w) (hindex : k + input.order < w) (hk : k < L)
    (hP : JetHornerMachine.coefficientPolynomial
      (input.coefficients.map (ArithmeticMachine.decode a)) = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial
      (mapInput (ArithmeticMachine.decode a) input).terms =
        MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hdegree : P.natDegree ≤ D) :
    letI := fieldOfNonsquare a ha
    (effectiveRegularCandidate k input.order P 1).natDegree ≤ D →
    differentialWeightedDegree D (semanticEquation Q) < L →
    ∃ steps c out, runFuel a input w L k steps (.start samples) = (.done out, c) ∧
      out.map (ArithmeticMachine.decode a) =
        effectiveDirectRegularCoefficient Q (ArithmeticMachine.decode a input.center) P k ∧
      steps + c.total ≤ 4194304 * DirectCoefficientMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) L k samples.length := by
  let := fieldOfNonsquare a ha
  intro hdegreeOne hweight
  obtain ⟨sourceCost, hs, _⟩ := DirectCoefficientMachine.computation_runFuel_correct Q
    (ArithmeticMachine.decode a input.center) P
    (input.coefficients.map (ArithmeticMachine.decode a))
    (mapInput (ArithmeticMachine.decode a) input).terms w k points
    (samples.map (ArithmeticMachine.decode a)) hsamples (by simpa using hwidth) hindex hk
    hP hQ hdegree hdegreeOne hweight
  change DirectCoefficientMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) w L k
    (DirectCoefficientMachine.fuel (mapInput (ArithmeticMachine.decode a) input) L k
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a))) = _ at hs
  obtain ⟨steps, c, hr, hb⟩ := run_lowering a ha (mapInput (ArithmeticMachine.decode a) input) w L k
    (DirectCoefficientMachine.fuel (mapInput (ArithmeticMachine.decode a) input) L k
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hi := QuadraticResidualBatch.encode_decode_input a input
  change mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input at hi
  rw [hi] at hr
  have hp : (samples.map (ArithmeticMachine.decode a)).map encode = samples := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [represent, hp] at hr
  refine ⟨steps, c, _, hr, ?_, ?_⟩
  · simp [Option.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  · simpa only [List.length_map] using hb

end ReedSolomon.HiddenDerivative.QuadraticDirectCoefficientMachine
