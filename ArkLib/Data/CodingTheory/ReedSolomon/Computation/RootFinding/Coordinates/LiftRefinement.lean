/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.LiftMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.DirectRefinement
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Semantics
public import ArkLib.Data.Polynomial.QuadraticUpdateRefinement
/-!
# Same-execution coordinate lifting loop

All stages retain direct and indexed-update children. A fixed absolute factor bounds the whole
source trace, including failures; it never compounds by iteration. Raw input representations
identify the whole emitted polynomial and its physical width. Regular-jet hypotheses transfer
the unique exhaustive-prefix candidate, without claiming full residual acceptance.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticRegularLiftMachine

open Polynomial QuadraticAlgebra CompPoly PolynomialDifferential
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

abbrev mapInput := @QuadraticResidualBatch.mapInput

/-- Preserve counters, samples, retained input fields and every partial child phase. -/
def represent {K F : Type*} [One K] (a : F) (f : K → Pair F) (input : RegularLiftMachine.Input K) :
    RegularLiftMachine.Configuration K → Configuration F
  | .start xs => .start (xs.map f)
  | .loop k n cs xs => .loop k n (cs.map f) (xs.map f)
  | .direct k n cs xs s => .direct k n (xs.map f)
      (mapInput f (DirectCoefficientMachine.withCoefficients input cs))
      (QuadraticDirectCoefficientMachine.represent a f
        (DirectCoefficientMachine.withCoefficients input cs) s)
  | .update k n xs gamma s => .update k n (xs.map f) (f gamma)
      (.ready (QuadraticUpdateMachine.mapState f s))
  | .emit out => .emit (out.map (List.map f))
  | .done out => .done (out.map (List.map f))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Direct child instructions use the retained input and keep their complete nested ledger. -/
theorem direct_trace {a : F} {input payload : Input F} {D L k remaining n : ℕ}
    (xs : List (Pair F)) {s t : QuadraticDirectCoefficientMachine.Configuration F} {c : Cost}
    (h : QuadraticDirectCoefficientMachine.Trace a payload (D + 1) L k n s c t) :
    ∃ d, Trace a input D L n (.direct k remaining xs payload s) d
      (.direct k remaining xs payload t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Indexed updates retain materialized gamma and each instruction's full cost. -/
theorem update_trace {a : F} {input : Input F} {D L k remaining n : ℕ}
    (xs : List (Pair F)) (gamma : Pair F) {s t : QuadraticUpdateMachine.Configuration F} {c : Cost}
    (h : QuadraticUpdateMachine.Trace a gamma n s c t) :
    ∃ d, Trace a input D L n (.update k remaining xs gamma s) d
      (.update k remaining xs gamma t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- One absolute constant bounds every source step, independently of the Taylor iteration. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (input : RegularLiftMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : RegularLiftMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : RegularLiftMachine.Cost}, RegularLiftMachine.Step input D L s c t →
      ∃ n d, Trace a (mapInput encode input) D L n (represent a encode input s) d
        (represent a encode input t) ∧ n + d.total ≤ 16777216 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | start => exact ⟨1, administrative RegularLiftMachine.startCost, single rfl, by decide⟩
  | finish => exact ⟨1, administrative RegularLiftMachine.finishCost + allocation 1,
      single rfl, by decide⟩
  | stage => exact ⟨1, administrative RegularLiftMachine.stageCost + allocation 4,
      single rfl, by decide⟩
  | direct h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticDirectCoefficientMachine.step_lowering a ha _ _ _ _ h
      obtain ⟨d, hd, he⟩ := direct_trace (input := mapInput encode input) _ hc
      exact ⟨n, d, hd, by omega⟩
  | directReturn => exact ⟨1, administrative RegularLiftMachine.directReturnCost,
      single rfl, by decide⟩
  | directReject => exact ⟨1, administrative RegularLiftMachine.rejectCost, single rfl, by decide⟩
  | update h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticUpdateMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := update_trace (input := mapInput encode input) (D := D) (L := L) _ _ hc
      exact ⟨n, d, hd, by omega⟩
  | updateReturn => exact ⟨1, administrative RegularLiftMachine.updateReturnCost,
      single rfl, by decide⟩
  | updateReject => exact ⟨1, administrative RegularLiftMachine.rejectCost, single rfl, by decide⟩
  | emit => exact ⟨1, administrative RegularLiftMachine.emitCost, single rfl, by decide⟩

/-- Compose the fixed factor over total source steps, with no per-iteration exponentiation. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (input : RegularLiftMachine.Input (QuadraticAlgebra F a 0)) (D L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : RegularLiftMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : RegularLiftMachine.Cost}, RegularLiftMachine.Trace input D L n s c t →
      ∃ steps d, Trace a (mapInput encode input) D L steps (represent a encode input s) d
        (represent a encode input t) ∧ steps + d.total ≤ 16777216 * n := by
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
    (input : RegularLiftMachine.Input (QuadraticAlgebra F a 0)) (D L fuel : ℕ)
    (s : RegularLiftMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ steps d, runFuel a (mapInput encode input) D L steps (represent a encode input s) =
      (represent a encode input (RegularLiftMachine.runFuel input D L fuel s).1, d) ∧
      steps + d.total ≤ 16777216 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := RegularLiftMachine.runFuel_refines input D L fuel s
  obtain ⟨steps, d, hd, hb⟩ := trace_lowering a ha input D L ht
  exact ⟨steps, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Completed source execution transfers directly to already materialized coordinate inputs. -/
theorem start_run_lowering (a : F) (ha : ¬IsSquare a) (input : Input F) (D L fuel : ℕ)
    (samples : List (Pair F)) (out : Option (List (QuadraticAlgebra F a 0)))
    (sourceCost : RegularLiftMachine.Cost) :
    letI := fieldOfNonsquare a ha
    RegularLiftMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L fuel
      (.start (samples.map (ArithmeticMachine.decode a))) = (.done out, sourceCost) →
    ∃ steps c, runFuel a input D L steps (.start samples) =
      (.done (out.map (List.map encode)), c) ∧ steps + c.total ≤ 16777216 * fuel := by
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

/-- Raw input executes the whole functional lift with physical width preserved on success. -/
theorem computation_correct (a : F) (ha : ¬IsSquare a) (input : Input F) (D L : ℕ)
    (samples : List (Pair F))
    (Q : CPoly.CMvPolynomial (input.order + 2) (QuadraticAlgebra F a 0))
    (P : CPolynomial (QuadraticAlgebra F a 0)) (points : Fin L ↪ QuadraticAlgebra F a 0)
    (hsamples : samples.map (ArithmeticMachine.decode a) = List.ofFn (fun i => points i))
    (hwidth : input.coefficients.length = D + 1)
    (hP : JetHornerMachine.coefficientPolynomial
      (input.coefficients.map (ArithmeticMachine.decode a)) = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial
      (mapInput (ArithmeticMachine.decode a) input).terms =
        MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : input.order ≤ D) (hlookup : D - input.order < L) :
    letI := fieldOfNonsquare a ha
    differentialWeightedDegree D (semanticEquation Q) < L →
    ∃ steps c out, runFuel a input D L steps (.start samples) = (.done out, c) ∧
      out.map (fun xs => JetHornerMachine.coefficientPolynomial
        (xs.map (ArithmeticMachine.decode a))) =
          (directRegularIteration Q (ArithmeticMachine.decode a input.center) P
            (D - input.order)).map CPolynomial.toPoly ∧
      (∀ xs, out = some xs → xs.length = D + 1) ∧
      steps + c.total ≤ 16777216 * RegularLiftMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) D L samples.length := by
  let := fieldOfNonsquare a ha
  intro hweight
  obtain ⟨out, sourceCost, hs, hspec, hlen, _⟩ := RegularLiftMachine.computation_runFuel_correct Q
    (ArithmeticMachine.decode a input.center) (input.coefficients.map (ArithmeticMachine.decode a))
    P (mapInput (ArithmeticMachine.decode a) input).terms points
    (samples.map (ArithmeticMachine.decode a)) hsamples (by simpa using hwidth)
    hP hQ hr hlookup hweight
  change RegularLiftMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L
    (RegularLiftMachine.fuel (mapInput (ArithmeticMachine.decode a) input) D L
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

/-- A regular jet yields the unique exhaustive-prefix candidate through this same execution.
Full residual identity checking remains a subsequent obligation. -/
theorem regular_correct (a : F) (ha : ¬IsSquare a) [Fintype (QuadraticAlgebra F a 0)]
    (input : Input F) (D L : ℕ)
    (samples : List (Pair F))
    (Q : CPoly.CMvPolynomial (input.order + 2) (QuadraticAlgebra F a 0))
    (jet : Fin (input.order + 1) → QuadraticAlgebra F a 0)
    (points : Fin L ↪ QuadraticAlgebra F a 0)
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
    IsRegularJet (semanticEquation Q) (Fin.last input.order)
      (ArithmeticMachine.decode a input.center) jet → D < ringChar (QuadraticAlgebra F a 0) →
    ∃ steps c out, ∃ P : CPolynomial (QuadraticAlgebra F a 0),
      runFuel a input D L steps (.start samples) = (.done (some out), c) ∧
      out.length = D + 1 ∧
      JetHornerMachine.coefficientPolynomial (out.map (ArithmeticMachine.decode a)) = P.toPoly ∧
      (effectiveRegularIteration Q (ArithmeticMachine.decode a input.center)
        (effectiveInitialPrefix jet) (D - input.order)).candidates = {P} ∧
      steps + c.total ≤ 16777216 * RegularLiftMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) D L samples.length := by
  let := fieldOfNonsquare a ha
  intro hP hweight hregular hchar
  obtain ⟨out, P, sourceCost, hs, hlen, hpoly, hcandidates, _⟩ :=
    RegularLiftMachine.computation_runFuel_regular Q (ArithmeticMachine.decode a input.center) jet
      (input.coefficients.map (ArithmeticMachine.decode a))
      (mapInput (ArithmeticMachine.decode a) input).terms points
      (samples.map (ArithmeticMachine.decode a)) hsamples (by simpa using hwidth) hP hQ
      hr hlookup hweight hregular hchar
  change RegularLiftMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) D L
    (RegularLiftMachine.fuel (mapInput (ArithmeticMachine.decode a) input) D L
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a))) = (.done (some out), sourceCost) at hs
  obtain ⟨steps, c, ht, hb⟩ := start_run_lowering a ha input D L _ samples (some out) sourceCost hs
  refine ⟨steps, c, out.map encode, P, ht, by simpa using hlen, ?_, hcandidates, ?_⟩
  · simpa [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode] using hpoly
  · simpa only [List.length_map] using hb

end ReedSolomon.HiddenDerivative.QuadraticRegularLiftMachine
