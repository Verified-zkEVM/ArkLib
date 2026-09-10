/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.Machine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.Semantics
public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticSystemRefinement
public import ArkLib.Data.Matrix.QuadraticBackSubstitutionRefinement
/-!
# Same-execution coordinate coefficient recovery

Source phases lower to actual system and back-substitution instructions with charged seed
allocation. Raw input representations, degree bounds and distinct supplied samples identify
every emitted coefficient. The same execution satisfies a bound from original input structure.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualCoefficientMachine

open Polynomial Matrix QuadraticAlgebra CompPoly PolynomialDifferential
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

abbrev mapInput := @QuadraticResidualBatch.mapInput
abbrev mapRows {K J : Type*} (f : K → J) (rows : List (ForwardEchelonMachine.Row K)) :=
  QuadraticSelectionMachine.mapRows f rows
abbrev mapPivots {K J : Type*} (f : K → J) (ps : List (ForwardEchelonMachine.Pivot K)) :=
  QuadraticForwardEchelonMachine.mapPivots f ps

/-- Pointwise source representation preserves all partial phases and retained input records. -/
def represent {K F : Type*} (a : F) (f : K → Pair F) (input : ResidualCoefficientMachine.Input K) :
    ResidualCoefficientMachine.Configuration K → Configuration F
  | .start xs => .start (xs.map f)
  | .system s => .system (mapInput f input) (QuadraticResidualSystemMachine.represent f input s)
  | .initialize ps rs n zs => .initialize (mapPivots f ps) (mapRows f rs) n (zs.map f)
  | .backsub s => .backsub (QuadraticBackSubstitutionMachine.enter a
      (QuadraticBackSubstitutionMachine.mapState f s))
  | .emit out => .emit (out.map (List.map f))
  | .done out => .done (out.map (List.map f))

variable {F : Type*} [Field F] [DecidableEq F]

/-- System instructions use the retained payload and add this caller's wrapper. -/
theorem system_trace {a : F} {input payload : Input F} {L n : ℕ}
    {s t : QuadraticResidualSystemMachine.Configuration F} {c : Cost}
    (h : QuadraticResidualSystemMachine.Trace a payload L n s c t) :
    ∃ d, Trace a input L n (.system payload s) d (.system payload t) ∧
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

/-- Every back-substitution instruction retains all nested work and pays outer dispatch. -/
theorem backsub_trace {a : F} {input : Input F} {L n : ℕ}
    {s t : QuadraticBackSubstitutionMachine.Configuration F} {c : Cost}
    (h : QuadraticBackSubstitutionMachine.Trace a n s c t) :
    ∃ d, Trace a input L n (.backsub s) d (.backsub t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Each source phase has its identical represented successor, including failure returns. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (input : ResidualCoefficientMachine.Input (QuadraticAlgebra F a 0)) (L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : ResidualCoefficientMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : ResidualCoefficientMachine.Cost}, ResidualCoefficientMachine.Step input L s c t →
      ∃ n d, Trace a (mapInput encode input) L n (represent a encode input s) d
        (represent a encode input t) ∧ n + d.total ≤ 1048576 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | enter => exact ⟨1, administrative ResidualCoefficientMachine.entryCost + allocation 4,
      single rfl, by decide⟩
  | system h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticResidualSystemMachine.step_lowering a ha input L h
      obtain ⟨d, hd, he⟩ := system_trace (input := mapInput encode input) hc
      exact ⟨n, d, hd, by omega⟩
  | systemReturn =>
      exact ⟨1, administrative ResidualCoefficientMachine.systemReturnCost, single rfl, by decide⟩
  | systemFailed =>
      exact ⟨1, administrative ResidualCoefficientMachine.returnCost, single rfl, by decide⟩
  | «initialize» =>
      exact ⟨1, administrative ResidualCoefficientMachine.initializeCost + seedExtra,
        single rfl, by decide⟩
  | initializeDone =>
      exact ⟨1, administrative ResidualCoefficientMachine.initializeDoneCost, single rfl, by decide⟩
  | backsub h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticBackSubstitutionMachine.step_lowering a ha h
      obtain ⟨d, hd, he⟩ := backsub_trace (input := mapInput encode input) (L := L) hc
      exact ⟨n, d, hd, by omega⟩
  | returned => exact ⟨1, administrative ResidualCoefficientMachine.returnCost + allocation 1,
      single rfl, by decide⟩
  | inconsistent =>
      exact ⟨1, administrative ResidualCoefficientMachine.returnCost, single rfl, by decide⟩
  | rejected =>
      exact ⟨1, administrative ResidualCoefficientMachine.returnCost, single rfl, by decide⟩
  | emit => exact ⟨1, administrative ResidualCoefficientMachine.emitCost, single rfl, by decide⟩

/-- Same-endpoint traces compose with every nested charge and allocation retained. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (input : ResidualCoefficientMachine.Input (QuadraticAlgebra F a 0)) (L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : ResidualCoefficientMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : ResidualCoefficientMachine.Cost}, ResidualCoefficientMachine.Trace input L n s c t →
      ∃ k d, Trace a (mapInput encode input) L k (represent a encode input s) d
        (represent a encode input t) ∧ k + d.total ≤ 1048576 * n := by
  let := fieldOfNonsquare a ha
  intro n s t c h
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering a ha input L head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Any finite source run reaches the exact represented endpoint with bounded actual work. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a)
    (input : ResidualCoefficientMachine.Input (QuadraticAlgebra F a 0)) (L fuel : ℕ)
    (s : ResidualCoefficientMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ k d, runFuel a (mapInput encode input) L k (represent a encode input s) =
      (represent a encode input (ResidualCoefficientMachine.runFuel input L fuel s).1, d) ∧
      k + d.total ≤ 1048576 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := ResidualCoefficientMachine.runFuel_refines input L fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering a ha input L ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- A consistent raw input executes to a width-L vector solving its sampled equations. -/
theorem computation_correct (a : F) (ha : ¬IsSquare a) (input : Input F) (L : ℕ)
    (samples : List (Pair F)) :
    letI := fieldOfNonsquare a ha
    (∃ x, PivotSelectionMachine.Satisfies (VandermondeMachine.rowsSpec L
      (ResidualBatchMachine.outputSpec (mapInput (ArithmeticMachine.decode a) input)
        (samples.map (ArithmeticMachine.decode a)))) x) →
    ∃ k c out, runFuel a input L k (.start samples) = (.done (some out), c) ∧
      out.length = L ∧ PivotSelectionMachine.Satisfies (VandermondeMachine.rowsSpec L
        (ResidualBatchMachine.outputSpec (mapInput (ArithmeticMachine.decode a) input)
          (samples.map (ArithmeticMachine.decode a))))
        (fun i => (out.map (ArithmeticMachine.decode a)).getD i 0) ∧
      k + c.total ≤ 1048576 * ResidualCoefficientMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) L samples.length := by
  let := fieldOfNonsquare a ha
  intro hconsistent
  obtain ⟨out, sourceCost, hs, hlen, hsol, _⟩ :=
    ResidualCoefficientMachine.computation_runFuel (mapInput (ArithmeticMachine.decode a) input) L
      (samples.map (ArithmeticMachine.decode a)) hconsistent
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha (mapInput (ArithmeticMachine.decode a) input) L
    (ResidualCoefficientMachine.fuel (mapInput (ArithmeticMachine.decode a) input) L
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hi := QuadraticResidualBatch.encode_decode_input a input
  change mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input at hi
  rw [hi] at hr
  have hp : (samples.map (ArithmeticMachine.decode a)).map encode = samples := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [represent, hp, Option.map_some] at hr
  have hout : (out.map encode).map (ArithmeticMachine.decode a) = out := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨k, c, out.map encode, hr, by simpa using hlen, ?_, ?_⟩
  · simpa only [hout] using hsol
  · simpa only [List.length_map] using hb

/-- Actual coordinate execution recovers every residual coefficient under the original input
representations, strict degree bound and distinct supplied sample points. -/
theorem coefficients_correct (a : F) (ha : ¬IsSquare a) (input : Input F) (D L : ℕ)
    (samples : List (Pair F))
    (Q : CPoly.CMvPolynomial (input.order + 2) (QuadraticAlgebra F a 0))
    (P : CPolynomial (QuadraticAlgebra F a 0)) (points : Fin L ↪ QuadraticAlgebra F a 0)
    (hsamples : samples.map (ArithmeticMachine.decode a) = List.ofFn (fun i => points i))
    (hP : JetHornerMachine.coefficientPolynomial
      (input.coefficients.map (ArithmeticMachine.decode a)) = P.toPoly)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial
      (mapInput (ArithmeticMachine.decode a) input).terms =
        MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hdegree : P.natDegree ≤ D) :
    letI := fieldOfNonsquare a ha
    differentialWeightedDegree D (semanticEquation Q) < L →
    ∃ k c out, runFuel a input L k (.start samples) = (.done (some out), c) ∧ out.length = L ∧
      (∀ i : Fin L, (out.map (ArithmeticMachine.decode a)).getD i.val 0 =
        (effectiveResidual Q (ArithmeticMachine.decode a input.center) P).coeff i.val) ∧
      k + c.total ≤ 1048576 * ResidualCoefficientMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) L samples.length := by
  let := fieldOfNonsquare a ha
  intro hweight
  obtain ⟨out, sourceCost, hs, hlen, hcoeff, _⟩ :=
    ResidualCoefficientMachine.computation_runFuel_coefficients Q
      (ArithmeticMachine.decode a input.center) P
      (input.coefficients.map (ArithmeticMachine.decode a))
      (mapInput (ArithmeticMachine.decode a) input).terms points
      (samples.map (ArithmeticMachine.decode a)) hsamples hP hQ hdegree hweight
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha (mapInput (ArithmeticMachine.decode a) input) L
    (ResidualCoefficientMachine.fuel (mapInput (ArithmeticMachine.decode a) input) L
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a)))
  change ResidualCoefficientMachine.runFuel (mapInput (ArithmeticMachine.decode a) input) L
    (ResidualCoefficientMachine.fuel (mapInput (ArithmeticMachine.decode a) input) L
      (samples.map (ArithmeticMachine.decode a)).length)
    (.start (samples.map (ArithmeticMachine.decode a))) = (.done (some out), sourceCost) at hs
  rw [hs] at hr
  have hi := QuadraticResidualBatch.encode_decode_input a input
  change mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input at hi
  rw [hi] at hr
  have hp : (samples.map (ArithmeticMachine.decode a)).map encode = samples := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [represent, hp, Option.map_some] at hr
  have hout : (out.map encode).map (ArithmeticMachine.decode a) = out := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨k, c, out.map encode, hr, by simpa using hlen, ?_, ?_⟩
  · simpa only [hout] using hcoeff
  · simpa only [List.length_map] using hb

end ReedSolomon.HiddenDerivative.QuadraticResidualCoefficientMachine
