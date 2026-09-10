/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticSystemMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticBatchSpec
public import ArkLib.Data.Matrix.QuadraticVandermondeRefinement
public import ArkLib.Data.Matrix.QuadraticForwardEchelonRefinement
/-!
# Same-execution coordinate residual-system refinement

Each source transition lowers to actual retained child instructions with its exact represented
endpoint. Complete raw-coordinate execution produces the same echelon equations, row count and
solution set as sampling and Vandermonde construction. The work bound uses only source structural
fuel from the supplied input and dimensions. Representation maps are proof-only.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualSystemMachine

open Matrix QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)

abbrev mapInput := @QuadraticResidualBatch.mapInput
abbrev mapRows {K J : Type*} (f : K → J) (rows : List (ForwardEchelonMachine.Row K)) :=
  QuadraticSelectionMachine.mapRows f rows
abbrev mapPivots {K J : Type*} (f : K → J) (ps : List (ForwardEchelonMachine.Pivot K)) :=
  QuadraticForwardEchelonMachine.mapPivots f ps

/-- Represent every source phase with actual child states and its exact retained batch payload. -/
def represent {K F : Type*} (f : K → Pair F) (input : ResidualSystemMachine.Input K) :
    ResidualSystemMachine.Configuration K → Configuration F
  | .start ps => .start (ps.map f)
  | .sample s => .sample (mapInput f input) (QuadraticResidualBatch.represent f input s)
  | .matrix s => .matrix (.ready (QuadraticVandermondeMachine.mapState f s))
  | .echelon s => .echelon (QuadraticForwardEchelonMachine.enter
      (QuadraticForwardEchelonMachine.mapState f s))
  | .done ps rs => .done (mapPivots f ps) (mapRows f rs)
  | .rejected => .rejected

variable {F : Type*} [Field F] [DecidableEq F]

/-- The sampling child uses its retained input and retains every instruction's charge. -/
theorem sample_trace {a : F} {input payload : Input F} {L n : ℕ}
    {s t : QuadraticResidualBatch.Configuration F} {c : Cost}
    (h : QuadraticResidualBatch.Trace a payload n s c t) :
    ∃ d, Trace a input L n (.sample payload s) d (.sample payload t) ∧
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

/-- Every matrix-construction instruction retains its charge and pays outer dispatch. -/
theorem matrix_trace {a : F} {input : Input F} {L n : ℕ}
    {s t : QuadraticVandermondeMachine.Configuration F} {c : Cost}
    (h : QuadraticVandermondeMachine.Trace a L n s c t) :
    ∃ d, Trace a input L n (.matrix s) d (.matrix t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Echelon instructions retain every nested cost and add this driver's wrapper. -/
theorem echelon_trace {a : F} {input : Input F} {L n : ℕ}
    {s t : QuadraticForwardEchelonMachine.Configuration F} {c : Cost}
    (h : QuadraticForwardEchelonMachine.Trace a n s c t) :
    ∃ d, Trace a input L n (.echelon s) d (.echelon t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      refine ⟨c + wrapper + d, .cons ?_ hd, ?_⟩
      · simp only [step, head]
      · rw [total_add, total_add, he, total_add]
        change c.total + 3 + (e.total + 3 * n) = _
        omega

/-- Source steps lower to identical represented endpoints using only actual child steps. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a)
    (input : ResidualSystemMachine.Input (QuadraticAlgebra F a 0)) (L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {s t : ResidualSystemMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : ResidualSystemMachine.Cost}, ResidualSystemMachine.Step input L s c t →
      ∃ n d, Trace a (mapInput encode input) L n (represent encode input s) d
        (represent encode input t) ∧ n + d.total ≤ 262144 := by
  let := fieldOfNonsquare a ha
  intro s t c h
  cases h with
  | start => exact ⟨1, administrative ResidualSystemMachine.startCost + inputRecord,
      single rfl, by decide⟩
  | sample h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticResidualBatch.step_lowering h
      obtain ⟨d, hd, he⟩ := sample_trace (input := mapInput encode input) (L := L) hc
      exact ⟨n, d, hd, by omega⟩
  | samples =>
      exact ⟨1, administrative ResidualSystemMachine.sampleReturnCost, single rfl, by decide⟩
  | matrix h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticVandermondeMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := matrix_trace (input := mapInput encode input) hc
      exact ⟨n, d, hd, by omega⟩
  | rows =>
      exact ⟨1, administrative ResidualSystemMachine.matrixReturnCost, single rfl, by decide⟩
  | echelon h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticForwardEchelonMachine.step_lowering a ha h
      obtain ⟨d, hd, he⟩ := echelon_trace (input := mapInput encode input) (L := L) hc
      exact ⟨n, d, hd, by omega⟩
  | done => exact ⟨1, administrative ResidualSystemMachine.returnCost, single rfl, by decide⟩
  | reject => exact ⟨1, administrative ResidualSystemMachine.returnCost, single rfl, by decide⟩

/-- Concrete source traces compose without omitting nested work or handoff charges. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a)
    (input : ResidualSystemMachine.Input (QuadraticAlgebra F a 0)) (L : ℕ) :
    letI := fieldOfNonsquare a ha
    ∀ {n : ℕ} {s t : ResidualSystemMachine.Configuration (QuadraticAlgebra F a 0)}
      {c : ResidualSystemMachine.Cost}, ResidualSystemMachine.Trace input L n s c t →
      ∃ k d, Trace a (mapInput encode input) L k (represent encode input s) d
        (represent encode input t) ∧ k + d.total ≤ 262144 * n := by
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

/-- Any finite source run reaches its exact represented endpoint with bounded base work. -/
theorem run_lowering (a : F) (ha : ¬IsSquare a)
    (input : ResidualSystemMachine.Input (QuadraticAlgebra F a 0)) (L fuel : ℕ)
    (s : ResidualSystemMachine.Configuration (QuadraticAlgebra F a 0)) :
    letI := fieldOfNonsquare a ha
    ∃ k d, runFuel a (mapInput encode input) L k (represent encode input s) =
      (represent encode input (ResidualSystemMachine.runFuel input L fuel s).1, d) ∧
      k + d.total ≤ 262144 * fuel := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, hn, ht⟩ := ResidualSystemMachine.runFuel_refines input L fuel s
  obtain ⟨k, d, hd, hb⟩ := trace_lowering a ha input L ht
  exact ⟨k, d, hd.runFuel_eq, hb.trans (Nat.mul_le_mul_left _ hn)⟩

/-- Raw coordinate input executes to solution-equivalent echelon equations with the physical
row count preserved. The bound uses only input structure, point count and supplied width. -/
theorem computation_correct (a : F) (ha : ¬IsSquare a) (input : Input F) (L : ℕ)
    (points : List (Pair F)) :
    letI := fieldOfNonsquare a ha
    ∃ k c ps rest, runFuel a input L k (.start points) = (.done ps rest, c) ∧
      ForwardEchelonMachine.Echelon L 0 (mapPivots (ArithmeticMachine.decode a) ps)
        (mapRows (ArithmeticMachine.decode a) rest) ∧
      ps.length + rest.length = points.length ∧
      (∀ x, ForwardEchelonMachine.Solutions (mapPivots (ArithmeticMachine.decode a) ps)
        (mapRows (ArithmeticMachine.decode a) rest) x ↔
          PivotSelectionMachine.Satisfies (VandermondeMachine.rowsSpec L
            (ResidualBatchMachine.outputSpec (mapInput (ArithmeticMachine.decode a) input)
              (points.map (ArithmeticMachine.decode a)))) x) ∧
      k + c.total ≤ 262144 * ResidualSystemMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) L points.length := by
  let := fieldOfNonsquare a ha
  obtain ⟨ps, rest, sourceCost, hs, he, hcount, hsol, _⟩ :=
    ResidualSystemMachine.computation_runFuel (mapInput (ArithmeticMachine.decode a) input) L
      (points.map (ArithmeticMachine.decode a))
  obtain ⟨k, c, hr, hb⟩ := run_lowering a ha (mapInput (ArithmeticMachine.decode a) input) L
    (ResidualSystemMachine.fuel (mapInput (ArithmeticMachine.decode a) input) L
      (points.map (ArithmeticMachine.decode a)).length)
    (.start (points.map (ArithmeticMachine.decode a)))
  rw [hs] at hr
  have hi := QuadraticResidualBatch.encode_decode_input a input
  change mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input at hi
  rw [hi] at hr
  have hp : (points.map (ArithmeticMachine.decode a)).map encode = points := by
    simp [List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  simp only [represent, hp] at hr
  have hps : mapPivots (ArithmeticMachine.decode a) (mapPivots encode ps) = ps := by
    simp [mapPivots, QuadraticForwardEchelonMachine.mapPivots, QuadraticSelectionMachine.mapRow,
      List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  have hrs : mapRows (ArithmeticMachine.decode a) (mapRows encode rest) = rest := by
    simp [mapRows, QuadraticSelectionMachine.mapRows, QuadraticSelectionMachine.mapRow,
      List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  refine ⟨k, c, mapPivots encode ps, mapRows encode rest, hr, ?_, ?_, ?_, ?_⟩
  · simpa only [hps, hrs] using he
  · simpa [mapPivots, QuadraticForwardEchelonMachine.mapPivots,
      mapRows, QuadraticSelectionMachine.mapRows] using hcount
  · simpa only [hps, hrs] using hsol
  · simpa only [List.length_map] using hb

end ReedSolomon.HiddenDerivative.QuadraticResidualSystemMachine
