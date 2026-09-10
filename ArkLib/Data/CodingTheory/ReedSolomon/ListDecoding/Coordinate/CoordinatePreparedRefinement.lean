/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinatePreparedMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.StagesRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateOutputRefinement
/-!
# Same-execution lowering of the complete prepared driver

Every original instruction is refined by actual coordinate instructions. The total bound charges
both source instructions and source work, retaining the existing base-field collector arithmetic.
No execution callback, chosen output, or runtime bulk conversion is assumed.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticPreparedDecoderMachine

open QuadraticAlgebra
local notation "qencode" => MvPolynomial.QuadraticEvaluationMachine.encode

variable {F : Type*} [Field F] [DecidableEq F]

/-- Logical encoding of materialized input roots; ordinary fields and rows are unchanged. -/
def encodeInput {a : F} (input : PreparedDecoderMachine.Input F a) : Input F :=
  ⟨input.alphabet.map qencode, input.samples.map qencode, input.received, input.order,
    input.degree, input.residualLength, input.dimension, input.agreement⟩

/-- Logical decoding used only in correctness statements for already supplied raw pairs. -/
def decodeInput (a : F) (input : Input F) : PreparedDecoderMachine.Input F a :=
  ⟨input.alphabet.map (ArithmeticMachine.decode a), input.samples.map (ArithmeticMachine.decode a),
    input.received, input.order, input.degree, input.residualLength,
    input.dimension, input.agreement⟩

omit [DecidableEq F] in
/-- Every supplied pair and ordinary parameter survives the proof-side round trip. -/
theorem encode_decode_input (a : F) (input : Input F) :
    encodeInput (decodeInput a input) = input := by
  cases input
  simp [encodeInput, decodeInput, List.map_map, Function.comp_def,
    MvPolynomial.QuadraticEvaluationMachine.encode, ArithmeticMachine.decode]

/-- Suspended states retain their actual stage input and their actual collector parameters. -/
def represent (a : F) (input : PreparedDecoderMachine.Input F a) :
    PreparedDecoderMachine.Configuration F a → Configuration F
  | .start ts => .start ts
  | .convert s => .convert (QuadraticPreparedInputMachine.represent s)
  | .roots ri s => .roots (HiddenDerivative.QuadraticStageRootsMachine.mapInput qencode ri)
      (HiddenDerivative.QuadraticStageRootsMachine.represent a qencode ri input.degree s)
  | .collect s => .collect (QuadraticCanonicalOutputMachine.represent a input.order input.samples
      (input.degree + 1) input.dimension input.agreement input.received s)
  | .emit out => .emit out
  | .done out => .done out

/-- Nested stage execution retains the complete coordinate ledger and every parent wrapper. -/
theorem roots_trace {a : F} {input : Input F}
    (ri : HiddenDerivative.QuadraticStageRootsMachine.Input F) {n : ℕ}
    {s t : HiddenDerivative.QuadraticStageRootsMachine.Configuration F}
    {c : MvPolynomial.QuadraticEvaluationMachine.Cost}
    (h : HiddenDerivative.QuadraticStageRootsMachine.Trace a ri input.degree
      input.residualLength n s c t) :
    Trace a input n (.roots ri s) (c.total + 3 * n) (.roots ri t) := by
  induction h with
  | nil s => exact .nil _
  | @cons n s u t c d head tail ih =>
      have hs : step a input (.roots ri s) = some (.roots ri u, c.total + 3) := by
        simp [step, head]
      convert Trace.cons hs ih using 1
      rw [MvPolynomial.QuadraticEvaluationMachine.total_add]
      omega

/-- Collector instructions retain their scalar totals and parent dispatches. -/
theorem collection_trace {a : F} {input : Input F} {n c : ℕ}
    {s t : QuadraticCanonicalOutputMachine.Configuration F}
    (h : QuadraticCanonicalOutputMachine.Trace a input.order input.samples (input.degree + 1)
      input.dimension input.agreement input.received n s c t) :
    Trace a input n (.collect s) (c + 3 * n) (.collect t) := by
  induction h with
  | nil s => exact .nil _
  | @cons n s u t c d head tail ih =>
      have hs : step a input (.collect s) = some (.collect u, c + 3) := by
        simp [step, head]
      convert Trace.cons hs ih using 1
      omega

/-- One absolute factor covers conversion, stage roots, collector work, and all failure paths. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a) (input : PreparedDecoderMachine.Input F a)
    {s t : PreparedDecoderMachine.Configuration F a} {c : ℕ}
    (h : PreparedDecoderMachine.step input ha s = some (t, c)) :
    ∃ n d, Trace a (encodeInput input) n (represent a input s) d (represent a input t) ∧
      n + d ≤ 17179869184 * (c + 1) := by
  let := fieldOfNonsquare a ha
  cases s with
  | start ts => cases h; exact ⟨1, 4, single rfl, by decide⟩
  | convert s =>
      cases hs : MvPolynomial.QuadraticInputMachine.step s with
      | some p =>
          simp only [PreparedDecoderMachine.step, hs,
            Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hc := QuadraticPreparedInputMachine.step_lowering
            (MvPolynomial.QuadraticInputMachine.step_sound hs)
          exact ⟨1, p.2.total + 3, single (by simp [step, represent, hc]), by omega⟩
      | none =>
          cases s with
          | done ts => cases h; exact ⟨1, 8, single rfl, by decide⟩
          | _ => simp [PreparedDecoderMachine.step, hs] at h
  | roots ri s =>
      cases hs : HiddenDerivative.StageRootsMachine.step ri input.degree input.residualLength s with
      | some p =>
          simp only [PreparedDecoderMachine.step, hs,
            Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          obtain ⟨n, d, hd, hb⟩ := HiddenDerivative.QuadraticStageRootsMachine.step_lowering
            a ha ri input.degree input.residualLength
            (HiddenDerivative.StageRootsMachine.step_sound hs)
          have ht := roots_trace (input := encodeInput input) _ hd
          exact ⟨n, d.total + 3 * n, ht, by omega⟩
      | none =>
          cases s with
          | done out =>
              cases out <;> cases h
              · exact ⟨1, 3, single rfl, by decide⟩
              · exact ⟨1, 4, single rfl, by decide⟩
          | _ => simp [PreparedDecoderMachine.step, hs] at h
  | collect s =>
      cases hs : CanonicalOutputMachine.step input.order input.samples (input.degree + 1)
          input.dimension input.agreement input.received s with
      | some p =>
          simp only [PreparedDecoderMachine.step, hs,
            Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have ht : CanonicalOutputMachine.Trace input.order input.samples (input.degree + 1)
              input.dimension input.agreement input.received 1 s p.2 p.1 := by
            simpa using CanonicalOutputMachine.Trace.cons (CanonicalOutputMachine.step_sound hs)
              (CanonicalOutputMachine.Trace.nil p.1)
          obtain ⟨n, d, hd, hb⟩ := QuadraticCanonicalOutputMachine.trace_lowering ht
          have hc := collection_trace (input := encodeInput input) hd
          exact ⟨n, d + 3 * n, hc, by omega⟩
      | none =>
          cases s with
          | done out => cases h; exact ⟨1, 4, single rfl, by decide⟩
          | _ => simp [PreparedDecoderMachine.step, hs] at h
  | emit out => cases h; exact ⟨1, 3, single rfl, by decide⟩
  | done out => simp [PreparedDecoderMachine.step] at h

/-- The factor multiplies total source instructions plus work once over the entire execution. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a) (input : PreparedDecoderMachine.Input F a)
    {n c : ℕ} {s t : PreparedDecoderMachine.Configuration F a}
    (h : PreparedDecoderMachine.Trace input ha n s c t) :
    ∃ steps d, Trace a (encodeInput input) steps (represent a input s) d (represent a input t) ∧
      steps + d ≤ 17179869184 * (n + c) := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, d, hd, hb⟩ := step_lowering a ha input head
      obtain ⟨m, e, he, hm⟩ := ih
      exact ⟨n + m, d + e, hd.trans he, by omega⟩

/-- Raw prepared input executes to exactly the completed base-field output or failure. -/
theorem start_run_lowering (a : F) (ha : ¬IsSquare a) (input : Input F)
    (ts : List (Term F)) (fuel sourceCost : ℕ) (out : Option (List (List F)))
    (hs : PreparedDecoderMachine.runFuel (decodeInput a input) ha fuel (.start ts) =
      (.done out, sourceCost)) :
    ∃ steps c, runFuel a input steps (.start ts) = (.done out, c) ∧
      steps + c ≤ 17179869184 * (fuel + sourceCost) := by
  obtain ⟨n, hn, ht⟩ := PreparedDecoderMachine.runFuel_refines
    (decodeInput a input) ha fuel (.start ts)
  rw [hs] at ht
  obtain ⟨steps, c, hc, hb⟩ := trace_lowering a ha (decodeInput a input) ht
  rw [encode_decode_input] at hc
  exact ⟨steps, c, hc.runFuel_eq, by omega⟩

end ReedSolomon.ListDecoding.QuadraticPreparedDecoderMachine
