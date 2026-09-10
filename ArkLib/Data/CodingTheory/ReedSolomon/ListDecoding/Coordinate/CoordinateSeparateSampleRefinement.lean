/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateSeparateSampleMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinatePreparedRefinement
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleDecoder
/-!
# Same-execution lowering with separate sample grids

Root recovery retains its raw residual samples. Only the actual collector reads guard samples.
The fixed factor includes source primitive work and applies once over the whole execution.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticSeparateSampleDecoder

open QuadraticAlgebra
local notation "qencode" => MvPolynomial.QuadraticEvaluationMachine.encode
open QuadraticPreparedDecoderMachine (Input Configuration Term encodeInput decodeInput)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Only collector states depend on the proof-side guard grid. -/
def represent (a : F) (input : PreparedDecoderMachine.Input F a)
    (guards : List (QuadraticAlgebra F a 0)) :=
  QuadraticPreparedDecoderMachine.represent a { input with samples := guards }

/-- Nested stage execution retains the complete coordinate ledger and every parent wrapper. -/
theorem roots_trace {a : F} {input : Input F} {guards : List (F × F)}
    (ri : HiddenDerivative.QuadraticStageRootsMachine.Input F) {n : ℕ}
    {s t : HiddenDerivative.QuadraticStageRootsMachine.Configuration F}
    {c : MvPolynomial.QuadraticEvaluationMachine.Cost}
    (h : HiddenDerivative.QuadraticStageRootsMachine.Trace a ri input.degree
      input.residualLength n s c t) :
    Trace a input guards n (.roots ri s) (c.total + 3 * n) (.roots ri t) := by
  induction h with
  | nil s => exact .nil _
  | @cons n s u t c d head tail ih =>
      have hs : step a input guards (.roots ri s) = some (.roots ri u, c.total + 3) := by
        simp [step, QuadraticPreparedDecoderMachine.step, head]
      convert Trace.cons hs ih using 1
      rw [MvPolynomial.QuadraticEvaluationMachine.total_add]
      omega

/-- Collector instructions retain their scalar totals and parent dispatches. -/
theorem collection_trace {a : F} {input : Input F} {guards : List (F × F)} {n c : ℕ}
    {s t : QuadraticCanonicalOutputMachine.Configuration F}
    (h : QuadraticCanonicalOutputMachine.Trace a input.order guards (input.degree + 1)
      input.dimension input.agreement input.received n s c t) :
    Trace a input guards n (.collect s) (c + 3 * n) (.collect t) := by
  induction h with
  | nil s => exact .nil _
  | @cons n s u t c d head tail ih =>
      have hs : step a input guards (.collect s) = some (.collect u, c + 3) := by
        simp [step, QuadraticPreparedDecoderMachine.step, head]
      convert Trace.cons hs ih using 1
      omega

/-- One absolute factor covers conversion, stage roots, collector work, and all failure paths. -/
theorem step_lowering (a : F) (ha : ¬IsSquare a) (input : PreparedDecoderMachine.Input F a)
    (guards : List (QuadraticAlgebra F a 0))
    {s t : PreparedDecoderMachine.Configuration F a} {c : ℕ}
    (h : SeparateSampleDecoder.step input guards ha s = some (t, c)) :
    ∃ n d, Trace a (encodeInput input) (guards.map qencode) n (represent a input guards s) d
        (represent a input guards t) ∧
      n + d ≤ 17179869184 * (c + 1) := by
  let := fieldOfNonsquare a ha
  cases s with
  | start ts => cases h; exact ⟨1, 4, single rfl, by decide⟩
  | convert s =>
      cases hs : MvPolynomial.QuadraticInputMachine.step s with
      | some p =>
          simp only [SeparateSampleDecoder.step, PreparedDecoderMachine.step, hs,
            Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hc := QuadraticPreparedInputMachine.step_lowering
            (MvPolynomial.QuadraticInputMachine.step_sound hs)
          exact ⟨1, p.2.total + 3, single (by
            simp [step, QuadraticPreparedDecoderMachine.step, represent,
            QuadraticPreparedDecoderMachine.represent, hc]), by omega⟩
      | none =>
          cases s with
          | done ts => cases h; exact ⟨1, 8, single rfl, by decide⟩
          | _ => simp [SeparateSampleDecoder.step, PreparedDecoderMachine.step, hs] at h
  | roots ri s =>
      cases hs : HiddenDerivative.StageRootsMachine.step ri input.degree input.residualLength s with
      | some p =>
          simp only [SeparateSampleDecoder.step, PreparedDecoderMachine.step, hs,
            Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          obtain ⟨n, d, hd, hb⟩ := HiddenDerivative.QuadraticStageRootsMachine.step_lowering
            a ha ri input.degree input.residualLength
            (HiddenDerivative.StageRootsMachine.step_sound hs)
          have ht := roots_trace (input := encodeInput input) (guards := guards.map qencode) _ hd
          exact ⟨n, d.total + 3 * n, ht, by omega⟩
      | none =>
          cases s with
          | done out =>
              cases out <;> cases h
              · exact ⟨1, 3, single rfl, by decide⟩
              · exact ⟨1, 4, single rfl, by decide⟩
          | _ => simp [SeparateSampleDecoder.step, PreparedDecoderMachine.step, hs] at h
  | collect s =>
      cases hs : CanonicalOutputMachine.step input.order guards (input.degree + 1)
          input.dimension input.agreement input.received s with
      | some p =>
          simp only [SeparateSampleDecoder.step, PreparedDecoderMachine.step, hs,
            Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have ht : CanonicalOutputMachine.Trace input.order guards (input.degree + 1)
              input.dimension input.agreement input.received 1 s p.2 p.1 := by
            simpa using CanonicalOutputMachine.Trace.cons (CanonicalOutputMachine.step_sound hs)
              (CanonicalOutputMachine.Trace.nil p.1)
          obtain ⟨n, d, hd, hb⟩ := QuadraticCanonicalOutputMachine.trace_lowering ht
          have hc := collection_trace (input := encodeInput input) (guards := guards.map qencode) hd
          exact ⟨n, d + 3 * n, hc, by omega⟩
      | none =>
          cases s with
          | done out => cases h; exact ⟨1, 4, single rfl, by decide⟩
          | _ => simp [SeparateSampleDecoder.step, PreparedDecoderMachine.step, hs] at h
  | emit out => cases h; exact ⟨1, 3, single rfl, by decide⟩
  | done out => simp [SeparateSampleDecoder.step, PreparedDecoderMachine.step] at h

/-- The factor multiplies total source instructions plus work once over the entire execution. -/
theorem trace_lowering (a : F) (ha : ¬IsSquare a) (input : PreparedDecoderMachine.Input F a)
    (guards : List (QuadraticAlgebra F a 0))
    {n c : ℕ} {s t : PreparedDecoderMachine.Configuration F a}
    (h : SeparateSampleDecoder.Trace input guards ha n s c t) :
    ∃ steps d, Trace a (encodeInput input) (guards.map qencode) steps (represent a input guards s) d
        (represent a input guards t) ∧
      steps + d ≤ 17179869184 * (n + c) := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, d, hd, hb⟩ := step_lowering a ha input guards head
      obtain ⟨m, e, he, hm⟩ := ih
      exact ⟨n + m, d + e, hd.trans he, by omega⟩

/-- Recover the exact original trace of a bounded interpreter prefix. -/
theorem source_runFuel_refines (a : F) (ha : ¬IsSquare a)
    (input : PreparedDecoderMachine.Input F a) (guards : List (QuadraticAlgebra F a 0))
    (fuel : ℕ) (s : PreparedDecoderMachine.Configuration F a) :
    ∃ n ≤ fuel, SeparateSampleDecoder.Trace input guards ha n s
      (SeparateSampleDecoder.runFuel input guards ha fuel s).2
      (SeparateSampleDecoder.runFuel input guards ha fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, .nil _⟩
  | succ fuel ih =>
      cases hs : SeparateSampleDecoder.step input guards ha s with
      | none => exact ⟨0, Nat.zero_le _, by
          simpa [SeparateSampleDecoder.runFuel, hs] using SeparateSampleDecoder.Trace.nil s⟩
      | some p =>
          obtain ⟨n, hn, ht⟩ := ih p.1
          exact ⟨n + 1, by omega, by
            simpa [SeparateSampleDecoder.runFuel, hs] using SeparateSampleDecoder.Trace.cons hs ht⟩

/-- A completed source run gives actual raw-pair execution at a fixed numerical budget. -/
theorem start_run_budget (a : F) (ha : ¬IsSquare a) (input : Input F) (guards : List (F × F))
    (ts : List (Term F)) (fuel sourceCost : ℕ) (out : Option (List (List F)))
    (hs : SeparateSampleDecoder.runFuel (decodeInput a input)
      (guards.map (ArithmeticMachine.decode a)) ha fuel (.start ts) = (.done out, sourceCost)) :
    ∃ c, runFuel a input guards (17179869184 * (fuel + sourceCost)) (.start ts) = (.done out, c) ∧
      c ≤ 17179869184 * (fuel + sourceCost) := by
  obtain ⟨n, hn, ht⟩ := source_runFuel_refines a ha (decodeInput a input)
    (guards.map (ArithmeticMachine.decode a)) fuel (.start ts)
  rw [hs] at ht
  obtain ⟨steps, c, hc, hb⟩ := trace_lowering a ha (decodeInput a input)
    (guards.map (ArithmeticMachine.decode a)) ht
  rw [QuadraticPreparedDecoderMachine.encode_decode_input] at hc
  have hg : (guards.map (ArithmeticMachine.decode a)).map qencode = guards := by
    simp [List.map_map, Function.comp_def,
    MvPolynomial.QuadraticEvaluationMachine.encode, ArithmeticMachine.decode]
  rw [hg] at hc
  have hsteps : steps ≤ 17179869184 * (fuel + sourceCost) := by omega
  have he := hc.runFuel_done (17179869184 * (fuel + sourceCost) - steps)
  rw [Nat.add_sub_of_le hsteps] at he
  exact ⟨c, he, by omega⟩

end ReedSolomon.ListDecoding.QuadraticSeparateSampleDecoder
