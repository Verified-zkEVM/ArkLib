/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticBatch
public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticResidualSampleSpec
/-!
# Same-execution coordinate batch refinement

Pointwise input and output maps express representation only. Actual execution retains each
constructed payload and samples every point, preserving order and duplicates through allocated
pair/list cells. The source trace is lowered without any assumed child-cost callback.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualBatch

open Polynomial MvPolynomial QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost total_add encode)
open QuadraticResidualSample (administrative wrapper)

/-- Proof-only representation of the four immutable batch input registers. -/
def mapInput {K J : Type*} (f : K → J) (input : ResidualBatchMachine.Input K) :
    ResidualBatchMachine.Input J :=
  ⟨input.coefficients.map f, input.terms.map (fun t => (f t.1, t.2)), f input.center, input.order⟩

/-- Proof-only point/value representation; runtime allocates entries individually. -/
def mapEntries {K J : Type*} (f : K → J) (xs : List (K × K)) : List (J × J) :=
  xs.map (fun p => (f p.1, f p.2))

/-- Represent source call states with the exact immutable payload constructed at entry. -/
def represent {K F : Type*} (f : K → Pair F) (input : ResidualBatchMachine.Input K) :
    ResidualBatchMachine.Configuration K → Configuration F
  | .start ps => .start (ps.map f)
  | .scan ps rev => .scan (ps.map f) (mapEntries f rev)
  | .enter u ps rev => .enter (f u) (ps.map f) (mapEntries f rev)
  | .call u ps rev s => .call (f u) (ps.map f) (mapEntries f rev)
      (ResidualBatchMachine.sampleInput (mapInput f input) (f u))
      (QuadraticResidualSample.represent f s)
  | .pack u v ps rev => .pack (f u) (f v) (ps.map f) (mapEntries f rev)
  | .save p ps rev => .save (f p.1, f p.2) (ps.map f) (mapEntries f rev)
  | .reverse ps out => .reverse (mapEntries f ps) (mapEntries f out)
  | .done out => .done (mapEntries f out)

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Actual coordinate input registers survive their proof-only round trip. -/
theorem encode_decode_input (a : F) (input : Input F) :
    mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input := by
  cases input
  simp [mapInput, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

omit [DecidableEq F] in
/-- Decoding encoded point/value entries preserves the ordered source list exactly. -/
theorem decode_encode_entries (a : F) (xs : List (QuadraticAlgebra F a 0 ×
    QuadraticAlgebra F a 0)) :
    mapEntries (ArithmeticMachine.decode a) (mapEntries encode xs) = xs := by
  simp [mapEntries, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

/-- Lift every actual sample instruction using the retained payload and an outer wrapper. -/
theorem lift_sample_trace {a : F} {input : Input F} (u : Pair F) (ps : List (Pair F))
    (rev : List (Entry F)) (payload : QuadraticResidualSample.Input F) {n : ℕ}
    {s t : QuadraticResidualSample.Configuration F} {c : Cost}
    (h : QuadraticResidualSample.Trace a payload n s c t) :
    ∃ d, Trace a input n (.call u ps rev payload s) d (.call u ps rev payload t) ∧
      d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s v t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a input (.call u ps rev payload s) =
          some (.call u ps rev payload v, c + wrapper) := by simp only [step, head]
      refine ⟨(c + wrapper) + d, .cons hs hd, ?_⟩
      simp only [total_add, he]
      change c.total + 3 + (e.total + 3 * n) = c.total + e.total + 3 * (n + 1)
      omega

/-- Each original batch transition has an actual concrete simulation to its represented target. -/
theorem step_lowering {a : F} {input : ResidualBatchMachine.Input (QuadraticAlgebra F a 0)}
    {s t : ResidualBatchMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : ResidualBatchMachine.Cost} (h : ResidualBatchMachine.Step input s c t) :
    ∃ n d, Trace a (mapInput encode input) n (represent encode input s) d
      (represent encode input t) ∧ n + d.total ≤ 8192 := by
  cases h with
  | start => exact ⟨1, administrative ResidualBatchMachine.startCost, single rfl, by decide⟩
  | take => exact ⟨1, administrative ResidualBatchMachine.takeCost, single rfl, by decide⟩
  | enter => exact ⟨1, administrative ResidualBatchMachine.entryCost + inputRecord,
      single rfl, by decide⟩
  | @call u ps rev s t c h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticResidualSample.step_lowering h
      obtain ⟨d, hd, he⟩ := lift_sample_trace (input := mapInput encode input)
        (encode u) (ps.map encode) (mapEntries encode rev)
        (ResidualBatchMachine.sampleInput (mapInput encode input) (encode u)) hc
      exact ⟨n, d, hd, by omega⟩
  | «return» => exact ⟨1, administrative ResidualBatchMachine.returnCost, single rfl, by decide⟩
  | pack => exact ⟨1, administrative ResidualBatchMachine.pairCost, single rfl, by decide⟩
  | save => exact ⟨1, administrative ResidualBatchMachine.saveCost, single rfl, by decide⟩
  | beginReverse => exact ⟨1, administrative ResidualBatchMachine.beginReverseCost,
      single rfl, by decide⟩
  | reverse => exact ⟨1, administrative ResidualBatchMachine.reverseCost, single rfl, by decide⟩
  | emit => exact ⟨1, administrative ResidualBatchMachine.emitCost, single rfl, by decide⟩

/-- Source traces compose into real batch traces with all nested wrapper costs retained. -/
theorem trace_lowering {a : F} {input : ResidualBatchMachine.Input (QuadraticAlgebra F a 0)}
    {n : ℕ} {s t : ResidualBatchMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : ResidualBatchMachine.Cost} (h : ResidualBatchMachine.Trace input n s c t) :
    ∃ k d, Trace a (mapInput encode input) k (represent encode input s) d
      (represent encode input t) ∧ k + d.total ≤ 8192 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Starting with actual coordinate points returns the original ordered sample list, including
all duplicates, with the real base ledger bounded by the source structural fuel. -/
theorem batch_correct (a : F) (input : Input F) (points : List (Pair F)) :
    ∃ n c out, runFuel a input n (.start points) = (.done out, c) ∧
      mapEntries (ArithmeticMachine.decode a) out =
        ResidualBatchMachine.outputSpec (mapInput (ArithmeticMachine.decode a) input)
          (points.map (ArithmeticMachine.decode a)) ∧
      n + c.total ≤ 8192 * ResidualBatchMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) points.length := by
  let decoded := mapInput (ArithmeticMachine.decode a) input
  let ps := points.map (ArithmeticMachine.decode a)
  have hr := ResidualBatchMachine.batch_runFuel decoded ps
  obtain ⟨k, hk, ht⟩ := ResidualBatchMachine.runFuel_refines decoded
    (ResidualBatchMachine.fuel decoded ps.length) (.start ps)
  rw [hr] at ht
  obtain ⟨n, c, hc, hb⟩ := trace_lowering ht
  have hp : ps.map encode = points := by
    simp [ps, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]
  change Trace a (mapInput encode (mapInput (ArithmeticMachine.decode a) input)) n _ _ _ at hc
  rw [encode_decode_input] at hc
  simp only [represent, hp] at hc
  refine ⟨n, c, _, hc.runFuel_eq, decode_encode_entries a _, ?_⟩
  have he := hb.trans (Nat.mul_le_mul_left 8192 hk)
  simpa only [ps, List.length_map] using he

/-- The decoded emitted pairs are concrete residual samples under explicit representations.
Only proof-side field certification is used; input construction and matrix solving remain open. -/
theorem batch_effective (a : F) (ha : ¬IsSquare a) (input : Input F) (points : List (Pair F))
    (Q : CPoly.CMvPolynomial (input.order + 2) (QuadraticAlgebra F a 0))
    (P : CompPoly.CPolynomial (QuadraticAlgebra F a 0))
    (hP : JetHornerMachine.coefficientPolynomial
      (input.coefficients.map (ArithmeticMachine.decode a)) = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial (mapInput (ArithmeticMachine.decode a) input).terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) :
    letI := fieldOfNonsquare a ha
    ∃ n c out, runFuel a input n (.start points) = (.done out, c) ∧
      mapEntries (ArithmeticMachine.decode a) out =
        (points.map (ArithmeticMachine.decode a)).map (fun u =>
          (u, (effectiveResidual Q (ArithmeticMachine.decode a input.center) P).toPoly.eval u)) ∧
      n + c.total ≤ 8192 * ResidualBatchMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) points.length := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, c, out, hr, he, hb⟩ := batch_correct a input points
  refine ⟨n, c, out, hr, he.trans ?_, hb⟩
  apply List.map_congr_left
  intro u hu
  congr 1
  exact ResidualBatchMachine.sampleValue_eq_effectiveResidual Q
    (ArithmeticMachine.decode a input.center) u P
    (input.coefficients.map (ArithmeticMachine.decode a))
    (mapInput (ArithmeticMachine.decode a) input).terms hP hQ

end ReedSolomon.HiddenDerivative.QuadraticResidualBatch
