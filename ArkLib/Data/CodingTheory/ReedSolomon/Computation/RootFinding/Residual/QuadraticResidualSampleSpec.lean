/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.QuadraticResidualSample
public import ArkLib.Data.Polynomial.QuadraticJetHornerRefinement
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationRefinement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSampleRefinement
/-!
# Same-execution residual-sample lowering

The pointwise input/state relations are proof-only. Every source rule lowers to actual child
instructions and charged handoffs; composition preserves the original scalar endpoint. The
polynomial-facing corollary retains explicit coefficient and sparse-term representation premises.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.QuadraticResidualSample

open Polynomial MvPolynomial QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated total_add encode)

/-- Pointwise relation on materialized inputs; this map is not an executed input conversion. -/
def mapInput {K J : Type*} (f : K → J) (input : ResidualSampleMachine.Input K) :
    ResidualSampleMachine.Input J :=
  ⟨input.coefficients.map f, input.terms.map (fun t => (f t.1, t.2)),
    f input.center, f input.sample, input.order⟩

/-- Source phases are represented at the ready endpoints of the actual lowered children. -/
def represent {K F : Type*} (f : K → Pair F) :
    ResidualSampleMachine.Configuration K → Configuration F
  | .start => .start
  | .jet s => .jet (.ready (QuadraticJetHornerMachine.mapState f s))
  | .point js => .point (js.map f)
  | .pack js p => .pack (js.map f) (f p)
  | .scalar vs s => .scalar (vs.map f) (.ready (QuadraticEvaluationMachine.mapState f s))
  | .done v => .done (f v)

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Coordinate encoding after decoding preserves every actual input register. -/
theorem encode_decode_input (a : F) (input : Input F) :
    mapInput encode (mapInput (ArithmeticMachine.decode a) input) = input := by
  cases input
  simp [mapInput, List.map_map, Function.comp_def, encode, ArithmeticMachine.decode]

private theorem wrapper_total : wrapper.total = 3 := rfl

/-- Lift every actual lowered jet instruction with its additional residual wrapper. -/
theorem lift_jet_trace {a : F} {input : Input F} {n : ℕ}
    {s t : QuadraticJetHornerMachine.Configuration F} {c : Cost}
    (h : QuadraticJetHornerMachine.Trace a input.sample n s c t) :
    ∃ d, Trace a input n (.jet s) d (.jet t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a input (.jet s) = some (.jet u, c + wrapper) := by
        simp only [step, head]
      refine ⟨(c + wrapper) + d, .cons hs hd, ?_⟩
      simp only [total_add, wrapper_total, he]
      omega

/-- Lift every actual lowered scalar instruction with its additional residual wrapper. -/
theorem lift_scalar_trace {a : F} {input : Input F} (vs : List (Pair F)) {n : ℕ}
    {s t : QuadraticEvaluationMachine.Configuration F} {c : Cost}
    (h : QuadraticEvaluationMachine.Trace a vs n s c t) :
    ∃ d, Trace a input n (.scalar vs s) d (.scalar vs t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a input (.scalar vs s) = some (.scalar vs u, c + wrapper) := by
        simp only [step, head]
      refine ⟨(c + wrapper) + d, .cons hs hd, ?_⟩
      simp only [total_add, wrapper_total, he]
      omega

private theorem delegated_total (c : ArithmeticMachine.Cost) :
    (delegated c).total = c.total + 3 := by
  change c.additions + c.multiplications + c.negations + c.inversions + c.equalities +
    (c.control + 1) + (c.data + 2) + c.constants + c.output + 0 = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem base_total_add (c d : ArithmeticMachine.Cost) :
    (c + d).total = c.total + d.total := total_add (⟨c, 0⟩ : Cost) ⟨d, 0⟩

/-- Actual base addition instructions retain their own residual-level dispatch charges. -/
theorem lift_point_trace {a : F} {input : Input F} (js : List (Pair F)) {n : ℕ}
    {s t : ArithmeticMachine.Configuration F} {c : ArithmeticMachine.Cost}
    (h : ArithmeticMachine.Trace ⟨a, input.center, input.sample⟩ n s c t) :
    ∃ d, Trace a input n (.adding js ⟨a, input.center, input.sample⟩ s) d
      (.adding js ⟨a, input.center, input.sample⟩ t) ∧ d.total = c.total + 3 * n := by
  induction h with
  | nil s => exact ⟨0, .nil _, rfl⟩
  | @cons n s u t c e head tail ih =>
      obtain ⟨d, hd, he⟩ := ih
      have hs : step a input (.adding js ⟨a, input.center, input.sample⟩ s) =
          some (.adding js ⟨a, input.center, input.sample⟩ u, delegated c) := by
        simp only [step, head.step_eq]
      refine ⟨delegated c + d, .cons hs hd, ?_⟩
      rw [total_add, delegated_total, he, base_total_add]
      omega

/-- Center plus sample is computed by the concrete base addition program. -/
theorem point_lowering (a : F) (input : ResidualSampleMachine.Input (QuadraticAlgebra F a 0))
    (js : List (Pair F)) :
    ∃ n c, Trace a (mapInput encode input) n (.point js) c
      (.pack js (encode (input.center + input.sample))) ∧ n + c.total ≤ 2048 := by
  obtain ⟨n, hn, ht⟩ := ArithmeticMachine.execution_trace
    (⟨a, encode input.center, encode input.sample⟩ : ArithmeticMachine.Input F) .add
  have hp : ArithmeticMachine.specification ⟨a, encode input.center, encode input.sample⟩ .add =
      .pair (encode (input.center + input.sample)) := rfl
  rw [hp] at ht
  obtain ⟨c, hc, he⟩ := lift_point_trace (a := a) (input := mapInput encode input) js ht
  have hr := hc.trans (single (show step a (mapInput encode input)
    (.adding js ⟨a, encode input.center, encode input.sample⟩
      (.done (.pair (encode (input.center + input.sample))))) = _ from rfl))
  refine ⟨n + 1 + 1, (administrative ResidualSampleMachine.pointCost + launch) + (c + pointReturn),
    .cons rfl hr, ?_⟩
  simp only [total_add, he]
  change n + 1 + 1 + (4 + 7 + ((ArithmeticMachine.cost .add).total + 3 * n + 4)) ≤ 2048
  have hb := ArithmeticMachine.cost_total_le .add
  omega

/-- Each source transition lowers to actual instructions with the same represented endpoint. -/
theorem step_lowering {a : F} {input : ResidualSampleMachine.Input (QuadraticAlgebra F a 0)}
    {s t : ResidualSampleMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : ResidualSampleMachine.Cost} (h : ResidualSampleMachine.Step input s c t) :
    ∃ n d, Trace a (mapInput encode input) n (represent encode s) d (represent encode t) ∧
      n + d.total ≤ 2048 := by
  cases h with
  | enter => exact ⟨1, administrative ResidualSampleMachine.entryCost, single rfl, by decide⟩
  | jet h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticJetHornerMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := lift_jet_trace (input := mapInput encode input) hc
      exact ⟨n, d, hd, by omega⟩
  | jetReturn => exact ⟨1, administrative ResidualSampleMachine.jetReturnCost,
      single rfl, by decide⟩
  | point => exact point_lowering _ _ _
  | pack => exact ⟨1, administrative ResidualSampleMachine.packCost + zeroPair + valueCell,
      single rfl, by decide⟩
  | scalar h =>
      obtain ⟨n, c, hc, hb⟩ := QuadraticEvaluationMachine.step_lowering h
      obtain ⟨d, hd, he⟩ := lift_scalar_trace (input := mapInput encode input) _ hc
      exact ⟨n, d, hd, by omega⟩
  | «return» => exact ⟨1, administrative ResidualSampleMachine.returnCost, single rfl, by decide⟩

/-- Every finite original trace has a concrete lowered trace; no callee-cost premise is needed. -/
theorem trace_lowering {a : F} {input : ResidualSampleMachine.Input (QuadraticAlgebra F a 0)}
    {n : ℕ} {s t : ResidualSampleMachine.Configuration (QuadraticAlgebra F a 0)}
    {c : ResidualSampleMachine.Cost} (h : ResidualSampleMachine.Trace input n s c t) :
    ∃ k d, Trace a (mapInput encode input) k (represent encode s) d (represent encode t) ∧
      k + d.total ≤ 2048 * n := by
  induction h with
  | nil s => exact ⟨0, 0, .nil _, by decide⟩
  | cons head tail ih =>
      obtain ⟨n, c, hc, hb⟩ := step_lowering head
      obtain ⟨m, d, hd, he⟩ := ih
      refine ⟨n + m, c + d, hc.trans hd, ?_⟩
      rw [total_add]
      omega

/-- Full-start sampling returns the original decoded sample value and its actual base ledger. -/
theorem evaluation_correct (a : F) (input : Input F) :
    ∃ n c v, runFuel a input n .start = (.done v, c) ∧
      ArithmeticMachine.decode a v = EvaluationMachine.termValue
        (ResidualSampleMachine.sampleValues (mapInput (ArithmeticMachine.decode a) input))
        (mapInput (ArithmeticMachine.decode a) input).terms ∧
      n + c.total ≤ 2048 * ResidualSampleMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) := by
  have ht := ResidualSampleMachine.evaluation_trace (mapInput (ArithmeticMachine.decode a) input)
  obtain ⟨n, c, hc, hb⟩ := trace_lowering ht
  rw [encode_decode_input] at hc
  exact ⟨n, c, _, hc.runFuel_eq, rfl, hb⟩

/-- The same actual coordinate run computes the concrete residual sample. Field certification
and polynomial representation equalities are proof-only; no conversion or residual callback runs. -/
theorem evaluation_effective (a : F) (ha : ¬IsSquare a) (input : Input F)
    (Q : CPoly.CMvPolynomial (input.order + 2) (QuadraticAlgebra F a 0))
    (P : CompPoly.CPolynomial (QuadraticAlgebra F a 0))
    (hP : JetHornerMachine.coefficientPolynomial
      (input.coefficients.map (ArithmeticMachine.decode a)) = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial (mapInput (ArithmeticMachine.decode a) input).terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) :
    letI := fieldOfNonsquare a ha
    ∃ n c v, runFuel a input n .start = (.done v, c) ∧
      ArithmeticMachine.decode a v =
        (effectiveResidual Q (ArithmeticMachine.decode a input.center) P).toPoly.eval
          (ArithmeticMachine.decode a input.sample) ∧
      n + c.total ≤ 2048 * ResidualSampleMachine.fuel
        (mapInput (ArithmeticMachine.decode a) input) := by
  let := fieldOfNonsquare a ha
  obtain ⟨n, c, v, hr, hv, hb⟩ := evaluation_correct a input
  have hs := (ResidualSampleMachine.evaluation_trace
    (mapInput (ArithmeticMachine.decode a) input)).runFuel_eq
  have he := ResidualSampleMachine.evaluation_runFuel_eq_effectiveResidual Q
    (ArithmeticMachine.decode a input.center) (ArithmeticMachine.decode a input.sample) P
    (input.coefficients.map (ArithmeticMachine.decode a))
    (mapInput (ArithmeticMachine.decode a) input).terms hP hQ
  have hh := ResidualSampleMachine.Configuration.done.inj (congrArg Prod.fst (hs.symm.trans he))
  exact ⟨n, c, v, hr, hv.trans hh, hb⟩

end ReedSolomon.HiddenDerivative.QuadraticResidualSample
