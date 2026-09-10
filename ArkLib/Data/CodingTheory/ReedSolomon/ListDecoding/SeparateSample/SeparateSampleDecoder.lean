/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Prepared.PreparedDecoderMachine
/-!
# Prepared decoding with distinct recovery and guard sample lists

The existing driver and all child programs are reused. Only the collector dispatch receives a
separate materialized guard grid. Root recovery continues to use the original residual grid.
This permits base-field centers and jets without requiring the entire residual polynomial to
be determined by base-field samples. Every delegated instruction and handoff remains charged.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SeparateSampleDecoder

open PreparedDecoderMachine (Input Configuration Element Term rootInput)

variable {F : Type*} [Field F] [DecidableEq F] {a : F}

/-- Override only the collector's sample register; root-recovery dispatch is unchanged. -/
def step (input : Input F a) (guardSamples : List (Element F a)) (ha : ¬IsSquare a) :
    Configuration F a → Option (Configuration F a × ℕ)
  | s@(.collect _) => PreparedDecoderMachine.step { input with samples := guardSamples } ha s
  | s => PreparedDecoderMachine.step input ha s

/-- Choosing the original grid preserves every original transition and its exact charge. -/
theorem step_same (input : Input F a) (ha : ¬IsSquare a) (s : Configuration F a) :
    step input input.samples ha s = PreparedDecoderMachine.step input ha s := by
  cases s <;> rfl

/-- Exact traces for the distinct-grid driver. -/
inductive Trace (input : Input F a) (guardSamples : List (Element F a)) (ha : ¬IsSquare a) :
    ℕ → Configuration F a → ℕ → Configuration F a → Prop where
  | nil (s) : Trace input guardSamples ha 0 s 0 s
  | cons {n s u t c e} (head : step input guardSamples ha s = some (u, c))
      (tail : Trace input guardSamples ha n u e t) :
      Trace input guardSamples ha (n + 1) s (c + e) t

/-- Composition retains all delegated and wrapper charges. -/
theorem Trace.trans {input : Input F a} {guardSamples : List (Element F a)} {ha : ¬IsSquare a}
    {n m : ℕ} {s u t : Configuration F a} {c e : ℕ}
    (h : Trace input guardSamples ha n s c u) (h' : Trace input guardSamples ha m u e t) :
    Trace input guardSamples ha (n + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Fuel advances the same child instructions, not their declarative specifications. -/
def runFuel (input : Input F a) (guardSamples : List (Element F a)) (ha : ¬IsSquare a) :
    ℕ → Configuration F a → Configuration F a × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step input guardSamples ha s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel input guardSamples ha n t; (r.1, c + r.2)

/-- Equal grids give the identical original interpreter result, including partial states/costs. -/
theorem runFuel_same (input : Input F a) (ha : ¬IsSquare a) (n : ℕ) (s : Configuration F a) :
    runFuel input input.samples ha n s = PreparedDecoderMachine.runFuel input ha n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [runFuel, PreparedDecoderMachine.runFuel, step_same]
      cases PreparedDecoderMachine.step input ha s with
      | none => rfl
      | some p => simp only [ih]

/-- Completed execution remains fixed under surplus fuel. -/
theorem Trace.runFuel_done {input : Input F a} {guardSamples : List (Element F a)}
    {ha : ¬IsSquare a} {n : ℕ} {s : Configuration F a} {c : ℕ} {out : Option (List (List F))}
    (h : Trace input guardSamples ha n s c (.done out)) (extra : ℕ) :
    runFuel input guardSamples ha (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head]
      dsimp only
      rw [ih he]

private theorem scalar_total_add (c e : QuadraticAlgebra.ArithmeticMachine.Cost) :
    (c + e).total = c.total + e.total := by
  change (c.additions + e.additions) + (c.multiplications + e.multiplications) +
    (c.negations + e.negations) + (c.inversions + e.inversions) +
    (c.equalities + e.equalities) + (c.control + e.control) + (c.data + e.data) +
    (c.constants + e.constants) + (c.output + e.output) = _
  simp only [QuadraticAlgebra.ArithmeticMachine.Cost.total]
  omega

/-- Scalar conversion is the identical child execution with its parent wrapper. -/
theorem lift_conversion (input : Input F a) (guardSamples : List (Element F a))
    (ha : ¬IsSquare a) {n : ℕ} {s t : MvPolynomial.QuadraticInputMachine.Configuration F a}
    {c : QuadraticAlgebra.ArithmeticMachine.Cost}
    (h : MvPolynomial.QuadraticInputMachine.Trace n s c t) :
    Trace input guardSamples ha n (.convert s) (c.total + 3 * n) (.convert t) := by
  induction h with
  | nil s => exact Trace.nil _
  | @cons n s u t c e head tail ih =>
      have hs : step input guardSamples ha (.convert s) = some (.convert u, c.total + 3) := by
        simp only [step, PreparedDecoderMachine.step, head.step_eq]
      convert Trace.cons hs ih using 1
      rw [scalar_total_add]
      omega

/-- The recovery grid remains the original input grid throughout root enumeration. -/
theorem lift_roots (input : Input F a) (guardSamples : List (Element F a)) (ha : ¬IsSquare a)
    (ri : HiddenDerivative.StageRootsMachine.Input (Element F a))
    {n : ℕ} {s t : HiddenDerivative.StageRootsMachine.Configuration (Element F a)}
    {c : HiddenDerivative.StageRootsMachine.Cost} :
    letI := QuadraticAlgebra.fieldOfNonsquare a ha
    HiddenDerivative.StageRootsMachine.Trace ri input.degree input.residualLength n s c t →
      Trace input guardSamples ha n (.roots ri s)
        (HiddenDerivative.StageRootsMachine.totalCost c + 3 * n) (.roots ri t) := by
  let := QuadraticAlgebra.fieldOfNonsquare a ha
  intro h
  induction h with
  | nil s => exact Trace.nil _
  | @cons n s u t c e head tail ih =>
      have hs : step input guardSamples ha (.roots ri s) =
          some (.roots ri u, HiddenDerivative.StageRootsMachine.totalCost c + 3) := by
        simp only [step, PreparedDecoderMachine.step, head.step_eq]
      convert Trace.cons hs ih using 1
      rw [HiddenDerivative.StageRootsMachine.total_add]
      omega

/-- Only collector guards use the distinct grid; acceptance/descent algorithms are unchanged. -/
theorem lift_collection (input : Input F a) (guardSamples : List (Element F a))
    (ha : ¬IsSquare a) {n c : ℕ} {s t : CanonicalOutputMachine.Configuration F a 0}
    (h : CanonicalOutputMachine.Trace input.order guardSamples (input.degree + 1)
      input.dimension input.agreement input.received n s c t) :
    Trace input guardSamples ha n (.collect s) (c + 3 * n) (.collect t) := by
  induction h with
  | nil s => exact Trace.nil _
  | @cons n s u t c e head tail ih =>
      have hs : step input guardSamples ha (.collect s) = some (.collect u, c + 3) := by
        simp only [step, PreparedDecoderMachine.step, head.step_eq]
      convert Trace.cons hs ih using 1
      omega

/-- The three actual children compose with recovery and guard samples kept separate. -/
theorem pipeline_trace (input : Input F a) (guardSamples : List (Element F a)) (ha : ¬IsSquare a)
    (ts : List (Term F)) (ets : List (Term (Element F a)))
    (records : List (HiddenDerivative.StageRootsMachine.Record (Element F a)))
    (out : List (List F)) (nc nr no co : ℕ)
    (cc : QuadraticAlgebra.ArithmeticMachine.Cost) (cr : HiddenDerivative.StageRootsMachine.Cost)
    (hc : MvPolynomial.QuadraticInputMachine.Trace nc (.scan ts []) cc (.done ets)) :
    letI := QuadraticAlgebra.fieldOfNonsquare a ha
    HiddenDerivative.StageRootsMachine.Trace (rootInput input ets) input.degree
      input.residualLength nr (.start input.samples) cr (.done (some records)) →
    CanonicalOutputMachine.Trace input.order guardSamples (input.degree + 1)
      input.dimension input.agreement input.received no (.start records) co (.done out) →
    Trace input guardSamples ha (nc + nr + no + 5) (.start ts)
      (cc.total + HiddenDerivative.StageRootsMachine.totalCost cr + co +
        3 * (nc + nr + no) + 23) (.done (some out)) := by
  let := QuadraticAlgebra.fieldOfNonsquare a ha
  intro hr ho
  have ht := Trace.cons (input := input) (guardSamples := guardSamples) (ha := ha)
    (show step input guardSamples ha (.start ts) = _ from rfl)
    ((lift_conversion input guardSamples ha hc).trans
      (Trace.cons (show step input guardSamples ha (.convert (.done ets)) = _ from rfl)
        ((lift_roots input guardSamples ha (rootInput input ets) hr).trans
          (Trace.cons (show step input guardSamples ha (.roots (rootInput input ets)
            (.done (some records))) = _ from rfl)
            ((lift_collection input guardSamples ha ho).trans
              (Trace.cons (show step input guardSamples ha (.collect (.done out)) = _ from rfl)
                (Trace.cons (show step input guardSamples ha (.emit (some out)) = _ from rfl)
                  (Trace.nil _))))))))
  convert ht using 1 <;> omega

end ReedSolomon.ListDecoding.SeparateSampleDecoder
