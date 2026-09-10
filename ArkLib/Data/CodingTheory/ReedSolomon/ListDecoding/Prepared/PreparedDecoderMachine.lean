/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.QuadraticInputSemantics
public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputMachine
/-!
# Root enumeration and output collection over a prepared quadratic field

This driver consumes the actual base-field interpolant and already materialized field/sample
data. It executes coefficient allocation, root enumeration and canonical base-field collection
one child instruction at a time. Every child ledger and caller dispatch is retained. Field setup
and interpolation search precede this driver; their costs are not supplied by callbacks here.
Extension arithmetic lowering and whole-instance bounds are separate refinement obligations.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.PreparedDecoderMachine

abbrev Term := MvPolynomial.EvaluationMachine.Term
abbrev Element (F : Type*) [Zero F] (a : F) := QuadraticAlgebra F a 0

/-- Materialized field/sample data and ordinary integer decoder parameters. -/
structure Input (F : Type*) [Zero F] (a : F) where
  alphabet : List (Element F a)
  samples : List (Element F a)
  received : List (F × F)
  order : ℕ
  degree : ℕ
  residualLength : ℕ
  dimension : ℕ
  agreement : ℕ

/-- Actual intermediate values are stored once and passed as immutable child inputs. -/
inductive Configuration (F : Type*) [Zero F] (a : F) where
  | start (terms : List (Term F))
  | convert (inner : MvPolynomial.QuadraticInputMachine.Configuration F a)
  | roots (input : HiddenDerivative.StageRootsMachine.Input (Element F a))
      (inner : HiddenDerivative.StageRootsMachine.Configuration (Element F a))
  | collect (inner : CanonicalOutputMachine.Configuration F a 0)
  | emit (output : Option (List (List F)))
  | done (output : Option (List (List F)))

variable {F : Type*} [Field F] [DecidableEq F] {a : F}

/-- Sparse equation and alphabet roots form a bounded-size input record, not a bulk conversion. -/
def rootInput (input : Input F a) (terms : List (Term (Element F a))) :
    HiddenDerivative.StageRootsMachine.Input (Element F a) :=
  ⟨input.alphabet, terms, input.order⟩

/-- Dispatch one actual child instruction or one fixed-size handoff. The nonsquare proof
only certifies the existing computable field dictionary and is erased from execution. -/
def step (input : Input F a) (ha : ¬IsSquare a) :
    Configuration F a → Option (Configuration F a × ℕ) :=
  letI := QuadraticAlgebra.fieldOfNonsquare a ha
  fun state => match state with
  | .start ts => some (.convert (.scan ts []), 4)
  | .convert s => match MvPolynomial.QuadraticInputMachine.step s with
      | some (t, c) => some (.convert t, c.total + 3)
      | none => match s with
          | .done ts => some (.roots (rootInput input ts) (.start input.samples), 8)
          | _ => none
  | .roots ri s => match HiddenDerivative.StageRootsMachine.step ri input.degree
      input.residualLength s with
      | some (t, c) => some (.roots ri t, HiddenDerivative.StageRootsMachine.totalCost c + 3)
      | none => match s with
          | .done none => some (.emit none, 3)
          | .done (some records) => some (.collect (.start records), 4)
          | _ => none
  | .collect s => match CanonicalOutputMachine.step input.order input.samples
      (input.degree + 1) input.dimension input.agreement input.received s with
      | some (t, c) => some (.collect t, c + 3)
      | none => match s with
          | .done out => some (.emit (some out), 4)
          | _ => none
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- Exact executable transitions and retained primitive totals of all three children. -/
inductive Trace (input : Input F a) (ha : ¬IsSquare a) :
    ℕ → Configuration F a → ℕ → Configuration F a → Prop where
  | nil (s) : Trace input ha 0 s 0 s
  | cons {n s u t c e} (head : step input ha s = some (u, c))
      (tail : Trace input ha n u e t) : Trace input ha (n + 1) s (c + e) t

/-- Composition retains the sum of every executed child and wrapper charge. -/
theorem Trace.trans {input : Input F a} {ha : ¬IsSquare a} {n m : ℕ}
    {s u t : Configuration F a} {c e : ℕ}
    (h : Trace input ha n s c u) (h' : Trace input ha m u e t) :
    Trace input ha (n + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Fuel advances the prepared driver; no callee is replaced by its declarative result. -/
def runFuel (input : Input F a) (ha : ¬IsSquare a) :
    ℕ → Configuration F a → Configuration F a × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step input ha s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel input ha n t; (r.1, c + r.2)

/-- Every interpreted prefix has the identical operational trace and charge. -/
theorem runFuel_refines (input : Input F a) (ha : ¬IsSquare a)
    (fuel : ℕ) (s : Configuration F a) :
    ∃ n ≤ fuel, Trace input ha n s (runFuel input ha fuel s).2
      (runFuel input ha fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, .nil _⟩
  | succ fuel ih =>
      cases hs : step input ha s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some p =>
          obtain ⟨n, hn, ht⟩ := ih p.1
          exact ⟨n + 1, by omega, by simpa [runFuel, hs] using Trace.cons hs ht⟩

/-- Completed actual traces determine execution with any surplus host fuel. -/
theorem Trace.runFuel_done {input : Input F a} {ha : ¬IsSquare a}
    {n : ℕ} {s : Configuration F a} {c : ℕ} {out : Option (List (List F))}
    (h : Trace input ha n s c (.done out)) (extra : ℕ) :
    runFuel input ha (n + extra) s = (.done out, c) := by
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

/-- Coefficient-conversion instructions retain their own ledger and parent dispatches. -/
theorem lift_conversion (input : Input F a) (ha : ¬IsSquare a)
    {n : ℕ} {s t : MvPolynomial.QuadraticInputMachine.Configuration F a}
    {c : QuadraticAlgebra.ArithmeticMachine.Cost}
    (h : MvPolynomial.QuadraticInputMachine.Trace n s c t) :
    Trace input ha n (.convert s) (c.total + 3 * n) (.convert t) := by
  induction h with
  | nil s => exact Trace.nil _
  | @cons n s u t c e head tail ih =>
      have hs : step input ha (.convert s) = some (.convert u, c.total + 3) := by
        simp only [step, head.step_eq]
      convert Trace.cons hs ih using 1
      rw [scalar_total_add]
      omega

/-- Root enumeration advances its actual chain, center and jet children under this driver. -/
theorem lift_roots (input : Input F a) (ha : ¬IsSquare a)
    (ri : HiddenDerivative.StageRootsMachine.Input (Element F a))
    {n : ℕ} {s t : HiddenDerivative.StageRootsMachine.Configuration (Element F a)}
    {c : HiddenDerivative.StageRootsMachine.Cost} :
    letI := QuadraticAlgebra.fieldOfNonsquare a ha
    HiddenDerivative.StageRootsMachine.Trace ri input.degree input.residualLength n s c t →
      Trace input ha n (.roots ri s)
        (HiddenDerivative.StageRootsMachine.totalCost c + 3 * n) (.roots ri t) := by
  let := QuadraticAlgebra.fieldOfNonsquare a ha
  intro h
  induction h with
  | nil s => exact Trace.nil _
  | @cons n s u t c e head tail ih =>
      have hs : step input ha (.roots ri s) =
          some (.roots ri u, HiddenDerivative.StageRootsMachine.totalCost c + 3) := by
        simp only [step, head.step_eq]
      convert Trace.cons hs ih using 1
      rw [HiddenDerivative.StageRootsMachine.total_add]
      omega

/-- Guard, descent, agreement and output instructions retain all their nested costs. -/
theorem lift_collection (input : Input F a) (ha : ¬IsSquare a)
    {n c : ℕ} {s t : CanonicalOutputMachine.Configuration F a 0}
    (h : CanonicalOutputMachine.Trace input.order input.samples (input.degree + 1)
      input.dimension input.agreement input.received n s c t) :
    Trace input ha n (.collect s) (c + 3 * n) (.collect t) := by
  induction h with
  | nil s => exact Trace.nil _
  | @cons n s u t c e head tail ih =>
      have hs : step input ha (.collect s) = some (.collect u, c + 3) := by
        simp only [step, head.step_eq]
      convert Trace.cons hs ih using 1
      omega

/-- Actual completed child traces compose without any assumed callback or declarative output. -/
theorem pipeline_trace (input : Input F a) (ha : ¬IsSquare a)
    (ts : List (Term F)) (ets : List (Term (Element F a)))
    (records : List (HiddenDerivative.StageRootsMachine.Record (Element F a)))
    (out : List (List F)) (nc nr no co : ℕ)
    (cc : QuadraticAlgebra.ArithmeticMachine.Cost) (cr : HiddenDerivative.StageRootsMachine.Cost)
    (hc : MvPolynomial.QuadraticInputMachine.Trace nc (.scan ts []) cc (.done ets)) :
    letI := QuadraticAlgebra.fieldOfNonsquare a ha
    HiddenDerivative.StageRootsMachine.Trace (rootInput input ets) input.degree
      input.residualLength nr (.start input.samples) cr (.done (some records)) →
    CanonicalOutputMachine.Trace input.order input.samples (input.degree + 1)
      input.dimension input.agreement input.received no (.start records) co (.done out) →
    Trace input ha (nc + nr + no + 5) (.start ts)
      (cc.total + HiddenDerivative.StageRootsMachine.totalCost cr + co + 3 * (nc + nr + no) + 23)
      (.done (some out)) := by
  let := QuadraticAlgebra.fieldOfNonsquare a ha
  intro hr ho
  have ht := Trace.cons (input := input) (ha := ha) (show step input ha (.start ts) = _ from rfl)
    ((lift_conversion input ha hc).trans
      (Trace.cons (show step input ha (.convert (.done ets)) = _ from rfl)
        ((lift_roots input ha (rootInput input ets) hr).trans
          (Trace.cons (show step input ha (.roots (rootInput input ets)
            (.done (some records))) = _ from rfl)
            ((lift_collection input ha ho).trans
              (Trace.cons (show step input ha (.collect (.done out)) = _ from rfl)
                (Trace.cons (show step input ha (.emit (some out)) = _ from rfl)
                  (Trace.nil _))))))))
  convert ht using 1 <;> omega

end ReedSolomon.ListDecoding.PreparedDecoderMachine
