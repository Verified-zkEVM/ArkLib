/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetPreparationMachine
/-!
# Closed change of center

The machine negates the supplied center, forms `D+1`, and executes the simultaneous Hasse-jet
Horner machine at that point. It then executes initial-jet preparation on the resulting ascending
list to obtain descending coefficients. The jet has exactly `D+1` entries, so this second call
reverses the list without padding or rejection. Every callee transition, handoff and emission is
charged; scalar negation and the preparation machine's constants have separate cost fields.

Inputs are already materialized. Physical width is a supplied representation invariant, not a
free list-length scan. Bulk polynomial operations and list specifications occur only in proofs.
The inherited primitive models share retained registers and treat host fuel bookkeeping and
scalar bit costs separately. This subroutine makes no base-field descent or full-decoder claim.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.CenterShiftMachine

open Polynomial

/-- Preserve all callee categories and separately count scalar negation. -/
@[ext] structure Cost where
  machine : JetHornerMachine.Cost
  constants : ℕ
  negations : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b ↦
  ⟨a.machine + b.machine, a.constants + b.constants, a.negations + b.negations⟩⟩

@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.machine + b.machine, a.constants + b.constants, a.negations + b.negations⟩ := rfl

/-- Total primitive charge, including retained constants and explicit negation. -/
def Cost.total (c : Cost) : ℕ := c.machine.total + c.constants + c.negations

/-- Embed every jet-machine cost field without discarding callee emissions. -/
def jetCost (c : JetHornerMachine.Cost) : Cost := ⟨c, 0, 0⟩
/-- Embed every preparation field, including scalar constants and callee emission. -/
def preparationCost (c : JetPreparationMachine.Cost) : Cost := ⟨c.machine, c.constants, 0⟩
/-- One outer dispatch reads and writes a retained callee state root. -/
def wrapperCost (n : ℕ) : Cost := ⟨⟨0, 0, n, 2 * n, 0, 0⟩, 0, 0⟩
/-- Read inputs, negate the center, compute `D+1`, and write point and callee state. -/
def entryCost : Cost := ⟨⟨0, 0, 1, 5, 1, 0⟩, 0, 1⟩
/-- Read the jet result and degree, and initialize the preparation state. -/
def handoffCost : Cost := ⟨⟨0, 0, 1, 3, 0, 0⟩, 0, 0⟩
/-- Read the preparation result and emit the final tagged list handle. -/
def returnCost : Cost := ⟨⟨0, 0, 1, 2, 0, 1⟩, 0, 0⟩
/-- Fixed outer charges, in addition to all delegated transitions. -/
def overheadCost : Cost := ⟨⟨0, 0, 3, 10, 1, 1⟩, 0, 1⟩

/-- Materialized descending coefficients and the supplied target physical degree. -/
structure Input (F : Type*) where
  coefficients : List F
  center : F
  degree : ℕ

/-- Suspended configurations expose both actual callees. -/
inductive Configuration (F : Type*) where
  | start
  | jet (point : F) (state : JetHornerMachine.Configuration F)
  | prepare (state : JetPreparationMachine.Configuration F)
  | done (result : Option (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [CommRing F]

/-- Independent rules permit only one callee transition at a time. -/
inductive Step (input : Input F) : Configuration F → Cost → Configuration F → Prop where
  | enter : Step input .start entryCost
      (.jet (-input.center) (.initialize input.coefficients (input.degree + 1) []))
  | jet {x s t c} (h : JetHornerMachine.Step x s c t) :
      Step input (.jet x s) (jetCost c + wrapperCost 1) (.jet x t)
  | handoff {x js} : Step input (.jet x (.done js)) handoffCost
      (.prepare (.start input.degree js))
  | prepare {s t c} (h : JetPreparationMachine.Step s c t) :
      Step input (.prepare s) (preparationCost c + wrapperCost 1) (.prepare t)
  | return {out} : Step input (.prepare (.done out)) returnCost (.done out)

/-- Literal dispatch negates once and never calls a bulk evaluator or reversal. -/
def step (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start => some
      (.jet (-input.center) (.initialize input.coefficients (input.degree + 1) []), entryCost)
  | .jet x s => match JetHornerMachine.step x s with
      | some (t, c) => some (.jet x t, jetCost c + wrapperCost 1)
      | none => match s with
          | .done js => some (.prepare (.start input.degree js), handoffCost)
          | _ => none
  | .prepare s => match JetPreparationMachine.step s with
      | some (t, c) => some (.prepare t, preparationCost c + wrapperCost 1)
      | none => match s with
          | .done out => some (.done out, returnCost)
          | _ => none
  | .done _ => none

/-- Independent rules match dispatch and the complete primitive charge. -/
theorem Step.step_eq {input : Input F} {s t : Configuration F} {c : Cost}
    (h : Step input s c t) : step input s = some (t, c) := by
  cases h with
  | jet h => simp [step, h.step_eq]
  | prepare h => simp [step, h.step_eq]
  | _ => rfl

/-- Every dispatch branch is justified by an independent rule. -/
theorem step_sound {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step input s = some (t, c)) : Step input s c t := by
  cases s with
  | start => cases h; exact Step.enter
  | done out => simp [step] at h
  | jet x s =>
      cases hs : JetHornerMachine.step x s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.jet (JetHornerMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.handoff
  | prepare s =>
      cases hs : JetPreparationMachine.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.prepare (JetPreparationMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.return

/-- Actual finite execution accumulates every nested charge. -/
inductive Trace (input : Input F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input 0 s 0 s
  | cons {n s u t c d} (head : Step input s c u) (tail : Trace input n u d t) :
      Trace input (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [cost_add, JetHornerMachine.cost_add, Nat.add_assoc]

/-- Composition preserves exact trace length and accumulated primitive cost. -/
theorem Trace.trans {input : Input F} {n m : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Trace input n s c t) (h' : Trace input m t d u) :
    Trace input (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- Fuel exhaustion exposes the suspended machine and never fabricates a returned list. -/
def runFuel (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input n t; (result.1, c + result.2)

/-- Every interpreter result refines a trace with the same nested costs. -/
theorem runFuel_refines (input : Input F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input n s (runFuel input fuel s).2 (runFuel input fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace fuel recovers its endpoint and cost. -/
theorem Trace.runFuel_eq {input : Input F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace input n s c t) : runFuel input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Lift actual Horner transitions, retaining all fields and one wrapper per step. -/
theorem lift_jet_trace (input : Input F) (x : F) {n : ℕ}
    {s t : JetHornerMachine.Configuration F} {c : JetHornerMachine.Cost}
    (h : JetHornerMachine.Trace x n s c t) :
    Trace input n (.jet x s) (jetCost c + wrapperCost n) (.jet x t) := by
  induction h with
  | nil s => simpa [jetCost, wrapperCost] using Trace.nil (input := input) (.jet x s)
  | @cons n s u t c d head tail ih =>
      have heq : (jetCost c + wrapperCost 1) + (jetCost d + wrapperCost n) =
          jetCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [jetCost, wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.jet head) ih

/-- Lift actual preparation transitions, retaining constants and callee output charges. -/
theorem lift_preparation_trace (input : Input F) {n : ℕ}
    {s t : JetPreparationMachine.Configuration F} {c : JetPreparationMachine.Cost}
    (h : JetPreparationMachine.Trace n s c t) :
    Trace input n (.prepare s) (preparationCost c + wrapperCost n) (.prepare t) := by
  induction h with
  | nil s => simpa [preparationCost, wrapperCost] using Trace.nil (input := input) (.prepare s)
  | @cons n s u t c d head tail ih =>
      have heq : (preparationCost c + wrapperCost 1) + (preparationCost d + wrapperCost n) =
          preparationCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [preparationCost, wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.prepare head) ih

/-- Full simultaneous-jet fuel, including initialization and its scalar emissions. -/
def jetFuel (input : Input F) : ℕ :=
  (input.coefficients.length + 1) * (2 * (input.degree + 1) + 3)
/-- Full reversal-callee fuel, including its capacity successor and tagged emission. -/
def preparationFuel (input : Input F) : ℕ := input.degree + 5
/-- Exact composite fuel. -/
def fuel (input : Input F) : ℕ := jetFuel input + preparationFuel input + 3
/-- Exact composite cost; the complete jet has no missing coefficients to pad. -/
def cost (input : Input F) : Cost :=
  jetCost (JetHornerMachine.evaluationCost input.coefficients.length (input.degree + 1)) +
    wrapperCost (jetFuel input) +
    preparationCost (JetPreparationMachine.successCost input.degree (input.degree + 1)) +
    wrapperCost (preparationFuel input) + overheadCost

/-- Mathematical ascending jet specification; dispatch executes the actual callee instead. -/
def jetSpec (input : Input F) : List F :=
  JetHornerMachine.jetLoop (-input.center) input.coefficients (List.replicate (input.degree + 1) 0)
/-- Mathematical descending output specification. -/
def outputSpec (input : Input F) : List F :=
  JetPreparationMachine.prepared input.degree (jetSpec input)

@[simp] theorem jetSpec_length (input : Input F) : (jetSpec input).length = input.degree + 1 := by
  simp [jetSpec]

/-- The preparation call reverses the full jet without inserting any padding zeros. -/
theorem outputSpec_eq_reverse (input : Input F) : outputSpec input = (jetSpec input).reverse := by
  simp [outputSpec, JetPreparationMachine.prepared]

/-- Physical output width is fixed independently of leading zero coefficients. -/
theorem outputSpec_length (input : Input F) : (outputSpec input).length = input.degree + 1 := by
  simp [outputSpec_eq_reverse]

private theorem full_jet_trace (input : Input F) :
    JetHornerMachine.Trace (-input.center) (jetFuel input)
      (.initialize input.coefficients (input.degree + 1) [])
      (JetHornerMachine.evaluationCost input.coefficients.length (input.degree + 1))
      (.done (jetSpec input)) := by
  have hi := JetHornerMachine.initialization_trace (-input.center) input.coefficients []
    (input.degree + 1)
  simp only [List.append_nil] at hi
  have h := hi.trans (JetHornerMachine.loop_trace (-input.center) input.coefficients
    (List.replicate (input.degree + 1) 0))
  simp only [List.length_replicate] at h
  convert h using 1
  · dsimp [jetFuel]
    ring
  · ext <;> simp only [JetHornerMachine.evaluationCost, JetHornerMachine.initializationCost,
      JetHornerMachine.loopCost, JetHornerMachine.cost_add] <;> ring
  · rfl

/-- Complete trace is composed solely from individual callee and outer transitions. -/
theorem shift_trace (input : Input F) :
    Trace input (fuel input) .start (cost input) (.done (some (outputSpec input))) := by
  have hj := lift_jet_trace input (-input.center) (full_jet_trace input)
  have hp := lift_preparation_trace input
    (JetPreparationMachine.preparation_trace input.degree (jetSpec input) (by simp))
  simp only [jetSpec_length] at hp
  have ht := Trace.cons Step.enter (hj.trans (Trace.cons Step.handoff
    (hp.trans (Trace.cons Step.return (Trace.nil _)))))
  convert ht using 1
  · dsimp [fuel, preparationFuel]
    omega
  · ext <;> simp only [cost, preparationFuel, entryCost, handoffCost, returnCost, overheadCost,
      cost_zero, cost_add, JetHornerMachine.cost_zero, JetHornerMachine.cost_add] <;> omega
  · rfl

/-- Actual execution returns the full descending list with exact nested costs. -/
theorem shift_runFuel (input : Input F) :
    runFuel input (fuel input) .start = (.done (some (outputSpec input)), cost input) :=
  (shift_trace input).runFuel_eq

private theorem represented_degree_le (input : Input F)
    (hwidth : input.coefficients.length = input.degree + 1) :
    (JetHornerMachine.coefficientPolynomial input.coefficients).natDegree ≤ input.degree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hc := Polynomial.CoefficientList.ascendingPolynomial_coeff input.coefficients.reverse j
  simp only [Polynomial.CoefficientList.ascendingPolynomial, List.reverse_reverse] at hc
  rw [hc]
  have hlen : input.coefficients.reverse.length ≤ j := by simp [hwidth]; omega
  simp only [List.getD, List.getElem?_eq_none hlen, Option.getD_none]

/-- The reversed full jet is precisely the Taylor translation, including coefficients above `D`. -/
theorem outputSpec_polynomial (input : Input F)
    (hwidth : input.coefficients.length = input.degree + 1) :
    JetHornerMachine.coefficientPolynomial (outputSpec input) =
      taylor (-input.center) (JetHornerMachine.coefficientPolynomial input.coefficients) := by
  ext j
  rw [outputSpec, JetPreparationMachine.prepared_coeff]
  by_cases hj : j ≤ input.degree
  · rw [taylor_coeff]
    exact (JetHornerMachine.jetLoop_replicate_spec (-input.center)
      input.coefficients input.degree).2 j hj
  · have hlen : (jetSpec input).length ≤ j := by simp; omega
    have hz : (jetSpec input).getD j 0 = 0 := by
      simp only [List.getD, List.getElem?_eq_none hlen, Option.getD_none]
    rw [hz]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_taylor]
    have hd := represented_degree_le input hwidth
    omega

/-- Supplied polynomial representation and physical width certify the actual change of center.
No polynomial-to-list conversion or base-field descent is performed. -/
theorem shift_correct (input : Input F) (P : F[X])
    (hP : JetHornerMachine.coefficientPolynomial input.coefficients = P)
    (hwidth : input.coefficients.length = input.degree + 1) :
    ∃ cs, runFuel input (fuel input) .start = (.done (some cs), cost input) ∧
      cs.length = input.degree + 1 ∧
      JetHornerMachine.coefficientPolynomial cs = P.comp (X - C input.center) := by
  refine ⟨outputSpec input, shift_runFuel input, outputSpec_length input, ?_⟩
  rw [outputSpec_polynomial input hwidth, hP, taylor_apply]
  simp only [map_neg, sub_eq_add_neg]

omit [CommRing F] in
/-- Actual composition contains one scalar negation and no preparation padding constants. -/
theorem cost_scalar_counters (input : Input F) : (cost input).negations = 1 ∧
    (cost input).constants = 0 := by
  simp [cost, jetCost, preparationCost, wrapperCost, overheadCost,
    JetPreparationMachine.successCost, JetPreparationMachine.charge]

private theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [Cost.total, cost_add, JetHornerMachine.Cost.total, JetHornerMachine.cost_add]
  omega

omit [CommRing F] in
/-- The full actual cost, including wrappers and reversal, has a quadratic polynomial bound. -/
theorem cost_total_le (input : Input F)
    (hwidth : input.coefficients.length = input.degree + 1) :
    (cost input).total ≤ 160 * (input.degree + 2) ^ 2 := by
  simp only [cost, total_add]
  simp [jetCost, preparationCost, wrapperCost, overheadCost, Cost.total,
    JetHornerMachine.evaluationCost, JetHornerMachine.Cost.total, jetFuel, preparationFuel,
    JetPreparationMachine.successCost, JetPreparationMachine.charge, hwidth]
  nlinarith

/-- The cost bound applies to the executed machine, not just its declared vector. -/
theorem shift_cost_le (input : Input F)
    (hwidth : input.coefficients.length = input.degree + 1) :
    (runFuel input (fuel input) .start).2.total ≤ 160 * (input.degree + 2) ^ 2 := by
  rw [shift_runFuel]
  exact cost_total_le input hwidth

end ReedSolomon.HiddenDerivative.CenterShiftMachine
