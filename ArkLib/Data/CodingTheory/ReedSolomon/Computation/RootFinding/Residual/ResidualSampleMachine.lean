/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.JetHornerMachine
public import ArkLib.Data.MvPolynomial.EvaluationMachine
public import Mathlib.Algebra.MvPolynomial.Variables
/-!
# Closed composition for one scalar residual sample

The wrapper executes individual transitions of the jet and sparse-evaluation machines. It forms
`center+sample`, prepends that value to the materialized ascending jet, and evaluates sparse terms.
Every delegated transition pays an extra wrapper dispatch and two state-root accesses. Five other
phases charge entry, jet return, point addition, value-list construction and final scalar return.
Internal callee emissions remain counted, as does the final outer scalar output.

The inputs are materialized lists. Polynomial-facing correctness requires explicit coefficient-list
and sparse-term representation equalities and an explicit variable-arity bound. Preparing those
inputs, bit costs and a complete root-finding runtime are outside this subroutine's contract.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualSampleMachine

open Polynomial MvPolynomial

abbrev Cost := JetHornerMachine.Cost

/-- Materialized immutable input registers. -/
structure Input (F : Type*) where
  coefficients : List F
  terms : List (EvaluationMachine.Term F)
  center : F
  sample : F
  order : ℕ

/-- A wrapper dispatch reads and writes the callee state root. -/
def wrapperCost (n : ℕ) : Cost := ⟨0, 0, n, 2 * n, 0, 0⟩
/-- Read coefficients and order, write callee state, and form the jet length by successor. -/
def entryCost : Cost := ⟨0, 0, 1, 3, 1, 0⟩
/-- Read the returned jet root and write the retained jet register. -/
def jetReturnCost : Cost := ⟨0, 0, 1, 2, 0, 0⟩
/-- Read center and sample, add them, and write the point register. -/
def pointCost : Cost := ⟨1, 0, 1, 3, 0, 0⟩
/-- Read point, jet root and terms root; write values root and scalar-callee state. -/
def packCost : Cost := ⟨0, 0, 1, 5, 0, 0⟩
/-- Read the scalar return, write the final result, and emit it to the caller. -/
def returnCost : Cost := ⟨0, 0, 1, 2, 0, 1⟩
/-- Fixed overhead excluding the per-delegated-transition wrapper charges. -/
def overheadCost : Cost := ⟨1, 0, 5, 15, 1, 1⟩
/-- Preserve every component of the scalar evaluator's primitive costs. -/
def scalarCost (c : EvaluationMachine.Cost) : Cost :=
  ⟨c.additions, c.multiplications, c.control, c.data, c.natural, c.output⟩

/-- The complete wrapper state, including the actual suspended callee configurations. -/
inductive Configuration (F : Type*) where
  | start
  | jet (state : JetHornerMachine.Configuration F)
  | point (jets : List F)
  | pack (jets : List F) (point : F)
  | scalar (values : List F) (state : EvaluationMachine.Configuration F)
  | done (value : F)
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F]

/-- Independent wrapper rules; callee work is justified by a single actual callee step. -/
inductive Step (input : Input F) : Configuration F → Cost → Configuration F → Prop where
  | enter : Step input .start entryCost
      (.jet (.initialize input.coefficients (input.order + 1) []))
  | jet {s t c} (h : JetHornerMachine.Step input.sample s c t) :
      Step input (.jet s) (c + wrapperCost 1) (.jet t)
  | jetReturn {js} : Step input (.jet (.done js)) jetReturnCost (.point js)
  | point {js} : Step input (.point js) pointCost (.pack js (input.center + input.sample))
  | pack {js x} : Step input (.pack js x) packCost
      (.scalar (x :: js) (.terms input.terms 0))
  | scalar {values s t c} (h : EvaluationMachine.Step values s c t) :
      Step input (.scalar values s) (scalarCost c + wrapperCost 1) (.scalar values t)
  | return {values a} : Step input (.scalar values (.done a)) returnCost (.done a)

/-- Closed dispatch delegates only one callee transition, never a whole evaluation or run. -/
def step (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start => some (.jet (.initialize input.coefficients (input.order + 1) []), entryCost)
  | .jet s => match JetHornerMachine.step input.sample s with
      | some (t, c) => some (.jet t, c + wrapperCost 1)
      | none => match s with
          | .done js => some (.point js, jetReturnCost)
          | _ => none
  | .point js => some (.pack js (input.center + input.sample), pointCost)
  | .pack js x => some (.scalar (x :: js) (.terms input.terms 0), packCost)
  | .scalar values s => match EvaluationMachine.step values s with
      | some (t, c) => some (.scalar values t, scalarCost c + wrapperCost 1)
      | none => match s with
          | .done a => some (.done a, returnCost)
          | _ => none
  | .done _ => none

private theorem jet_halted (x : F) (s : JetHornerMachine.Configuration F)
    (h : JetHornerMachine.step x s = none) : ∃ js, s = .done js := by
  cases s with
  | «initialize» cs n zs => cases n <;> simp [JetHornerMachine.step] at h
  | coefficients cs js => cases cs <;> simp [JetHornerMachine.step] at h
  | update cs old rev carry => cases old <;> simp [JetHornerMachine.step] at h
  | reverse cs pending out => cases pending <;> simp [JetHornerMachine.step] at h
  | emit pending out => cases pending <;> simp [JetHornerMachine.step] at h
  | done js => exact ⟨js, rfl⟩

private theorem scalar_halted (values : List F) (s : EvaluationMachine.Configuration F)
    (h : EvaluationMachine.step values s = none) : ∃ a, s = .done a := by
  cases s with
  | terms ts a => cases ts <;> simp [EvaluationMachine.step] at h
  | factors ts a p fs => cases fs <;> simp [EvaluationMachine.step] at h
  | lookup ts a p fs e i xs => cases xs <;> cases i <;> simp [EvaluationMachine.step] at h
  | power ts a p fs x e => cases e <;> simp [EvaluationMachine.step] at h
  | done a => exact ⟨a, rfl⟩

/-- Each independent wrapper rule executes with its stated charge. -/
theorem Step.step_eq {input : Input F} {s t : Configuration F} {c : Cost}
    (h : Step input s c t) : step input s = some (t, c) := by
  cases h with
  | jet h => simp [step, h.step_eq]
  | scalar h => simp [step, h.step_eq]
  | _ => rfl

/-- Every actual wrapper transition satisfies the independent rules. -/
theorem step_sound {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step input s = some (t, c)) : Step input s c t := by
  cases s with
  | start => cases h; exact Step.enter
  | point js => cases h; exact Step.point
  | pack js x => cases h; exact Step.pack
  | done a => simp [step] at h
  | jet s =>
      cases hs : JetHornerMachine.step input.sample s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.jet (JetHornerMachine.step_sound hs)
      | none =>
          obtain ⟨js, rfl⟩ := jet_halted input.sample s hs
          cases h
          exact Step.jetReturn
  | scalar values s =>
      cases hs : EvaluationMachine.step values s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.scalar (EvaluationMachine.step_sound hs)
      | none =>
          obtain ⟨a, rfl⟩ := scalar_halted values s hs
          cases h
          exact Step.return

/-- Both successor and primitive charge are determined by the closed input and state. -/
theorem Step.deterministic {input : Input F} {s t u : Configuration F} {c d : Cost}
    (h : Step input s c t) (h' : Step input s d u) : t = u ∧ c = d := by
  simpa only [Option.some.injEq, Prod.mk.injEq] using h.step_eq.symm.trans h'.step_eq

/-- A finite trace accounts for all delegated and wrapper transitions. -/
inductive Trace (input : Input F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input 0 s 0 s
  | cons {n s u t c d} (head : Step input s c u) (tail : Trace input n u d t) :
      Trace input (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

/-- Trace composition charges no extra abstract computation. -/
theorem Trace.trans {input : Input F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace input n s c u) (h' : Trace input m u d t) :
    Trace input (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cost_assoc] using
        Trace.cons head (ih h')

/-- Execute at most the supplied number of wrapper steps. -/
def runFuel (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input n t; (result.1, c + result.2)

/-- Interpreter soundness includes exact accumulated charges. -/
theorem runFuel_refines (input : Input F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input n s (runFuel input fuel s).2 (runFuel input fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (input := input) s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace fuel reproduces the same result and charge. -/
theorem Trace.runFuel_eq {input : Input F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace input n s c t) : runFuel input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Lift an actual jet-machine trace with one wrapper charge per transition. -/
theorem lift_jet_trace (input : Input F) {n : ℕ}
    {s t : JetHornerMachine.Configuration F} {c : Cost}
    (h : JetHornerMachine.Trace input.sample n s c t) :
    Trace input n (.jet s) (c + wrapperCost n) (.jet t) := by
  induction h with
  | nil s => simpa [wrapperCost] using Trace.nil (input := input) (.jet s)
  | @cons n s u t c d head tail ih =>
      have heq : (c + wrapperCost 1) + (d + wrapperCost n) = (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.jet head) ih

/-- Lift an actual sparse-evaluator trace, preserving every primitive charge. -/
theorem lift_scalar_trace (input : Input F) (values : List F) {n : ℕ}
    {s t : EvaluationMachine.Configuration F} {c : EvaluationMachine.Cost}
    (h : EvaluationMachine.Trace values n s c t) :
    Trace input n (.scalar values s) (scalarCost c + wrapperCost n) (.scalar values t) := by
  induction h with
  | nil s => simpa [scalarCost, wrapperCost] using Trace.nil (input := input) (.scalar values s)
  | @cons n s u t c d head tail ih =>
      have heq : (scalarCost c + wrapperCost 1) + (scalarCost d + wrapperCost n) =
          scalarCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [scalarCost, wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.scalar head) ih

/-- Jet-callee fuel, including initialization and output. -/
def jetFuel (input : Input F) : ℕ :=
  (input.coefficients.length + 1) * (2 * (input.order + 1) + 3)
/-- Sparse-callee fuel for the translated point followed by the jet. -/
def scalarFuel (input : Input F) : ℕ :=
  EvaluationMachine.evaluationSteps (input.order + 2) input.terms
/-- Exact composite fuel. -/
def fuel (input : Input F) : ℕ := jetFuel input + scalarFuel input + 5
/-- Exact composite charges, including both callee emissions and final outer emission. -/
def cost (input : Input F) : Cost :=
  JetHornerMachine.evaluationCost input.coefficients.length (input.order + 1) +
    wrapperCost (jetFuel input) +
    scalarCost (EvaluationMachine.evaluationCost (input.order + 2) input.terms) +
    wrapperCost (scalarFuel input) + overheadCost

/-- The value list passed to the scalar callee, stated mathematically for refinement only. -/
def sampleValues (input : Input F) : List F :=
  (input.center + input.sample) :: JetHornerMachine.jetLoop input.sample input.coefficients
    (List.replicate (input.order + 1) 0)

@[simp] theorem sampleValues_length (input : Input F) :
    (sampleValues input).length = input.order + 2 := by simp [sampleValues]

private theorem full_jet_trace (input : Input F) :
    JetHornerMachine.Trace input.sample (jetFuel input)
      (.initialize input.coefficients (input.order + 1) [])
      (JetHornerMachine.evaluationCost input.coefficients.length (input.order + 1))
      (.done (JetHornerMachine.jetLoop input.sample input.coefficients
        (List.replicate (input.order + 1) 0))) := by
  have hi := JetHornerMachine.initialization_trace input.sample input.coefficients []
    (input.order + 1)
  simp only [List.append_nil] at hi
  have h := hi.trans (JetHornerMachine.loop_trace input.sample input.coefficients
    (List.replicate (input.order + 1) 0))
  simp only [List.length_replicate] at h
  convert h using 1
  · dsimp [jetFuel]
    ring
  · ext <;> simp only [JetHornerMachine.evaluationCost, JetHornerMachine.initializationCost,
      JetHornerMachine.loopCost, JetHornerMachine.cost_add] <;> ring

/-- Complete outer trace, assembled exclusively from individual callee and wrapper steps. -/
theorem evaluation_trace (input : Input F) :
    Trace input (fuel input) .start (cost input)
      (.done (EvaluationMachine.termValue (sampleValues input) input.terms)) := by
  have hj := lift_jet_trace input (full_jet_trace input)
  have he := lift_scalar_trace input (sampleValues input)
    (EvaluationMachine.evaluation_trace (sampleValues input) input.terms 0)
  simp only [sampleValues_length, zero_add] at he
  have h := Trace.cons Step.enter (hj.trans (Trace.cons Step.jetReturn
    (Trace.cons Step.point (Trace.cons Step.pack
      (he.trans (Trace.cons Step.return (Trace.nil _)))))))
  convert h using 1
  · dsimp [fuel, scalarFuel]
    omega
  · ext <;> simp only [cost, scalarFuel, entryCost, jetReturnCost, pointCost, packCost,
      returnCost, overheadCost, JetHornerMachine.cost_zero, JetHornerMachine.cost_add] <;> omega

/-- Actual fuel execution computes the sparse polynomial value with exact composite charges. -/
theorem evaluation_runFuel (input : Input F) :
    runFuel input (fuel input) .start =
      (.done (MvPolynomial.eval (fun i ↦ (sampleValues input).getD i 0)
        (EvaluationMachine.sparsePolynomial input.terms)), cost input) := by
  rw [EvaluationMachine.eval_sparsePolynomial]
  exact (evaluation_trace input).runFuel_eq

private theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [JetHornerMachine.Cost.total, JetHornerMachine.cost_add]
  omega

private theorem total_scalarCost (c : EvaluationMachine.Cost) :
    (scalarCost c).total = c.total := rfl

/-- The derived bound includes linear wrapper overhead, not just callee arithmetic. -/
theorem cost_total_le (input : Input F) :
    (cost input).total ≤ 43 * (input.coefficients.length + 1) * (input.order + 1) +
      12 * scalarFuel input + 23 := by
  have hj := JetHornerMachine.evaluationCost_total_le input.coefficients.length input.order
  have hjfuel := JetHornerMachine.evaluationFuel_le input.coefficients.length input.order
  have he := EvaluationMachine.evaluationCost_total_le (sampleValues input) input.terms
  simp only [sampleValues_length] at he
  simp only [cost, total_add, total_scalarCost]
  change _ + (wrapperCost (jetFuel input)).total + _ +
    (wrapperCost (scalarFuel input)).total + overheadCost.total ≤ _
  simp only [wrapperCost, overheadCost, JetHornerMachine.Cost.total]
  dsimp [jetFuel, scalarFuel] at *
  simp only [JetHornerMachine.Cost.total] at hj
  nlinarith only [hj, hjfuel, he]

/-- The intended infinite jet valuation; an explicit arity premise below restricts its use. -/
noncomputable def jetValuation (input : Input F) (P : F[X]) (i : ℕ) : F :=
  if i = 0 then input.center + input.sample else (hasseDeriv (i - 1) P).eval input.sample

private theorem sampleValues_getD (input : Input F) (P : F[X])
    (hP : JetHornerMachine.coefficientPolynomial input.coefficients = P)
    (i : ℕ) (hi : i < input.order + 2) :
    (sampleValues input).getD i 0 = jetValuation input P i := by
  cases i with
  | zero => simp [sampleValues, jetValuation]
  | succ j =>
      simp only [sampleValues, List.getD_cons_succ, jetValuation, Nat.add_one_ne_zero,
        ↓reduceIte, Nat.add_sub_cancel]
      have h := (JetHornerMachine.jetLoop_replicate_spec input.sample input.coefficients
        input.order).2 j (by omega)
      simpa only [hP] using h

/-- Polynomial-facing scalar correctness, requiring both representations and the full arity bound.
No variables outside `X,Y₀,...,Y_r` may silently be replaced by zero in this theorem. -/
theorem evaluation_runFuel_eq_jet (input : Input F) (P : F[X]) (Q : MvPolynomial ℕ F)
    (hP : JetHornerMachine.coefficientPolynomial input.coefficients = P)
    (hQ : EvaluationMachine.sparsePolynomial input.terms = Q)
    (harity : ∀ i ∈ Q.vars, i < input.order + 2) :
    runFuel input (fuel input) .start =
      (.done (MvPolynomial.eval (jetValuation input P) Q), cost input) := by
  rw [evaluation_runFuel, hQ]
  congr 2
  apply MvPolynomial.eval₂_congr
  intro i c hic hc
  apply sampleValues_getD input P hP i
  exact harity i ((MvPolynomial.mem_vars_iff_mem_support i).mpr
    ⟨c, MvPolynomial.mem_support_iff.mpr hc, hic⟩)

end ReedSolomon.HiddenDerivative.ResidualSampleMachine
