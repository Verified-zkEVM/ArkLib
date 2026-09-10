/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CandidateFilterSemantics
public import ArkLib.Data.QuadraticAlgebra.CoefficientDescentSemantics
/-!
# Closed base-field acceptance of a quadratic-field candidate

The driver first executes checked coordinate descent and then the degree/agreement filter.
It retains every callee charge and pays for each suspended-state dispatch and output. Inputs
are globally centered, materialized coefficients and received rows. Root enumeration, translating
local Taylor coordinates, duplicate removal and bit-cost lowering are separate consumers or
preparation steps. No whole-run callback or bulk conversion is an executable instruction.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticCandidateMachine

namespace Descent
export QuadraticAlgebra.CoefficientDescentMachine
  (Configuration Step step Trace runFuel runFuel_refines result descent_runFuel result_length)
end Descent

namespace Filter
export CandidateFilterMachine
  (Configuration Step step Trace runFuel runFuel_refines result fuel workBound evaluation_runFuel)
end Filter

/-- Each suspended callee retains its actual state. -/
inductive Configuration (F : Type*) (a b : F) where
  | start (coefficients : List (QuadraticAlgebra F a b))
  | descent (inner : Descent.Configuration F a b)
  | filter (inner : Filter.Configuration F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq

variable {F : Type*} [CommSemiring F] [DecidableEq F] {a b : F}

/-- Scalar work sums all primitive categories; wrapper dispatch/root accesses cost three. -/
inductive Step (w k A : ℕ) (rows : List (F × F)) :
    Configuration F a b → ℕ → Configuration F a b → Prop where
  | start {cs} : Step w k A rows (.start cs) 4 (.descent (.start cs))
  | descent {s t c} (h : Descent.Step s c t) :
      Step w k A rows (.descent s) (c.total + 3) (.descent t)
  | reject : Step w k A rows (.descent (.done none)) 3 (.emit none)
  | descended {cs} : Step w k A rows (.descent (.done (some cs))) 4 (.filter (.start cs))
  | filter {s t c} (h : Filter.Step w k A rows s c t) :
      Step w k A rows (.filter s) (c + 3) (.filter t)
  | filtered {out} : Step w k A rows (.filter (.done out)) 3 (.emit out)
  | emit {out} : Step w k A rows (.emit out) 3 (.done out)

/-- One nested step or one local handoff, never an entire uncharged subroutine. -/
def step (w k A : ℕ) (rows : List (F × F)) :
    Configuration F a b → Option (Configuration F a b × ℕ)
  | .start cs => some (.descent (.start cs), 4)
  | .descent s => match Descent.step s with
      | some (t, c) => some (.descent t, c.total + 3)
      | none => match s with
          | .done none => some (.emit none, 3)
          | .done (some cs) => some (.filter (.start cs), 4)
          | _ => none
  | .filter s => match Filter.step w k A rows s with
      | some (t, c) => some (.filter t, c + 3)
      | none => match s with
          | .done out => some (.emit out, 3)
          | _ => none
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- The operational rules predict the executable state and its exact scalar work. -/
theorem Step.step_eq {w k A : ℕ} {rows : List (F × F)}
    {s t : Configuration F a b} {c : ℕ} (h : Step w k A rows s c t) :
    step w k A rows s = some (t, c) := by
  cases h with
  | descent h => simp [step, h.step_eq]
  | filter h => simp [step, h.step_eq]
  | _ => rfl

/-- Every dispatched branch is covered by the independent rules. -/
theorem step_sound {w k A : ℕ} {rows : List (F × F)} {s t : Configuration F a b} {c : ℕ}
    (h : step w k A rows s = some (t, c)) : Step w k A rows s c t := by
  cases s with
  | start cs => cases h; constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h
  | descent s =>
      cases hs : Descent.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.descent (QuadraticAlgebra.CoefficientDescentMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases out <;> cases h <;> constructor
          | _ => simp [step, hs] at h
  | filter s =>
      cases hs : Filter.step w k A rows s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.filter (CandidateFilterMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases h; constructor
          | _ => simp [step, hs] at h

/-- Finite traces with the sum of actual instruction charges. -/
inductive Trace (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F a b → ℕ → Configuration F a b → Prop where
  | nil (s) : Trace w k A rows 0 s 0 s
  | cons {n s t u c d} (head : Step w k A rows s c t)
      (tail : Trace w k A rows n t d u) : Trace w k A rows (n + 1) s (c + d) u

omit [DecidableEq F] in
/-- Sequential composition retains all nested work. -/
theorem Trace.trans {w k A n m : ℕ} {rows : List (F × F)}
    {s t u : Configuration F a b} {c d : ℕ}
    (h : Trace w k A rows n s c t) (h' : Trace w k A rows m t d u) :
    Trace w k A rows (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Host fuel is separate from modeled primitive work. -/
def runFuel (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F a b → Configuration F a b × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step w k A rows s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel w k A rows n t; (r.1, c + r.2)

/-- Every run, including a partial run, has an operational trace with the same cost. -/
theorem runFuel_refines (w k A fuel : ℕ) (rows : List (F × F)) (s : Configuration F a b) :
    ∃ n ≤ fuel, Trace w k A rows n s (runFuel w k A rows fuel s).2
      (runFuel w k A rows fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step w k A rows s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Completed traces determine executions with additional fuel. -/
theorem Trace.runFuel_done {w k A n : ℕ} {rows : List (F × F)}
    {s : Configuration F a b} {c : ℕ} {out : Option (List F)}
    (h : Trace w k A rows n s c (.done out)) (extra : ℕ) :
    runFuel w k A rows (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih he]

omit [DecidableEq F] in
/-- Each coordinate descent step retains every primitive category and pays its wrapper. -/
theorem lift_descent {w k A n : ℕ} (rows : List (F × F))
    {s t : Descent.Configuration F a b} {c : QuadraticAlgebra.ArithmeticMachine.Cost}
    (h : Descent.Trace n s c t) :
    Trace w k A rows n (.descent s) (c.total + 3 * n) (.descent t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.descent head) ih using 1
      rw [QuadraticAlgebra.CoefficientDescentMachine.total_add]
      omega

omit [DecidableEq F] in
/-- The candidate filter also advances one actual instruction per driver transition. -/
theorem lift_filter {w k A n : ℕ} (rows : List (F × F))
    {s t : Filter.Configuration F} {c : ℕ} (h : Filter.Trace w k A rows n s c t) :
    Trace (a := a) (b := b) w k A rows n (.filter s) (c + 3 * n) (.filter t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.filter head) ih using 1
      omega

/-- Proof-only composition specification, not invoked by executable dispatch. -/
def result (w k A : ℕ) (xs : List (QuadraticAlgebra F a b)) (rows : List (F × F)) :
    Option (List F) := (Descent.result xs).bind fun cs => Filter.result w k A cs rows

/-- Supplied width and point count give finite host fuel without a free length scan. -/
def fuel (w k n : ℕ) : ℕ := 2 * w + 4 + Filter.fuel w k n + 4

/-- Primitive work is linear in the ambient width times the received length. -/
def workBound (w n : ℕ) : ℕ := 192 * (w + 1) * (n + 1)

/-- Coordinate descent and exact candidate filtering compose into a single bounded execution. -/
theorem evaluation_runFuel (w k A : ℕ) (xs : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (hwidth : xs.length = w) :
    ∃ c, runFuel w k A rows (fuel w k rows.length) (.start xs) =
      (.done (result w k A xs rows), c) ∧ c ≤ workBound w rows.length := by
  obtain ⟨dc, hdr, hdc⟩ := Descent.descent_runFuel xs
  obtain ⟨dn, hdn, hdt⟩ := Descent.runFuel_refines (2 * xs.length + 4) (.start xs)
  rw [hdr] at hdt
  dsimp only at hdt
  rw [hwidth] at hdn hdc
  have hd := lift_descent (w := w) (k := k) (A := A) rows hdt
  cases hr : Descent.result xs with
  | none =>
      rw [hr] at hd
      have ht := Trace.cons Step.start (hd.trans
        (Trace.cons Step.reject (Trace.cons Step.emit (Trace.nil _))))
      have hsteps : dn + (0 + 1 + 1) + 1 ≤ fuel w k rows.length := by
        dsimp [fuel]; omega
      have he := ht.runFuel_done (fuel w k rows.length - (dn + (0 + 1 + 1) + 1))
      rw [Nat.add_sub_of_le hsteps] at he
      refine ⟨_, by simpa only [result, hr, Option.bind_none] using he, ?_⟩
      dsimp [workBound]
      nlinarith
  | some cs =>
      have hcwidth : cs.length = w := (Descent.result_length hr).trans hwidth
      obtain ⟨fc, hfr, hfc⟩ := Filter.evaluation_runFuel w k A cs rows hcwidth.le
      obtain ⟨fn, hfn, hft⟩ := Filter.runFuel_refines w k A
        (Filter.fuel w k rows.length) rows (.start cs)
      rw [hfr] at hft
      dsimp only at hft
      have hf := lift_filter (a := a) (b := b) rows hft
      rw [hr] at hd
      have ht := Trace.cons Step.start (hd.trans (Trace.cons Step.descended
        (hf.trans (Trace.cons Step.filtered (Trace.cons Step.emit (Trace.nil _))))))
      have hsteps : dn + (fn + (0 + 1 + 1) + 1) + 1 ≤ fuel w k rows.length := by
        dsimp [fuel]; omega
      have he := ht.runFuel_done (fuel w k rows.length -
        (dn + (fn + (0 + 1 + 1) + 1) + 1))
      rw [Nat.add_sub_of_le hsteps] at he
      refine ⟨_, by simpa only [result, hr, Option.bind_some] using he, ?_⟩
      dsimp [Filter.workBound, CandidateFilterMachine.workBound] at hfc
      dsimp [Filter.fuel, CandidateFilterMachine.fuel] at hfn
      have hw : w - k ≤ w := Nat.sub_le _ _
      dsimp [workBound]
      nlinarith

end ReedSolomon.ListDecoding.QuadraticCandidateMachine
