/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.CanonicalGuardBounds
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticCandidateSemantics
/-!
# Closed canonical base-field candidate acceptance

One closed driver executes the canonical stage/center guard and then checked base-field descent,
degree truncation and agreement testing. It advances each callee one instruction at a time and
retains every charge plus its caller dispatch. Rejection short-circuits the remaining work.
Coefficients are global and materialized. The guard uses the original maximum derivative order,
which can exceed the active order used to construct this candidate.

The scalar ledger counts base and extension field operations as unit operations at this layer.
Replacing extension operations by their proved base-field implementations is a separate lowering
obligation. This component neither generates candidates nor proves uniqueness of the whole list.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CanonicalAcceptanceMachine

namespace Guard
export HiddenDerivative.CanonicalGuardMachine
  (Input Equation Configuration Step step Trace runFuel runFuel_refines result fuel workBound)
end Guard

namespace Candidate
export QuadraticCandidateMachine
  (Configuration Step step Trace runFuel runFuel_refines result fuel workBound)
end Candidate

/-- Suspended execution retains the exact child configuration and emitted base coefficients. -/
inductive Configuration (F : Type*) (a b : F) where
  | start (previous : List (Guard.Equation (QuadraticAlgebra F a b)))
  | guard (inner : Guard.Configuration (QuadraticAlgebra F a b))
  | candidate (inner : Candidate.Configuration F a b)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq

variable {F : Type*} [CommSemiring F] [DecidableEq F] {a b : F}

/-- All caller instructions expose their own fixed charges; nested work is never discarded. -/
inductive Step (input : Guard.Input (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) : Configuration F a b → ℕ → Configuration F a b → Prop where
  | start {ps} : Step input w k A rows (.start ps) 4 (.guard (.start ps))
  | guard {s t c} (h : Guard.Step input s c t) :
      Step input w k A rows (.guard s) (c + 3) (.guard t)
  | reject : Step input w k A rows (.guard (.done false)) 3 (.emit none)
  | passed : Step input w k A rows (.guard (.done true)) 4
      (.candidate (.start input.coefficients))
  | candidate {s t c} (h : Candidate.Step w k A rows s c t) :
      Step input w k A rows (.candidate s) (c + 3) (.candidate t)
  | returned {out} : Step input w k A rows (.candidate (.done out)) 3 (.emit out)
  | emit {out} : Step input w k A rows (.emit out) 3 (.done out)

/-- Dispatch performs one child instruction or one bounded handoff, not an entire child run. -/
def step (input : Guard.Input (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) : Configuration F a b → Option (Configuration F a b × ℕ)
  | .start ps => some (.guard (.start ps), 4)
  | .guard s => match Guard.step input s with
      | some (t, c) => some (.guard t, c + 3)
      | none => match s with
          | .done false => some (.emit none, 3)
          | .done true => some (.candidate (.start input.coefficients), 4)
          | _ => none
  | .candidate s => match Candidate.step w k A rows s with
      | some (t, c) => some (.candidate t, c + 3)
      | none => match s with
          | .done out => some (.emit out, 3)
          | _ => none
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- The independent transition rules predict exactly the interpreter and its charge. -/
theorem Step.step_eq {input : Guard.Input (QuadraticAlgebra F a b)} {w k A : ℕ}
    {rows : List (F × F)} {s t : Configuration F a b} {c : ℕ}
    (h : Step input w k A rows s c t) : step input w k A rows s = some (t, c) := by
  cases h with
  | guard h => simp [step, h.step_eq]
  | candidate h => simp [step, h.step_eq]
  | _ => rfl

/-- Every executable dispatch branch is represented by an independent transition rule. -/
theorem step_sound {input : Guard.Input (QuadraticAlgebra F a b)} {w k A : ℕ}
    {rows : List (F × F)} {s t : Configuration F a b} {c : ℕ}
    (h : step input w k A rows s = some (t, c)) : Step input w k A rows s c t := by
  cases s with
  | start ps => cases h; constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h
  | guard s =>
      cases hs : Guard.step input s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.guard (HiddenDerivative.CanonicalGuardMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases out <;> cases h <;> constructor
          | _ => simp [step, hs] at h
  | candidate s =>
      cases hs : Candidate.step w k A rows s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.candidate (QuadraticCandidateMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases h; constructor
          | _ => simp [step, hs] at h

/-- Finite traces accumulate the full work of local and delegated instructions. -/
inductive Trace (input : Guard.Input (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) : ℕ → Configuration F a b → ℕ → Configuration F a b → Prop where
  | nil (s) : Trace input w k A rows 0 s 0 s
  | cons {n s t u c d} (head : Step input w k A rows s c t)
      (tail : Trace input w k A rows n t d u) : Trace input w k A rows (n + 1) s (c + d) u

/-- Trace concatenation preserves both step counts and all primitive charges. -/
theorem Trace.trans {input : Guard.Input (QuadraticAlgebra F a b)} {w k A n m : ℕ}
    {rows : List (F × F)} {s t u : Configuration F a b} {c d : ℕ}
    (h : Trace input w k A rows n s c t) (h' : Trace input w k A rows m t d u) :
    Trace input w k A rows (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Fuel exhaustion returns the actual suspended state; modeled work remains separate. -/
def runFuel (input : Guard.Input (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) : ℕ → Configuration F a b → Configuration F a b × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step input w k A rows s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel input w k A rows n t; (r.1, c + r.2)

/-- Every partial or complete interpreter run has an actual trace with identical work. -/
theorem runFuel_refines (input : Guard.Input (QuadraticAlgebra F a b)) (w k A fuel : ℕ)
    (rows : List (F × F)) (s : Configuration F a b) :
    ∃ n ≤ fuel, Trace input w k A rows n s (runFuel input w k A rows fuel s).2
      (runFuel input w k A rows fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input w k A rows s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Completed traces determine the interpreter result for every sufficient fuel bound. -/
theorem Trace.runFuel_done {input : Guard.Input (QuadraticAlgebra F a b)} {w k A n : ℕ}
    {rows : List (F × F)} {s : Configuration F a b} {c : ℕ} {out : Option (List F)}
    (h : Trace input w k A rows n s c (.done out)) (extra : ℕ) :
    runFuel input w k A rows (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih he]

/-- The guard runs instruction by instruction, retaining its exact work and caller charges. -/
theorem lift_guard {input : Guard.Input (QuadraticAlgebra F a b)} {w k A n : ℕ}
    (rows : List (F × F)) {s t : Guard.Configuration (QuadraticAlgebra F a b)} {c : ℕ}
    (h : Guard.Trace input n s c t) :
    Trace input w k A rows n (.guard s) (c + 3 * n) (.guard t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.guard head) ih using 1
      omega

/-- Base-field acceptance similarly retains every descent, filtering and dispatch charge. -/
theorem lift_candidate (input : Guard.Input (QuadraticAlgebra F a b)) {w k A n : ℕ}
    {rows : List (F × F)} {s t : Candidate.Configuration F a b} {c : ℕ}
    (h : Candidate.Trace w k A rows n s c t) :
    Trace input w k A rows n (.candidate s) (c + 3 * n) (.candidate t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.candidate head) ih using 1
      omega

/-- Proof-side composition specification; executable dispatch does not call either full result. -/
def result (input : Guard.Input (QuadraticAlgebra F a b))
    (previous : List (Guard.Equation (QuadraticAlgebra F a b))) (w k A : ℕ)
    (rows : List (F × F)) : Option (List F) :=
  if Guard.result input previous then Candidate.result w k A input.coefficients rows else none

/-- Fuel bounds both actual child programs and the four local handoffs. -/
def fuel (input : Guard.Input (QuadraticAlgebra F a b))
    (previous : List (Guard.Equation (QuadraticAlgebra F a b))) (w k n : ℕ) : ℕ :=
  Guard.fuel input previous + Candidate.fuel w k n + 4

/-- Work includes both children, their caller dispatches, and local handoff/emission costs. -/
def workBound (input : Guard.Input (QuadraticAlgebra F a b))
    (previous : List (Guard.Equation (QuadraticAlgebra F a b))) (w k n : ℕ) : ℕ :=
  Guard.workBound input previous + 3 * Guard.fuel input previous +
    Candidate.workBound w n + 3 * Candidate.fuel w k n + 20

/-- The same closed execution implements canonical acceptance with its accumulated work bound. -/
theorem evaluation_runFuel (input : Guard.Input (QuadraticAlgebra F a b))
    (previous : List (Guard.Equation (QuadraticAlgebra F a b))) (w k A : ℕ)
    (rows : List (F × F)) (hwidth : input.coefficients.length = w) :
    ∃ c, runFuel input w k A rows (fuel input previous w k rows.length) (.start previous) =
      (.done (result input previous w k A rows), c) ∧
      c ≤ workBound input previous w k rows.length := by
  obtain ⟨gc, hgr, hgc⟩ := HiddenDerivative.CanonicalGuardMachine.evaluation_runFuel input previous
  obtain ⟨gn, hgn, hgt⟩ := Guard.runFuel_refines input (Guard.fuel input previous) (.start previous)
  rw [hgr] at hgt
  have hg := lift_guard (w := w) (k := k) (A := A) rows hgt
  cases hr : Guard.result input previous with
  | false =>
      rw [hr] at hg
      have ht := Trace.cons Step.start (hg.trans
        (Trace.cons Step.reject (Trace.cons Step.emit (Trace.nil _))))
      have hn : gn + (0 + 1 + 1) + 1 ≤ fuel input previous w k rows.length := by
        dsimp [fuel]; omega
      have he := ht.runFuel_done (fuel input previous w k rows.length -
        (gn + (0 + 1 + 1) + 1))
      rw [Nat.add_sub_of_le hn] at he
      refine ⟨_, by simpa only [result, hr, Bool.false_eq_true, ↓reduceIte] using he, ?_⟩
      dsimp [workBound]
      omega
  | true =>
      rw [hr] at hg
      obtain ⟨cc, hcr, hcc⟩ := QuadraticCandidateMachine.evaluation_runFuel w k A
        input.coefficients rows hwidth
      obtain ⟨cn, hcn, hct⟩ := Candidate.runFuel_refines w k A
        (Candidate.fuel w k rows.length) rows (.start input.coefficients)
      rw [hcr] at hct
      have ht := Trace.cons Step.start (hg.trans (Trace.cons Step.passed
        ((lift_candidate input hct).trans
          (Trace.cons Step.returned (Trace.cons Step.emit (Trace.nil _))))))
      have hn : gn + (cn + (0 + 1 + 1) + 1) + 1 ≤
          fuel input previous w k rows.length := by dsimp [fuel]; omega
      have he := ht.runFuel_done (fuel input previous w k rows.length -
        (gn + (cn + (0 + 1 + 1) + 1) + 1))
      rw [Nat.add_sub_of_le hn] at he
      refine ⟨_, by simpa only [result, hr, ↓reduceIte] using he, ?_⟩
      dsimp [workBound]
      omega

end ReedSolomon.ListDecoding.CanonicalAcceptanceMachine
