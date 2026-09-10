/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.AgreementMachine
public import ArkLib.Data.Polynomial.DegreeTruncationSemantics
/-!
# Closed degree and agreement filtering of one candidate

The program first checks the high coefficients, then counts agreements using the emitted
short coefficient vector. Each callee advances one instruction at a time. A scalar work count
sums every category in each callee's operation vector and adds wrapper dispatch and root
accesses. Thus this is a unit-cost primitive bound, not a bit-complexity assertion.

Inputs are materialized descending coefficients and point/value pairs. Base-field descent,
candidate enumeration, deduplication, input preparation and scalar bit costs are separate.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CandidateFilterMachine

open Polynomial

abbrev DegreeConfiguration := DegreeTruncationMachine.Configuration

/-- Sum all agreement-machine primitive categories, including counters and Horner indexing. -/
def agreementWork (c : AgreementMachine.Cost) : ℕ :=
  c.machine.additions + c.machine.multiplications + c.machine.control + c.machine.indexing +
    c.machine.data + c.machine.output + c.equalities + c.counterUpdates + c.thresholdTests

@[simp] theorem agreementWork_zero : agreementWork 0 = 0 := rfl
@[simp] theorem agreementWork_add (a b : AgreementMachine.Cost) :
    agreementWork (a + b) = agreementWork a + agreementWork b := by
  simp only [agreementWork, AgreementMachine.cost_add, HornerMachine.cost_add]
  omega

/-- Total exact agreement work on materialized widths and positions. -/
theorem agreementWork_totalCost (w n : ℕ) :
    agreementWork (AgreementMachine.totalCost w n) = 20 * n * w + 32 * n + 7 := by
  simp only [agreementWork, AgreementMachine.totalCost]
  ring

/-- The actual suspended state is retained at each call, together with the checked candidate. -/
inductive Configuration (F : Type*) where
  | start (coefficients : List F)
  | degree (inner : DegreeConfiguration F)
  | agreement (coefficients : List F) (inner : AgreementMachine.Configuration F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Every nested transition retains its entire primitive work and pays three wrapper accesses.
Start and successful handoff cost four; rejection/selection and emission cost three each. -/
inductive Step (w k A : ℕ) (rows : List (F × F)) :
    Configuration F → ℕ → Configuration F → Prop where
  | start {cs} : Step w k A rows (.start cs) 4 (.degree (.start cs))
  | degree {s t c} (h : DegreeTruncationMachine.Step w k s c t) :
      Step w k A rows (.degree s) (c.total + 3) (.degree t)
  | reject : Step w k A rows (.degree (.done none)) 3 (.emit none)
  | checked {cs} : Step w k A rows (.degree (.done (some cs))) 4
      (.agreement cs (.scan rows 0))
  | agreement {cs s t c} (h : AgreementMachine.Step cs A s c t) :
      Step w k A rows (.agreement cs s) (agreementWork c + 3) (.agreement cs t)
  | selected {cs count b} : Step w k A rows (.agreement cs (.done count b)) 3
      (.emit (if b then some cs else none))
  | emit {out} : Step w k A rows (.emit out) 3 (.done out)

/-- Dispatch never computes the full degree test, agreement count, or a callee run for free. -/
def step (w k A : ℕ) (rows : List (F × F)) :
    Configuration F → Option (Configuration F × ℕ)
  | .start cs => some (.degree (.start cs), 4)
  | .degree s => match DegreeTruncationMachine.step w k s with
      | some (t, c) => some (.degree t, c.total + 3)
      | none => match s with
          | .done none => some (.emit none, 3)
          | .done (some cs) => some (.agreement cs (.scan rows 0), 4)
          | _ => none
  | .agreement cs s => match AgreementMachine.step cs A s with
      | some (t, c) => some (.agreement cs t, agreementWork c + 3)
      | none => match s with
          | .done _ b => some (.emit (if b then some cs else none), 3)
          | _ => none
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- Each rule agrees with dispatch, including its primitive work. -/
theorem Step.step_eq {w k A : ℕ} {rows : List (F × F)} {s t : Configuration F} {c : ℕ}
    (h : Step w k A rows s c t) : step w k A rows s = some (t, c) := by
  cases h with
  | degree h => simp [step, h.step_eq]
  | agreement h => simp [step, h.step_eq]
  | _ => rfl

/-- Every dispatched operation belongs to the independent semantics. -/
theorem step_sound {w k A : ℕ} {rows : List (F × F)} {s t : Configuration F} {c : ℕ}
    (h : step w k A rows s = some (t, c)) : Step w k A rows s c t := by
  cases s with
  | start cs => cases h; constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h
  | degree s =>
      cases hs : DegreeTruncationMachine.step w k s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.degree (DegreeTruncationMachine.step_sound hs)
      | none =>
          cases s with
          | done out =>
              cases out <;>
                simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h <;>
                rcases h with ⟨rfl, rfl⟩ <;> constructor
          | _ => simp [step, hs] at h
  | agreement cs s =>
      cases hs : AgreementMachine.step cs A s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.agreement (AgreementMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.selected

/-- Actual finite traces with scalar work obtained by summing their instructions. -/
inductive Trace (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace w k A rows 0 s 0 s
  | cons {n s t u c d} (head : Step w k A rows s c t)
      (tail : Trace w k A rows n t d u) : Trace w k A rows (n + 1) s (c + d) u

omit [DecidableEq F] in
/-- Sequential composition preserves every instruction and its work. -/
theorem Trace.trans {w k A n m : ℕ} {rows : List (F × F)}
    {s t u : Configuration F} {c d : ℕ}
    (h : Trace w k A rows n s c t) (h' : Trace w k A rows m t d u) :
    Trace w k A rows (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Trace.cons head (ih h')

/-- Host fuel bounds the number of actual transitions, not a cost-free computation oracle. -/
def runFuel (w k A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step w k A rows s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel w k A rows n t; (result.1, c + result.2)

/-- Every interpreter run is justified by a trace with the same scalar work. -/
theorem runFuel_refines (w k A fuel : ℕ) (rows : List (F × F)) (s : Configuration F) :
    ∃ n ≤ fuel, Trace w k A rows n s (runFuel w k A rows fuel s).2
      (runFuel w k A rows fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step w k A rows s with
      | none =>
          exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using
            (Trace.nil (w := w) (k := k) (A := A) (rows := rows) s)⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Completed executions remain fixed under additional host fuel. -/
theorem Trace.runFuel_done {w k A n : ℕ} {rows : List (F × F)} {s : Configuration F}
    {c : ℕ} {out : Option (List F)} (h : Trace w k A rows n s c (.done out)) (extra : ℕ) :
    runFuel w k A rows (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

omit [DecidableEq F] in
/-- Each degree-check instruction is stepped rather than treated as a unit-cost subroutine. -/
theorem lift_degree_trace {w k A n : ℕ} (rows : List (F × F))
    {s t : DegreeConfiguration F} {c : DegreeTruncationMachine.Cost}
    (h : DegreeTruncationMachine.Trace w k n s c t) :
    Trace w k A rows n (.degree s) (c.total + 3 * n) (.degree t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.degree head) ih using 1
      simp only [DegreeTruncationMachine.Cost.total, DegreeTruncationMachine.cost_add]
      omega

omit [DecidableEq F] in
/-- Each agreement instruction is stepped, retaining every Horner and counter charge. -/
theorem lift_agreement_trace {w k A n : ℕ} (rows : List (F × F)) (cs : List F)
    {s t : AgreementMachine.Configuration F} {c : AgreementMachine.Cost}
    (h : AgreementMachine.Trace cs A n s c t) :
    Trace w k A rows n (.agreement cs s) (agreementWork c + 3 * n) (.agreement cs t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.agreement head) ih using 1
      rw [agreementWork_add]
      omega

/-- Proof-only result specification; executable dispatch never invokes this bulk expression. -/
def result (w k A : ℕ) (cs : List F) (rows : List (F × F)) : Option (List F) :=
  match DegreeTruncationMachine.result (w - k) cs with
  | none => none
  | some tail => if decide (A ≤ AgreementMachine.agreementCount tail rows) then some tail else none

/-- Uniform fuel using the supplied ambient width rather than an uncharged input-length scan. -/
def fuel (w k n : ℕ) : ℕ := w - k + 3 + n * (3 * w + 6) + 5

/-- A conservative primitive-work bound, linear in width times the number of received points. -/
def workBound (w n : ℕ) : ℕ := 64 * (w + 1) * (n + 1)

/-- A materialized vector of at most the supplied width is filtered by an actual bounded trace.
Both early degree rejection and the complete agreement path retain all their work. -/
theorem evaluation_trace (w k A : ℕ) (cs : List F) (rows : List (F × F))
    (hwidth : cs.length ≤ w) :
    ∃ steps c, steps ≤ fuel w k rows.length ∧
      Trace w k A rows steps (.start cs) c (.done (result w k A cs rows)) ∧
      c ≤ workBound w rows.length := by
  obtain ⟨s, dc, hs, ht⟩ := DegreeTruncationMachine.scan_trace w k (w - k) cs
  have hdt := DegreeTruncationMachine.Trace.cons DegreeTruncationMachine.Step.start ht
  have hdc := hdt.total_le
  have hd := lift_degree_trace (A := A) rows hdt
  cases hr : DegreeTruncationMachine.result (w - k) cs with
  | none =>
      rw [hr] at hd
      have h := Trace.cons Step.start (hd.trans
        (Trace.cons Step.reject (Trace.cons Step.emit (Trace.nil _))))
      refine ⟨_, _, ?_, by simpa only [result, hr] using h, ?_⟩
      · dsimp [fuel]
        omega
      · dsimp [workBound]
        simp only [DegreeTruncationMachine.Cost.total, DegreeTruncationMachine.cost_add] at hdc ⊢
        have hw : w - k ≤ w := Nat.sub_le _ _
        nlinarith
  | some tail =>
      have hshape := (DegreeTruncationMachine.result_eq_some_iff (w - k) cs tail).mp hr
      have htail : tail.length ≤ w := by
        have hh := congrArg List.length hshape
        simp only [List.length_append, List.length_replicate] at hh
        omega
      have ha := lift_agreement_trace (w := w) (k := k) rows tail
        (AgreementMachine.agreement_trace tail A rows 0)
      simp only [Nat.zero_add] at ha
      rw [hr] at hd
      have h := Trace.cons Step.start (hd.trans (Trace.cons Step.checked
        (ha.trans (Trace.cons Step.selected (Trace.cons Step.emit (Trace.nil _))))))
      refine ⟨_, _, ?_, by simpa only [result, hr] using h, ?_⟩
      · have hp := Nat.mul_le_mul_left rows.length
          (Nat.add_le_add_right (Nat.mul_le_mul_left 3 htail) 6)
        dsimp [fuel]
        omega
      · rw [agreementWork_totalCost]
        have hp := Nat.mul_le_mul_left rows.length htail
        have hw : w - k ≤ w := Nat.sub_le _ _
        dsimp [workBound]
        simp only [DegreeTruncationMachine.Cost.total, DegreeTruncationMachine.cost_add] at hdc ⊢
        nlinarith

/-- The returned result and its primitive cost refer to the very same closed execution. -/
theorem evaluation_runFuel (w k A : ℕ) (cs : List F) (rows : List (F × F))
    (hwidth : cs.length ≤ w) :
    ∃ c, runFuel w k A rows (fuel w k rows.length) (.start cs) =
      (.done (result w k A cs rows), c) ∧ c ≤ workBound w rows.length := by
  obtain ⟨s, c, hs, ht, hc⟩ := evaluation_trace w k A cs rows hwidth
  have hr := ht.runFuel_done (fuel w k rows.length - s)
  rw [Nat.add_sub_of_le hs] at hr
  exact ⟨c, hr, hc⟩

end ReedSolomon.ListDecoding.CandidateFilterMachine
