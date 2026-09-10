/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine

/-!
# Checked descent of quadratic coefficient vectors

The program scans actual two-coordinate coefficients. It rejects any nonzero imaginary
coordinate and otherwise materializes the real-coordinate list, preserving its order and
physical width. Each scalar equality, coordinate read, allocation, reversal and emission is
charged. The field structure and the input vector are supplied; host fuel and bit costs remain
outside the primitive model. No bulk projection or algebra-map conversion occurs in dispatch.
-/

@[expose] public section

namespace QuadraticAlgebra.CoefficientDescentMachine

abbrev Cost := ArithmeticMachine.Cost

/-- Base-field equality and administrative charges of one instruction. -/
def charge (data eq constants output : ℕ) : Cost :=
  { control := 1, data := data, equalities := eq, constants := constants, output := output }

/-- Input coefficients remain shared; accepted scalar cells are allocated and reversed. -/
inductive Configuration (F : Type*) (a b : F) where
  | start (coefficients : List (QuadraticAlgebra F a b))
  | scan (remaining : List (QuadraticAlgebra F a b)) (output : List F)
  | reverse (remaining output : List F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq

variable {F : Type*} {a b : F} [Zero F] [DecidableEq F]

/-- Each independent rule performs at most one base-field equality test. -/
inductive Step : Configuration F a b → Cost → Configuration F a b → Prop where
  | start {cs} : Step (.start cs) (charge 3 0 1 0) (.scan cs [])
  | accepted {x xs out} (h : x.im = 0) :
      Step (.scan (x :: xs) out) (charge 6 1 0 0) (.scan xs (x.re :: out))
  | rejected {x xs out} (h : x.im ≠ 0) :
      Step (.scan (x :: xs) out) (charge 3 1 0 0) (.emit none)
  | finish {out} : Step (.scan [] out) (charge 3 0 0 0) (.reverse out [])
  | reverse {x xs out} : Step (.reverse (x :: xs) out) (charge 5 0 0 0)
      (.reverse xs (x :: out))
  | reversed {out} : Step (.reverse [] out) (charge 2 0 0 0) (.emit (some out))
  | emit {out} : Step (.emit out) (charge 2 0 0 1) (.done out)

/-- One cursor or output instruction; no full-list test or conversion is hidden. -/
def step : Configuration F a b → Option (Configuration F a b × Cost)
  | .start cs => some (.scan cs [], charge 3 0 1 0)
  | .scan [] out => some (.reverse out [], charge 3 0 0 0)
  | .scan (x :: xs) out => if x.im = 0 then
      some (.scan xs (x.re :: out), charge 6 1 0 0)
      else some (.emit none, charge 3 1 0 0)
  | .reverse (x :: xs) out => some (.reverse xs (x :: out), charge 5 0 0 0)
  | .reverse [] out => some (.emit (some out), charge 2 0 0 0)
  | .emit out => some (.done out, charge 2 0 0 1)
  | .done _ => none

/-- Rules and executable transitions agree on the exact cost. -/
theorem Step.step_eq {s t : Configuration F a b} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by
  cases h with
  | accepted h => simp [step, h]
  | rejected h => simp [step, h]
  | _ => rfl

/-- Every dispatched transition has an independent rule. -/
theorem step_sound {s t : Configuration F a b} {c : Cost}
    (h : step s = some (t, c)) : Step s c t := by
  cases s with
  | start cs => cases h; constructor
  | scan xs out =>
      cases xs with
      | nil => cases h; constructor
      | cons x xs =>
          by_cases hx : x.im = 0
          · simp only [step, if_pos hx] at h
            cases h; exact Step.accepted hx
          · simp only [step, if_neg hx] at h
            cases h; exact Step.rejected hx
  | reverse xs out => cases xs <;> cases h <;> constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h

/-- Finite operational traces retain all primitive charges. -/
inductive Trace : ℕ → Configuration F a b → Cost → Configuration F a b → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s t u c d} (head : Step s c t) (tail : Trace n t d u) :
      Trace (n + 1) s (c + d) u

/-- Host fuel exposes partial state; it does not invoke an uncharged vector conversion. -/
def runFuel : ℕ → Configuration F a b → Configuration F a b × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel n t; (r.1, c + r.2)

/-- Every actual run has a trace with identical primitive work. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration F a b) :
    ∃ n ≤ fuel, Trace n s (runFuel fuel s).2 (runFuel fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Completed traces determine executions with surplus fuel. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration F a b} {c : Cost} {out : Option (List F)}
    (h : Trace n s c (.done out)) (extra : ℕ) : runFuel (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih he]

omit [DecidableEq F] in
/-- Each instruction uses at most eight primitives in the supplied coordinate representation. -/
theorem Step.total_le {s t : Configuration F a b} {c : Cost} (h : Step s c t) :
    c.total ≤ 8 := by cases h <;> decide

/-- Summing operation vectors preserves every primitive category. -/
theorem total_add (c d : Cost) : (c + d).total = c.total + d.total := by
  change (c.additions + d.additions) + (c.multiplications + d.multiplications) +
    (c.negations + d.negations) + (c.inversions + d.inversions) +
    (c.equalities + d.equalities) + (c.control + d.control) + (c.data + d.data) +
    (c.constants + d.constants) + (c.output + d.output) = _
  unfold ArithmeticMachine.Cost.total
  omega

omit [DecidableEq F] in
/-- The primitive work of an actual trace is linear in its instruction count. -/
theorem Trace.total_le {n : ℕ} {s t : Configuration F a b} {c : Cost}
    (h : Trace n s c t) : c.total ≤ 8 * n := by
  induction h with
  | nil s => exact Nat.zero_le _
  | cons head tail ih => rw [total_add]; have hh := head.total_le; omega

/-- Proof-only checked projection; executable dispatch advances one cell at a time. -/
def result : List (QuadraticAlgebra F a b) → Option (List F)
  | [] => some []
  | x :: xs => if x.im = 0 then (result xs).map (x.re :: ·) else none

omit [DecidableEq F] in
private theorem reverse_trace (xs out : List F) :
    ∃ c, Trace (a := a) (b := b) (xs.length + 2) (.reverse xs out) c
      (.done (some (xs.reverse ++ out))) := by
  induction xs generalizing out with
  | nil => exact ⟨_, Trace.cons Step.reversed (Trace.cons Step.emit (Trace.nil _))⟩
  | cons x xs ih =>
      obtain ⟨c, ht⟩ := ih (x :: out)
      refine ⟨charge 5 0 0 0 + c, ?_⟩
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using Trace.cons Step.reverse ht

/-- A failed coordinate discards the partial output; otherwise accumulated cells are reversed. -/
theorem scan_trace (xs : List (QuadraticAlgebra F a b)) (out : List F) :
    ∃ n c, n ≤ 2 * xs.length + out.length + 3 ∧ Trace n (.scan xs out) c
      (.done ((result xs).map (out.reverse ++ ·))) := by
  induction xs generalizing out with
  | nil =>
      obtain ⟨c, ht⟩ := reverse_trace (a := a) (b := b) out []
      refine ⟨out.length + 3, charge 3 0 0 0 + c, by simp, ?_⟩
      simpa [result] using Trace.cons Step.finish ht
  | cons x xs ih =>
      by_cases hx : x.im = 0
      · obtain ⟨n, c, hn, ht⟩ := ih (x.re :: out)
        refine ⟨n + 1, charge 6 1 0 0 + c, ?_, ?_⟩
        · simp only [List.length_cons] at hn ⊢; omega
        · simpa [result, hx, Option.map_map, Function.comp_def,
            List.reverse_cons, List.append_assoc] using
            Trace.cons (Step.accepted hx) ht
      · refine ⟨2, charge 3 1 0 0 + (charge 2 0 0 1 + 0), by omega, ?_⟩
        simpa [result, hx] using Trace.cons (Step.rejected hx)
          (Trace.cons Step.emit (Trace.nil _))

/-- Descent returns its exact checked projection and a bound on the same execution. -/
theorem descent_runFuel (xs : List (QuadraticAlgebra F a b)) :
    ∃ c, runFuel (2 * xs.length + 4) (.start xs) = (.done (result xs), c) ∧
      c.total ≤ 8 * (2 * xs.length + 4) := by
  obtain ⟨n, c, hn, ht⟩ := scan_trace xs []
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hn ht
  have h := Trace.cons Step.start ht
  have hr := h.runFuel_done (2 * xs.length + 4 - (n + 1))
  rw [Nat.add_sub_of_le (show n + 1 ≤ 2 * xs.length + 4 by omega)] at hr
  exact ⟨_, by simpa using hr, h.total_le.trans (Nat.mul_le_mul_left 8 (by omega))⟩

end QuadraticAlgebra.CoefficientDescentMachine
