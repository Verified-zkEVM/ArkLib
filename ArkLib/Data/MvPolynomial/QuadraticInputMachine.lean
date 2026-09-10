/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.EvaluationMachine
public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine

/-!
# Materializing base-field sparse polynomials in a quadratic algebra

Each input coefficient c is explicitly replaced by the coordinate value (c,0). Factor lists
are shared unchanged; coefficient, term and outer list cells are allocated and charged.
The output order is restored by a charged reversal. There is no runtime map callback or bulk
algebra-map conversion. Only the correctness statement uses the canonical scalar embedding.
The parameter a is supplied by field setup; no field operation is needed for this conversion.
-/

@[expose] public section

namespace MvPolynomial.QuadraticInputMachine

abbrev Cost := QuadraticAlgebra.ArithmeticMachine.Cost
abbrev Term (F : Type*) := EvaluationMachine.Term F

/-- Administrative instruction cost; this conversion executes no field arithmetic. -/
def charge (data constants output : ℕ) : Cost :=
  { control := 1, data := data, constants := constants, output := output }

private theorem total_charge_add (data constants output : ℕ) (c : Cost) :
    (charge data constants output + c).total = 1 + data + constants + output + c.total := by
  change 0 + c.additions + (0 + c.multiplications) + (0 + c.negations) +
    (0 + c.inversions) + (0 + c.equalities) + (1 + c.control) +
    (data + c.data) + (constants + c.constants) + (output + c.output) = _
  simp only [QuadraticAlgebra.ArithmeticMachine.Cost.total]
  omega

/-- Cursors share input factors and retain each newly allocated coefficient explicitly. -/
inductive Configuration (F : Type*) [Zero F] (a : F) where
  | scan (remaining : List (Term F)) (saved : List (Term (QuadraticAlgebra F a 0)))
  | reverse (remaining output : List (Term (QuadraticAlgebra F a 0)))
  | emit (output : List (Term (QuadraticAlgebra F a 0)))
  | done (output : List (Term (QuadraticAlgebra F a 0)))
  deriving DecidableEq

variable {F : Type*} [Zero F] {a : F}

/-- A transition constructs at most one coefficient, one term and one outer list cell. -/
inductive Step : Configuration F a → Cost → Configuration F a → Prop where
  | coefficient {c fs ts out} :
      Step (.scan ((c, fs) :: ts) out) (charge 10 1 0)
        (.scan ts ((⟨c, 0⟩, fs) :: out))
  | scanned {out} : Step (.scan [] out) (charge 3 0 0) (.reverse out [])
  | reverse {t ts out} :
      Step (.reverse (t :: ts) out) (charge 5 0 0) (.reverse ts (t :: out))
  | reversed {out} : Step (.reverse [] out) (charge 2 0 0) (.emit out)
  | emit {out} : Step (.emit out) (charge 2 0 1) (.done out)

/-- Each dispatch reads or allocates boundedly many cells; factor tails remain immutable. -/
def step : Configuration F a → Option (Configuration F a × Cost)
  | .scan ((c, fs) :: ts) out => some (.scan ts ((⟨c, 0⟩, fs) :: out), charge 10 1 0)
  | .scan [] out => some (.reverse out [], charge 3 0 0)
  | .reverse (t :: ts) out => some (.reverse ts (t :: out), charge 5 0 0)
  | .reverse [] out => some (.emit out, charge 2 0 0)
  | .emit out => some (.done out, charge 2 0 1)
  | .done _ => none

theorem Step.step_eq {s t : Configuration F a} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by cases h <;> rfl

/-- Executable dispatch has exactly the independently specified primitive transition. -/
theorem step_sound {s t : Configuration F a} {c : Cost}
    (h : step s = some (t, c)) : Step s c t := by
  cases s with
  | scan ts out => cases ts <;> cases h <;> constructor
  | reverse ts out => cases ts <;> cases h <;> constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h

/-- Actual transitions and their complete coordinate-allocation charges. -/
inductive Trace : ℕ → Configuration F a → Cost → Configuration F a → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c e} (head : Step s c u) (tail : Trace n u e t) :
      Trace (n + 1) s (c + e) t

/-- Host fuel exposes the real suspended conversion state without doing uncharged list work. -/
def runFuel : ℕ → Configuration F a → Configuration F a × Cost
  | 0, s => (s, 0)
  | fuel + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel fuel t; (r.1, c + r.2)

/-- Every bounded interpretation has a trace with the same endpoint and charge. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration F a) :
    ∃ n ≤ fuel, Trace n s (runFuel fuel s).2 (runFuel fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil _⟩
  | succ fuel ih =>
      cases hs : step s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some p =>
          obtain ⟨n, hn, ht⟩ := ih p.1
          exact ⟨n + 1, by omega, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Completed traces remain complete under surplus fuel. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration F a} {c : Cost} {out}
    (h : Trace n s c (.done out)) (extra : ℕ) :
    runFuel (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih he]

/-- Semantic input relation only; runtime allocates these values in individual transitions. -/
def embedded (ts : List (Term F)) : List (Term (QuadraticAlgebra F a 0)) :=
  ts.map (fun t => (⟨t.1, 0⟩, t.2))

private theorem reverse_trace (ts out : List (Term (QuadraticAlgebra F a 0))) :
    ∃ c, Trace (ts.length + 2) (.reverse ts out) c (.done (ts.reverse ++ out)) ∧
      c.total = 6 * ts.length + 7 := by
  induction ts generalizing out with
  | nil => exact ⟨charge 2 0 0 + (charge 2 0 1 + 0),
      Trace.cons Step.reversed (Trace.cons Step.emit (Trace.nil _)), rfl⟩
  | cons t ts ih =>
      obtain ⟨c, ht, hc⟩ := ih (t :: out)
      refine ⟨charge 5 0 0 + c, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverse ht
      · rw [total_charge_add, hc]
        simp only [List.length_cons]
        omega

/-- The input traversal preserves exact order and pays for every coefficient and reversal cell. -/
theorem scan_trace (ts : List (Term F)) (out : List (Term (QuadraticAlgebra F a 0))) :
    ∃ c, Trace (2 * ts.length + out.length + 3) (.scan ts out) c
      (.done (out.reverse ++ embedded ts)) ∧ c.total = 18 * ts.length + 6 * out.length + 11 := by
  induction ts generalizing out with
  | nil =>
      obtain ⟨c, ht, hc⟩ := reverse_trace out []
      refine ⟨charge 3 0 0 + c, ?_, ?_⟩
      · simpa [embedded] using Trace.cons Step.scanned ht
      · rw [total_charge_add, hc]
        simp only [List.length_nil]
        omega
  | cons t ts ih =>
      obtain ⟨c, ht, hc⟩ := ih ((⟨t.1, 0⟩, t.2) :: out)
      refine ⟨charge 10 1 0 + c, ?_, ?_⟩
      · convert Trace.cons Step.coefficient ht using 1
        · simp only [List.length_cons]; omega
        · simp [embedded, List.reverse_cons, List.append_assoc]
      · rw [total_charge_add, hc]
        simp only [List.length_cons]
        omega

/-- The actual coefficient conversion is linear in sparse term count, with exact observed work. -/
theorem evaluation_runFuel (ts : List (Term F)) :
    ∃ c, runFuel (2 * ts.length + 3) (.scan ts [] : Configuration F a) =
      (.done (embedded ts), c) ∧ c.total = 18 * ts.length + 11 := by
  obtain ⟨c, ht, hc⟩ := scan_trace ts ([] : List (Term (QuadraticAlgebra F a 0)))
  exact ⟨c, by simpa using ht.runFuel_done 0, by simpa using hc⟩

end MvPolynomial.QuadraticInputMachine
