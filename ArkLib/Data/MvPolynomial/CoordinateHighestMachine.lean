/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.HighestJetMachine
public import ArkLib.Data.MvPolynomial.CoordinateNormalizeMachine

/-!
# Coordinate highest-jet selection

Actual coordinate normalization precedes the unchanged natural-index scan. Every normalization
instruction keeps its full charge plus the parent wrapper; factor comparisons remain scalar-free.
-/

@[expose] public section

namespace MvPolynomial.QuadraticHighestMachine

open QuadraticEvaluationMachine (Cost cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Term (F : Type*) := EvaluationMachine.Term (Pair F)
abbrev administrative := QuadraticNormalizeMachine.administrative
/-- Outer child dispatch and retained-state reads/writes. -/
def wrapper : Cost := ⟨{ control := 1, data := 2 }, 0⟩

inductive Configuration (F : Type*) where
  | normalizing (state : QuadraticNormalizeMachine.Configuration F)
  | terms (pending : List (Term F)) (best : Option (ℕ × ℕ))
  | factors (pending : List (ℕ × ℕ)) (terms : List (Term F)) (best : Option (ℕ × ℕ))
  | done (best : Option (ℕ × ℕ))

variable {F : Type*} [Field F] [DecidableEq F]

/-- Execute one coordinate normalization instruction or one original index/cursor operation. -/
def step (a : F) : Configuration F → Option (Configuration F × Cost)
  | .normalizing s => match QuadraticNormalizeMachine.step a s with
      | some (t, c) => some (.normalizing t, c + wrapper)
      | none => match s with
          | .ready (.done out) => some (.terms out none,
              administrative (HighestJetMachine.charge 0 2 0 0 0))
          | _ => none
  | .terms [] b => some (.done b, administrative (HighestJetMachine.charge 0 2 0 0 1))
  | .terms ((_, fs) :: ts) b => some (.factors fs ts b,
      administrative (HighestJetMachine.charge 0 3 0 0 0))
  | .factors [] ts b => some (.terms ts b, administrative (HighestJetMachine.charge 0 2 0 0 0))
  | .factors (p :: fs) ts b => some (.factors fs ts (HighestJetMachine.update p b),
      administrative (HighestJetMachine.charge 0 6 5 0 0))
  | .done _ => none

/-- Concrete edges accumulate their full base ledger. -/
inductive Trace (a : F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a 0 s 0 s
  | cons {n s u t c d} (head : step a s = some (u, c)) (tail : Trace a n u d t) :
      Trace a (n + 1) s (c + d) t

/-- Execute one edge. -/
theorem single {a : F} {s t : Configuration F} {c : Cost} (h : step a s = some (t, c)) :
    Trace a 1 s c t := by simpa using Trace.cons h (Trace.nil t)

/-- Concatenate concrete traces and ledgers. -/
theorem Trace.trans {a : F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a n s c u) (h' : Trace a m u d t) : Trace a (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel exposes partially completed equality and addition calls. -/
def runFuel (a : F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a n t; (r.1, c + r.2)

/-- Exact trace fuel recovers its endpoint and complete cost. -/
theorem Trace.runFuel_eq {a : F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a n s c t) : runFuel a n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end MvPolynomial.QuadraticHighestMachine
