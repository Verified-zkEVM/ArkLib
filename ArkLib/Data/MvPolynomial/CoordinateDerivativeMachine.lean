/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.PartialDerivativeMachine
public import ArkLib.Data.MvPolynomial.CoordinateNormalizeMachine

/-!
# Coordinate sparse differentiation

The factor cursor and repeated-addition counter are explicit. Actual base addition scales each
coefficient; actual pair equality detects characteristic cancellation. Prefix restoration and
term emission retain source order. Literal zeros, operands and every child instruction are charged.
-/

@[expose] public section

namespace MvPolynomial.QuadraticDerivativeMachine

open QuadraticAlgebra
open QuadraticEvaluationMachine (Cost delegated cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Term (F : Type*) := EvaluationMachine.Term (Pair F)
abbrev administrative := QuadraticNormalizeMachine.administrative
abbrev launch := QuadraticNormalizeMachine.launch
abbrev zeroSeed := QuadraticNormalizeMachine.zeroSeed

/-- Calls retain the exact counter, coefficient and factor/term cursors. -/
inductive Continuation (F : Type*) where
  | add (coefficient : Pair F) (remaining : ℕ) (factors saved : List (ℕ × ℕ))
      (terms output : List (Term F))
  | test (coefficient : Pair F) (factors saved : List (ℕ × ℕ)) (terms output : List (Term F))

inductive Configuration (F : Type*) where
  | ready (state : PartialDerivativeMachine.Configuration (Pair F))
  | call (continuation : Continuation F) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)

variable {F : Type*} [Field F] [DecidableEq F]

/-- One cursor step or one actual base instruction, never a natural-to-field cast. -/
def step (a : F) (j : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .ready (.terms ((c, fs) :: ts) out) => some (.ready (.scan c fs [] ts out),
      administrative (PartialDerivativeMachine.charge 0 4 0 0 0))
  | .ready (.terms [] out) => some (.ready (.reverse out []),
      administrative (PartialDerivativeMachine.charge 0 3 0 0 0))
  | .ready (.scan _ [] _ ts out) => some (.ready (.terms ts out),
      administrative (PartialDerivativeMachine.charge 0 1 0 0 0))
  | .ready (.scan c ((i, e) :: fs) pre ts out) => if i = j then match e with
      | 0 => some (.ready (.terms ts out),
          administrative (PartialDerivativeMachine.charge 0 2 2 0 0))
      | k + 1 => some (.ready (.scale c (k + 1) (0, 0) ((i, k) :: fs) pre ts out),
          administrative (PartialDerivativeMachine.charge 0 7 3 0 0) + zeroSeed)
      else some (.ready (.scan c fs ((i, e) :: pre) ts out),
        administrative (PartialDerivativeMachine.charge 0 6 1 0 0))
  | .ready (.scale c (k + 1) v fs pre ts out) =>
      some (.call (.add c k fs pre ts out) ⟨a, v, c⟩ (.start .add), launch)
  | .ready (.scale _ 0 v fs pre ts out) => some (.ready (.test v fs pre ts out),
      administrative (PartialDerivativeMachine.charge 0 1 1 0 0))
  | .ready (.test c fs pre ts out) =>
      some (.call (.test c fs pre ts out) ⟨a, c, (0, 0)⟩ (.start .equal), launch + zeroSeed)
  | .ready (.restore c (x :: xs) fs ts out) => some (.ready (.restore c xs (x :: fs) ts out),
      administrative (PartialDerivativeMachine.charge 0 5 0 0 0))
  | .ready (.restore c [] fs ts out) => some (.ready (.terms ts ((c, fs) :: out)),
      administrative (PartialDerivativeMachine.charge 0 5 0 0 1))
  | .ready (.reverse (t :: ts) out) => some (.ready (.reverse ts (t :: out)),
      administrative (PartialDerivativeMachine.charge 0 5 0 0 0))
  | .ready (.reverse [] out) => some (.ready (.done out),
      administrative (PartialDerivativeMachine.charge 0 2 0 0 1))
  | .ready (.done _) => none
  | .call k payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.call k payload t, delegated c)
      | none => match s, k with
          | .done (.pair p), .add c n fs pre ts out =>
              some (.ready (.scale c n p fs pre ts out),
                administrative (PartialDerivativeMachine.charge 1 5 2 0 0))
          | .done (.boolean b), .test c fs pre ts out =>
              some ((if b then .ready (.terms ts out) else .ready (.restore c pre fs ts out)),
                administrative (PartialDerivativeMachine.charge 0 2 0 1 0))
          | _, _ => none

/-- Concrete edges accumulate their full base ledger. -/
inductive Trace (a : F) (j : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a j 0 s 0 s
  | cons {n s u t c d} (head : step a j s = some (u, c)) (tail : Trace a j n u d t) :
      Trace a j (n + 1) s (c + d) t

/-- Execute one edge. -/
theorem single {a : F} {j : ℕ} {s t : Configuration F} {c : Cost} (h : step a j s = some (t, c)) :
    Trace a j 1 s c t := by simpa using Trace.cons h (Trace.nil t)

/-- Concatenate concrete traces and ledgers. -/
theorem Trace.trans {a : F} {j : ℕ} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a j n s c u) (h' : Trace a j m u d t) : Trace a j (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel exposes partially completed equality and addition calls. -/
def runFuel (a : F) (j : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a j s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a j n t; (r.1, c + r.2)

/-- Exact trace fuel recovers its endpoint and complete cost. -/
theorem Trace.runFuel_eq {a : F} {j : ℕ} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a j n s c t) : runFuel a j n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end MvPolynomial.QuadraticDerivativeMachine
