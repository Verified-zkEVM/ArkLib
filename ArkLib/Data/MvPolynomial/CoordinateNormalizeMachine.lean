/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.DenseNormalizeMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationMachine

/-!
# Coordinate sparse normalization

The original insertion and factor-key cursors are retained. Coefficient addition and zero tests
execute the actual base arithmetic programs, with retained operands, zero literals and costs.
Cancellation drops the same term; duplicate keys and input order receive no bulk processing.
-/

@[expose] public section

namespace MvPolynomial.QuadraticNormalizeMachine

open QuadraticAlgebra
open QuadraticEvaluationMachine (Cost delegated cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Term (F : Type*) := EvaluationMachine.Term (Pair F)

/-- Retain source cursor work while replacing abstract scalar arithmetic and comparison. -/
def administrative (c : DenseNormalizeMachine.Cost) : Cost :=
  ⟨{ control := c.work.control, data := c.work.data, output := c.work.output }, c.work.natural⟩
/-- Read operands and retain their three-field arithmetic input record. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩
/-- Both base zero literals and both pair slots are materialized. -/
def zeroSeed : Cost := ⟨{ data := 2, constants := 2 }, 0⟩

/-- Continuations retain the exact source lists and coefficient awaiting an equality result. -/
inductive Continuation (F : Type*) where
  | term (value : Pair F) (key : List (ℕ × ℕ)) (pending aggregate : List (Term F))
  | sum (value : Pair F) (key : List (ℕ × ℕ)) (remaining saved pending : List (Term F))
  | add (key : List (ℕ × ℕ)) (remaining saved pending : List (Term F))

inductive Configuration (F : Type*) where
  | ready (state : DenseNormalizeMachine.Configuration (Pair F))
  | call (continuation : Continuation F) (payload : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)

/-- Branch on the actual Boolean, preserving cancellation and insertion order. -/
def checked {F : Type*} (k : Continuation F) (b : Bool) : Option (Configuration F × Cost) :=
  match k with
  | .term c fs ts out => if b then
      some (.ready (.terms ts out), administrative (DenseNormalizeMachine.charge 0 2 0 1 0))
      else some (.ready (.search c fs out [] ts),
        administrative (DenseNormalizeMachine.charge 0 6 0 1 0))
  | .sum c fs rest pre ts => if b then
      some (.ready (.restore pre rest ts), administrative (DenseNormalizeMachine.charge 0 3 0 1 0))
      else some (.ready (.restore pre ((c, fs) :: rest) ts),
        administrative (DenseNormalizeMachine.charge 0 5 0 1 0))
  | .add _ _ _ _ => none

variable {F : Type*} [Field F] [DecidableEq F]

/-- One key/cursor step or one retained base arithmetic instruction. -/
def step (a : F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.terms [] out) =>
      some (.ready (.done out), administrative (DenseNormalizeMachine.charge 0 2 0 0 1))
  | .ready (.terms ((c, fs) :: ts) out) =>
      some (.call (.term c fs ts out) ⟨a, c, (0, 0)⟩ (.start .equal), launch + zeroSeed)
  | .ready (.search c fs [] pre ts) => some (.ready (.restore pre [(c, fs)] ts),
      administrative (DenseNormalizeMachine.charge 0 4 0 0 0))
  | .ready (.search c fs ((d, gs) :: rest) pre ts) =>
      some (.ready (.compare c fs (d, gs) fs gs rest pre ts),
        administrative (DenseNormalizeMachine.charge 0 8 0 0 0))
  | .ready (.compare c fs (d, _) [] [] rest pre ts) =>
      some (.call (.add fs rest pre ts) ⟨a, c, d⟩ (.start .add), launch)
  | .ready (.compare c fs t ((i, e) :: is) ((k, f) :: js) rest pre ts) =>
      if i = k ∧ e = f then some (.ready (.compare c fs t is js rest pre ts),
        administrative (DenseNormalizeMachine.charge 0 4 2 0 0))
      else some (.ready (.search c fs rest (t :: pre) ts),
        administrative (DenseNormalizeMachine.charge 0 6 2 0 0))
  | .ready (.compare c fs t [] (_ :: _) rest pre ts)
  | .ready (.compare c fs t (_ :: _) [] rest pre ts) =>
      some (.ready (.search c fs rest (t :: pre) ts),
        administrative (DenseNormalizeMachine.charge 0 5 0 0 0))
  | .ready (.sum c fs rest pre ts) =>
      some (.call (.sum c fs rest pre ts) ⟨a, c, (0, 0)⟩ (.start .equal), launch + zeroSeed)
  | .ready (.restore (t :: pre) out ts) =>
      some (.ready (.restore pre (t :: out) ts),
        administrative (DenseNormalizeMachine.charge 0 5 0 0 0))
  | .ready (.restore [] out ts) =>
      some (.ready (.terms ts out), administrative (DenseNormalizeMachine.charge 0 3 0 0 0))
  | .ready (.done _) => none
  | .call k payload s => match ArithmeticMachine.step payload s with
      | some (t, c) => some (.call k payload t, delegated c)
      | none => match s with
          | .done (.boolean b) => checked k b
          | .done (.pair p) => match k with
              | .add fs rest pre ts => some (.ready (.sum p fs rest pre ts),
                  administrative (DenseNormalizeMachine.charge 1 4 0 0 0))
              | _ => none
          | _ => none

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

end MvPolynomial.QuadraticNormalizeMachine
