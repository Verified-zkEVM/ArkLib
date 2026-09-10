/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.SeparantChainMachine
public import ArkLib.Data.MvPolynomial.CoordinateHighestMachine
public import ArkLib.Data.MvPolynomial.CoordinateDerivativeMachine

/-!
# Coordinate separant stages

The actual coordinate highest-jet selector and sparse derivative run one instruction at a time.
Each stage retains its original equation, chosen index/exponent and ordered context. Record and
reversal cells keep the source charges; every actual child instruction pays the outer wrapper.
-/

@[expose] public section

namespace MvPolynomial.QuadraticChainMachine

open QuadraticEvaluationMachine (Cost cost_assoc total_add)

abbrev Pair (F : Type*) := F × F
abbrev Term (F : Type*) := EvaluationMachine.Term (Pair F)
abbrev Stage (F : Type*) := SeparantChainMachine.Stage (Pair F)
abbrev administrative := QuadraticNormalizeMachine.administrative
abbrev wrapper := QuadraticHighestMachine.wrapper

inductive Configuration (F : Type*) where
  | selecting (equation : List (Term F)) (saved : List (Stage F))
      (state : QuadraticHighestMachine.Configuration F)
  | record (equation : List (Term F)) (selected : Option (ℕ × ℕ)) (saved : List (Stage F))
  | derivingAt (index : ℕ) (saved : List (Stage F))
      (state : QuadraticDerivativeMachine.Configuration F)
  | reverse (pending output : List (Stage F))
  | done (stages : List (Stage F))

/-- Retain the equation and initialize the actual coordinate selector. -/
def initial {F : Type*} (ts : List (Term F)) (saved : List (Stage F) := []) : Configuration F :=
  .selecting ts saved (.normalizing (.ready (.terms ts [])))

variable {F : Type*} [Field F] [DecidableEq F]

/-- One real child instruction or one explicit stage/record/cursor operation. -/
def step (a : F) : Configuration F → Option (Configuration F × Cost)
  | .selecting eqs pre s => match QuadraticHighestMachine.step a s with
      | some (t, c) => some (.selecting eqs pre t, c + wrapper)
      | none => match s with
          | .done b => some (.record eqs b pre,
              administrative (SeparantChainMachine.charge 0 2 0 0 0))
          | _ => none
  | .record eqs none pre => some (.reverse (⟨eqs, none⟩ :: pre) [],
      administrative (SeparantChainMachine.charge 0 6 0 0 1))
  | .record eqs (some (i, e)) pre =>
      some (.derivingAt i (⟨eqs, some (i, e)⟩ :: pre) (.ready (.terms eqs [])),
        administrative (SeparantChainMachine.charge 0 8 0 0 1))
  | .derivingAt i pre s => match QuadraticDerivativeMachine.step a i s with
      | some (t, c) => some (.derivingAt i pre t, c + wrapper)
      | none => match s with
          | .ready (.done ts) => some (initial ts pre,
              administrative (SeparantChainMachine.charge 0 5 0 0 0))
          | _ => none
  | .reverse (r :: pre) out => some (.reverse pre (r :: out),
      administrative (SeparantChainMachine.charge 0 5 0 0 1))
  | .reverse [] out => some (.done out, administrative (SeparantChainMachine.charge 0 2 0 0 1))
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

end MvPolynomial.QuadraticChainMachine
