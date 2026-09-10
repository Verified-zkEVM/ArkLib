/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.HornerMachine
public import ArkLib.Data.CodingTheory.ReedSolomon
public import CompPoly.Univariate.ToPoly.Impl
-- The representation theorem intentionally reduces CompPoly's coefficient array and evaluator.
import all CompPoly.Univariate.Basic
/-!
# Closed agreement counting with an integer threshold

This fixed machine scans an explicit list of point/value pairs and runs the closed Horner program
on every point. Each Horner transition is an outer transition with the same charge, not an opaque
unit-cost evaluation. The remaining control phases start a call, return its value, compare it with
the received value, update an integer counter, and test the supplied integer threshold `A`.
There are no host callbacks or real-gap computations in the executable machine.

Inputs are a materialized immutable descending coefficient list and a materialized point/value
list. Restarting Horner shares the coefficient-list pointer; it does not copy its cells. Input
conversion, allocation, and preparation are separate obligations. Natural counter addition and
threshold comparison are explicit abstract operations, not bit-cost claims. The model inherits
Horner's abstract field/data-access interpretation and excludes host interpreter bookkeeping.

Outer phase dispatch is charged once per outer instruction; during a Horner call its instruction
dispatch is the machine dispatch. Output counts include each Horner return value plus the two
components of the final count/acceptance result. This file certifies one polynomial's acceptance,
not degree checking, candidate enumeration, or a complete decoder.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementMachine

open Polynomial

/-- Horner's operation vector plus field equality and integer-counter operations. -/
@[ext]
structure Cost where
  machine : HornerMachine.Cost
  equalities : ℕ
  counterUpdates : ℕ
  thresholdTests : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b =>
  ⟨a.machine + b.machine, a.equalities + b.equalities,
    a.counterUpdates + b.counterUpdates, a.thresholdTests + b.thresholdTests⟩⟩

@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0⟩ := rfl

@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.machine + b.machine, a.equalities + b.equalities,
      a.counterUpdates + b.counterUpdates, a.thresholdTests + b.thresholdTests⟩ := rfl

/-- Lift an actual Horner instruction charge, adding no hidden equality or counter work. -/
def embedCost (c : HornerMachine.Cost) : Cost := ⟨c, 0, 0, 0⟩

@[simp] theorem embedCost_zero : embedCost 0 = 0 := rfl
@[simp] theorem embedCost_add (a b : HornerMachine.Cost) :
    embedCost (a + b) = embedCost a + embedCost b := rfl

/-- Reading the pair cell and coefficient pointer, then writing six call/frame registers. -/
def startCost : Cost := ⟨⟨0, 0, 1, 0, 8, 0⟩, 0, 0, 0⟩

/-- Read the Horner return slot and write the comparison register. -/
def returnCost : Cost := ⟨⟨0, 0, 1, 0, 2, 0⟩, 0, 0, 0⟩

/-- Read the two field values and counter, compare, add zero or one, and write the counter. -/
def compareCost : Cost := ⟨⟨0, 0, 1, 0, 4, 0⟩, 1, 1, 0⟩

/-- Read the empty-list marker, counter, and threshold; compare and emit count plus Boolean. -/
def finishCost : Cost := ⟨⟨0, 0, 1, 0, 3, 2⟩, 0, 0, 1⟩

/-- Closed control phases with a genuine suspended Horner-machine state during evaluation. -/
inductive Configuration (F : Type*) where
  | scan (remaining : List (F × F)) (count : ℕ)
  | evaluating (point received : F) (remaining : List (F × F)) (count : ℕ)
      (inner : HornerMachine.Configuration F)
  | comparing (value received : F) (remaining : List (F × F)) (count : ℕ)
  | done (count : ℕ) (accepted : Bool)
  deriving DecidableEq, Repr

variable {F : Type*} [Semiring F] [DecidableEq F]

/-- Independent operational rules for the fixed agreement program. -/
inductive Step (coefficients : List F) (A : ℕ) :
    Configuration F → Cost → Configuration F → Prop where
  | start {x y rows count} :
      Step coefficients A (.scan ((x, y) :: rows) count) startCost
        (.evaluating x y rows count (.running 0 coefficients 0 0))
  | horner {x y rows count s t c} (inner : HornerMachine.Step HornerMachine.hornerCode x s c t) :
      Step coefficients A (.evaluating x y rows count s) (embedCost c)
        (.evaluating x y rows count t)
  | returned {x y rows count value} :
      Step coefficients A (.evaluating x y rows count (.halted value)) returnCost
        (.comparing value y rows count)
  | matched {value y rows count} (equal : value = y) :
      Step coefficients A (.comparing value y rows count) compareCost (.scan rows (count + 1))
  | missed {value y rows count} (different : value ≠ y) :
      Step coefficients A (.comparing value y rows count) compareCost (.scan rows (count + 0))
  | finish {count} :
      Step coefficients A (.scan [] count) finishCost (.done count (decide (A ≤ count)))

/-- Execute one outer instruction or one actual Horner instruction,
with no opaque subroutine call. -/
def step (coefficients : List F) (A : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .done _ _ => none
  | .scan [] count => some (.done count (decide (A ≤ count)), finishCost)
  | .scan ((x, y) :: rows) count =>
      some (.evaluating x y rows count (.running 0 coefficients 0 0), startCost)
  | .evaluating _ y rows count (.halted value) =>
      some (.comparing value y rows count, returnCost)
  | .evaluating x y rows count inner@(.running _ _ _ _) =>
      match HornerMachine.step HornerMachine.hornerCode x inner with
      | none => none
      | some (next, cost) => some (.evaluating x y rows count next, embedCost cost)
  | .comparing value y rows count =>
      some (.scan rows (count + if value = y then 1 else 0), compareCost)

/-- Every operational rule is implemented with its prescribed charge. -/
theorem Step.step_eq {coefficients : List F} {A : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step coefficients A s c t) : step coefficients A s = some (t, c) := by
  cases h with
  | start => rfl
  | horner inner => cases inner <;> simp [step, HornerMachine.step, *]
  | returned => rfl
  | matched equal => simp [step, equal]
  | missed different => simp [step, different]
  | finish => rfl

/-- The executable instruction's state and cost both satisfy the independent semantics. -/
theorem step_sound {coefficients : List F} {A : ℕ} {s t : Configuration F} {c : Cost}
    (h : step coefficients A s = some (t, c)) : Step coefficients A s c t := by
  cases s with
  | done count accepted => simp [step] at h
  | scan rows count =>
      cases rows with
      | nil =>
          simp only [step, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.finish
      | cons row rows =>
          rcases row with ⟨x, y⟩
          simp only [step, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.start
  | evaluating x y rows count inner =>
      cases inner with
      | halted value =>
          simp only [step, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.returned
      | running pc remaining a current =>
          cases hi : HornerMachine.step HornerMachine.hornerCode x
              (.running pc remaining a current) with
          | none => simp [step, hi] at h
          | some pair =>
              simp only [step, hi, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact Step.horner (HornerMachine.step_sound hi)
  | comparing value y rows count =>
      by_cases heq : value = y
      · simp only [step, if_pos heq, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact Step.matched heq
      · simp only [step, if_neg heq, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact Step.missed heq

omit [DecidableEq F] in
/-- Both the next state and operation charge are deterministic. -/
theorem Step.deterministic {coefficients : List F} {A : ℕ}
    {s t u : Configuration F} {c d : Cost}
    (h : Step coefficients A s c t) (h' : Step coefficients A s d u) : t = u ∧ c = d := by
  classical
  simpa only [Option.some.injEq, Prod.mk.injEq] using h.step_eq.symm.trans h'.step_eq

/-- Finite traces sum only the charges of actual outer or embedded Horner transitions. -/
inductive Trace (coefficients : List F) (A : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace coefficients A 0 s 0 s
  | cons {n s u t c d} (head : Step coefficients A s c u)
      (tail : Trace coefficients A n u d t) : Trace coefficients A (n + 1) s (c + d) t

private theorem cost_add_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  simp [cost_add, HornerMachine.cost_add, Nat.add_assoc]

omit [DecidableEq F] in
/-- Sequential composition retains every transition and adds the two complete cost vectors. -/
theorem Trace.trans {coefficients : List F} {A n m : ℕ}
    {s u t : Configuration F} {c d : Cost}
    (h : Trace coefficients A n s c u) (h' : Trace coefficients A m u d t) :
    Trace coefficients A (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa [cost_add, HornerMachine.cost_add] using h'
  | cons head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cost_add_assoc] using
        Trace.cons head (ih h')

omit [DecidableEq F] in
/-- A Horner trace executes instruction for instruction inside the caller's suspended frame. -/
theorem Trace.horner {coefficients : List F} {A : ℕ} (x y : F) (rows : List (F × F))
    (count : ℕ) {n : ℕ} {s t : HornerMachine.Configuration F} {c : HornerMachine.Cost}
    (h : HornerMachine.Trace HornerMachine.hornerCode x n s c t) :
    Trace coefficients A n (.evaluating x y rows count s) (embedCost c)
      (.evaluating x y rows count t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih => simpa only [embedCost_add] using Trace.cons (Step.horner head) ih

/-- Fuel limits transitions; no polynomial evaluation is performed outside those transitions. -/
def runFuel (coefficients : List F) (A : ℕ) :
    ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step coefficients A s with
      | none => (s, 0)
      | some (u, c) =>
          let result := runFuel coefficients A n u
          (result.1, c + result.2)

/-- The interpreter returns precisely a prefix trace and its operation sum. -/
theorem runFuel_refines (coefficients : List F) (A fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace coefficients A n s
      (runFuel coefficients A fuel s).2 (runFuel coefficients A fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step coefficients A s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (A := A) s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn,
            by simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace length reproduces both its result and its accumulated cost. -/
theorem Trace.runFuel_eq {coefficients : List F} {A n : ℕ}
    {s t : Configuration F} {c : Cost} (h : Trace coefficients A n s c t) :
    runFuel coefficients A n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-! ## Exact count and operation bound -/

/-- Mathematical Horner specification, used only in correctness statements. -/
def valueAt (coefficients : List F) (x : F) : F :=
  coefficients.foldl (fun acc coeff => acc * x + coeff) 0

/-- Mathematical agreement specification on the supplied sequence, including repetitions. -/
def agreementCount (coefficients : List F) : List (F × F) → ℕ
  | [] => 0
  | (x, y) :: rows =>
      (if valueAt coefficients x = y then 1 else 0) + agreementCount coefficients rows

/-- Exact operation vector on `m` points with `n` supplied coefficient cells. -/
def totalCost (n m : ℕ) : Cost :=
  ⟨⟨m * n, m * n, m * (3 * n + 6) + 1, m * (3 * n + 3),
      m * (12 * n + 20) + 3, m + 2⟩, m, m, 1⟩

omit [DecidableEq F] in
private theorem full_horner_trace (coefficients : List F) (x : F) :
    HornerMachine.Trace HornerMachine.hornerCode x (3 * coefficients.length + 3)
      (.running 0 coefficients 0 0)
      (HornerMachine.hornerCost coefficients.length) (.halted (valueAt coefficients x)) := by
  unfold valueAt
  have h := HornerMachine.Trace.cons (HornerMachine.Step.reset
    (code := HornerMachine.hornerCode) (x := x)
    (pc := 0) (xs := coefficients) (a := 0) (c := 0) (by decide))
    (HornerMachine.horner_loop_trace x coefficients 0 0)
  convert h using 1
  simp [HornerMachine.hornerCost, HornerMachine.loopCost,
    HornerMachine.resetCost, HornerMachine.cost_add]
  omega

/-- The closed program computes the exact agreement count and threshold answer, with a trace
length and operation vector linear in the point count times one plus the coefficient count. -/
theorem agreement_trace (coefficients : List F) (A : ℕ) (rows : List (F × F)) (count : ℕ) :
    Trace coefficients A (rows.length * (3 * coefficients.length + 6) + 1) (.scan rows count)
      (totalCost coefficients.length rows.length)
      (.done (count + agreementCount coefficients rows)
        (decide (A ≤ count + agreementCount coefficients rows))) := by
  induction rows generalizing count with
  | nil =>
      simpa [agreementCount, totalCost, finishCost, cost_add, HornerMachine.cost_add] using
        Trace.cons (Step.finish (coefficients := coefficients) (A := A) (count := count))
          (Trace.nil _)
  | cons row rows ih =>
      rcases row with ⟨x, y⟩
      have hcall := Trace.horner (coefficients := coefficients) (A := A) x y rows count
        (full_horner_trace coefficients x)
      by_cases heq : valueAt coefficients x = y
      · have h := Trace.cons Step.start
          (hcall.trans (Trace.cons Step.returned (Trace.cons (Step.matched heq) (ih (count + 1)))))
        convert h using 1 <;>
          simp [agreementCount, heq, totalCost, startCost, returnCost, compareCost,
            embedCost, HornerMachine.hornerCost, cost_add, HornerMachine.cost_add,
            Nat.add_mul, Nat.mul_add,
            Nat.add_assoc] <;> omega
      · have h := Trace.cons Step.start
          (hcall.trans (Trace.cons Step.returned (Trace.cons (Step.missed heq) (ih (count + 0)))))
        convert h using 1 <;>
          simp [agreementCount, heq, totalCost, startCost, returnCost, compareCost,
            embedCost, HornerMachine.hornerCost, cost_add, HornerMachine.cost_add,
            Nat.add_mul, Nat.mul_add,
            Nat.add_assoc] <;> omega

/-- Exact executable output and operation vector for the supplied coefficient and point lists. -/
theorem agreement_runFuel (coefficients : List F) (A : ℕ) (rows : List (F × F)) :
    runFuel coefficients A (rows.length * (3 * coefficients.length + 6) + 1) (.scan rows 0) =
      (.done (agreementCount coefficients rows) (decide (A ≤ agreementCount coefficients rows)),
        totalCost coefficients.length rows.length) := by
  simpa using (agreement_trace coefficients A rows 0).runFuel_eq

omit [DecidableEq F] in
/-- A representation relation connects the specification to concrete polynomial evaluation.
No conversion is executed or charged implicitly by this theorem. -/
theorem valueAt_eq_eval (coefficients : List F) (p : CompPoly.CPolynomial F)
    (hcoefficients : coefficients = p.val.toList.reverse) (x : F) :
    valueAt coefficients x = p.eval x := by
  rw [valueAt, hcoefficients, List.foldl_reverse]
  change p.val.toList.foldr (fun coeff acc => acc * x + coeff) 0 = p.eval x
  rw [Array.foldr_toList]
  exact CompPoly.CPolynomial.eval_horner_eq_eval x p

private theorem agreementCount_eq_sum (coefficients : List F) (rows : List (F × F)) :
    agreementCount coefficients rows =
      (rows.map fun row => if valueAt coefficients row.1 = row.2 then 1 else 0).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨x, y⟩
      simp [agreementCount, ih]

/-- The supplied row list represents every indexed received position exactly once in order.
Under that explicit relation the machine's count is the canonical `Code.agree` value. -/
theorem agreementCount_eq_agree (coefficients : List F) (p : CompPoly.CPolynomial F)
    {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) (rows : List (F × F))
    (hcoefficients : coefficients = p.val.toList.reverse)
    (hrows : rows = List.ofFn fun i => (domain i, received i)) :
    agreementCount coefficients rows = Code.agree (evalOnPoints domain p.toPoly) received := by
  have hvalue (x : F) : valueAt coefficients x = p.toPoly.eval x :=
    (valueAt_eq_eval coefficients p hcoefficients x).trans
      (CompPoly.CPolynomial.eval_toPoly x p)
  rw [agreementCount_eq_sum, hrows]
  simp [List.map_ofFn, List.sum_ofFn, hvalue, Code.agree, evalOnPoints]
  rfl

/-- The closed agreement filter accepts precisely the requested integer agreement threshold,
with its exact operational cost. Coefficient/row preparation is an explicit precondition. -/
theorem agreement_runFuel_eq_agree (coefficients : List F) (A : ℕ)
    (p : CompPoly.CPolynomial F) {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (rows : List (F × F)) (hcoefficients : coefficients = p.val.toList.reverse)
    (hrows : rows = List.ofFn fun i => (domain i, received i)) :
    runFuel coefficients A (rows.length * (3 * coefficients.length + 6) + 1) (.scan rows 0) =
      (.done (Code.agree (evalOnPoints domain p.toPoly) received)
        (decide (A ≤ Code.agree (evalOnPoints domain p.toPoly) received)),
        totalCost coefficients.length rows.length) := by
  rw [agreement_runFuel, agreementCount_eq_agree coefficients p domain received rows
    hcoefficients hrows]

end ReedSolomon.ListDecoding.AgreementMachine
