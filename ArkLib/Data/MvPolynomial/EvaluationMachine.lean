/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Closed evaluation of materialized sparse polynomial terms

A term is a scalar coefficient and a list of variable-index/exponent pairs. Terms and variable
values are already materialized lists. Duplicate variables and terms, zero coefficients and zero
exponents are allowed without normalization. Out-of-range variable lookup returns zero, after
actually traversing the available list. The canonical polynomial uses variables indexed by `ℕ`,
with the supplied finite values extended by zero.

The fixed control phases have no callbacks, polynomial evaluation, or power primitive. Each power
runs an explicit multiplication loop. Costs count field additions/multiplications, phase dispatches,
data accesses, natural zero tests/predecessors, and scalar outputs. Reading a list cell retrieves
its record and tail together; unchanged frame registers are retained, not copied. Literal constants
are free. Dispatch includes list-constructor tests and phase changes. The cost table below specifies
all remaining register/list accesses. Input construction, host interpreter fuel bookkeeping, field
bit costs and conversion from another polynomial representation are separate obligations.
-/

@[expose] public section

namespace MvPolynomial.EvaluationMachine

/-- A materialized sparse term; repeated indices denote repeated factors. -/
abbrev Term (F : Type*) := F × List (ℕ × ℕ)

/-- Abstract primitive operation counts. Natural operations are zero tests and predecessors. -/
@[ext] structure Cost where
  additions : ℕ
  multiplications : ℕ
  control : ℕ
  data : ℕ
  natural : ℕ
  output : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b =>
  ⟨a.additions + b.additions, a.multiplications + b.multiplications,
    a.control + b.control, a.data + b.data, a.natural + b.natural, a.output + b.output⟩⟩

@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0, 0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.additions + b.additions, a.multiplications + b.multiplications,
      a.control + b.control, a.data + b.data, a.natural + b.natural, a.output + b.output⟩ := rfl
@[simp] theorem cost_add_zero (a : Cost) : a + 0 = a := by cases a; rfl

private theorem cost_add_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

/-- Read empty terms and accumulator; emit one scalar. -/
def emitCost : Cost := ⟨0, 0, 1, 2, 0, 1⟩
/-- Read a term cell; write remaining terms, factors, and product. -/
def termCost : Cost := ⟨0, 0, 1, 4, 0, 0⟩
/-- Read empty factors, accumulator and product; write their sum. -/
def addCost : Cost := ⟨1, 0, 1, 4, 0, 0⟩
/-- Read a factor cell and the value-list root; write factors, cursor, index and exponent. -/
def factorCost : Cost := ⟨0, 0, 1, 6, 0, 0⟩
/-- Read an empty value cursor and write literal zero as the base. -/
def missCost : Cost := ⟨0, 0, 1, 2, 0, 0⟩
/-- Read index and value cell, test zero, and write the selected base. -/
def hitCost : Cost := ⟨0, 0, 1, 3, 1, 0⟩
/-- Read index and value cell, test/decrement index, write index and cursor. -/
def seekCost : Cost := ⟨0, 0, 1, 4, 2, 0⟩
/-- Read and test the exhausted exponent. -/
def powerDoneCost : Cost := ⟨0, 0, 1, 1, 1, 0⟩
/-- Read exponent, product and base; test/decrement exponent, multiply and write two registers. -/
def multiplyCost : Cost := ⟨0, 1, 1, 5, 2, 0⟩

/-- The literal control phases, with only the registers needed by the current phase. -/
inductive Configuration (F : Type*) where
  | terms (remaining : List (Term F)) (acc : F)
  | factors (remaining : List (Term F)) (acc product : F) (pairs : List (ℕ × ℕ))
  | lookup (remaining : List (Term F)) (acc product : F) (pairs : List (ℕ × ℕ))
      (exponent index : ℕ) (cursor : List F)
  | power (remaining : List (Term F)) (acc product : F) (pairs : List (ℕ × ℕ))
      (base : F) (exponent : ℕ)
  | done (value : F)
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F]

/-- Independent closed transition rules; each rule fixes both the update and its charge. -/
inductive Step (values : List F) : Configuration F → Cost → Configuration F → Prop where
  | emit {a} : Step values (.terms [] a) emitCost (.done a)
  | term {c fs ts a} : Step values (.terms ((c, fs) :: ts) a) termCost (.factors ts a c fs)
  | add {ts a p} : Step values (.factors ts a p []) addCost (.terms ts (a + p))
  | factor {ts a p i e fs} : Step values (.factors ts a p ((i, e) :: fs)) factorCost
      (.lookup ts a p fs e i values)
  | miss {ts a p fs e i} : Step values (.lookup ts a p fs e i []) missCost
      (.power ts a p fs 0 e)
  | hit {ts a p fs e x xs} : Step values (.lookup ts a p fs e 0 (x :: xs)) hitCost
      (.power ts a p fs x e)
  | seek {ts a p fs e i x xs} : Step values (.lookup ts a p fs e (i + 1) (x :: xs)) seekCost
      (.lookup ts a p fs e i xs)
  | powerDone {ts a p fs x} : Step values (.power ts a p fs x 0) powerDoneCost
      (.factors ts a p fs)
  | multiply {ts a p fs x e} : Step values (.power ts a p fs x (e + 1)) multiplyCost
      (.power ts a (p * x) fs x e)

/-- Executable dispatch uses only list destructors, scalar arithmetic and natural predecessors. -/
def step (values : List F) : Configuration F → Option (Configuration F × Cost)
  | .done _ => none
  | .terms [] a => some (.done a, emitCost)
  | .terms ((c, fs) :: ts) a => some (.factors ts a c fs, termCost)
  | .factors ts a p [] => some (.terms ts (a + p), addCost)
  | .factors ts a p ((i, e) :: fs) => some (.lookup ts a p fs e i values, factorCost)
  | .lookup ts a p fs e _ [] => some (.power ts a p fs 0 e, missCost)
  | .lookup ts a p fs e 0 (x :: _) => some (.power ts a p fs x e, hitCost)
  | .lookup ts a p fs e (i + 1) (_ :: xs) => some (.lookup ts a p fs e i xs, seekCost)
  | .power ts a p fs _ 0 => some (.factors ts a p fs, powerDoneCost)
  | .power ts a p fs x (e + 1) => some (.power ts a (p * x) fs x e, multiplyCost)

/-- Every independent rule is implemented with the same charge. -/
theorem Step.step_eq {values : List F} {s t : Configuration F} {c : Cost}
    (h : Step values s c t) : step values s = some (t, c) := by
  cases h <;> rfl

/-- Every executable transition satisfies an independent rule. -/
theorem step_sound {values : List F} {s t : Configuration F} {c : Cost}
    (h : step values s = some (t, c)) : Step values s c t := by
  cases s with
  | done a => simp [step] at h
  | terms ts a =>
      cases ts with
      | nil => cases h; exact Step.emit
      | cons term ts => cases term; cases h; exact Step.term
  | factors ts a p fs =>
      cases fs with
      | nil => cases h; exact Step.add
      | cons pair fs => cases pair; cases h; exact Step.factor
  | lookup ts a p fs e i xs =>
      cases xs with
      | nil => cases h; exact Step.miss
      | cons x xs =>
          cases i with
          | zero => cases h; exact Step.hit
          | succ i => cases h; exact Step.seek
  | power ts a p fs x e =>
      cases e with
      | zero => cases h; exact Step.powerDone
      | succ e => cases h; exact Step.multiply

/-- Both successor and charge are uniquely fixed. -/
theorem Step.deterministic {values : List F} {s t u : Configuration F} {c d : Cost}
    (h : Step values s c t) (h' : Step values s d u) : t = u ∧ c = d := by
  simpa only [Option.some.injEq, Prod.mk.injEq] using h.step_eq.symm.trans h'.step_eq

/-- A finite execution trace sums the charges of its actual transitions. -/
inductive Trace (values : List F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace values 0 s 0 s
  | cons {n s u t c d} (head : Step values s c u) (tail : Trace values n u d t) :
      Trace values (n + 1) s (c + d) t

/-- Compose actual traces without adding an uncharged evaluation step. -/
theorem Trace.trans {values : List F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace values n s c u) (h' : Trace values m u d t) :
    Trace values (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cost_add_assoc] using
        Trace.cons head (ih h')

/-- Fuel execution returns the reached phase, so exhaustion is distinguishable from output. -/
def runFuel (values : List F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step values s with
      | none => (s, 0)
      | some (t, c) =>
          let result := runFuel values n t
          (result.1, c + result.2)

/-- The interpreter produces a trace of at most its supplied fuel, with identical charges. -/
theorem runFuel_refines (values : List F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace values n s (runFuel values fuel s).2 (runFuel values fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step values s with
      | none =>
          exact ⟨0, Nat.zero_le _, by
            simpa [runFuel, hs] using Trace.nil (values := values) s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- A trace's exact fuel executes all its transitions and no others. -/
theorem Trace.runFuel_eq {values : List F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace values n s c t) : runFuel values n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Total number of charged primitive operations. -/
def Cost.total (c : Cost) : ℕ :=
  c.additions + c.multiplications + c.control + c.data + c.natural + c.output

@[simp] theorem Cost.total_add (c d : Cost) : (c + d).total = c.total + d.total := by
  simp [Cost.total, Nat.add_comm, Nat.add_left_comm]

/-- Each literal dispatch charges at most nine primitive operations. -/
theorem Step.total_le {values : List F} {s t : Configuration F} {c : Cost}
    (h : Step values s c t) : c.total ≤ 9 := by
  cases h <;> decide

/-- Every finite trace has a linear primitive-operation bound. -/
theorem Trace.total_le {values : List F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace values n s c t) : c.total ≤ 9 * n := by
  induction h with
  | nil s => decide
  | cons head tail ih =>
      rw [Cost.total_add]
      have hhead := head.total_le
      omega

/-- Exact lookup cost, including the final successful or failed read. -/
def lookupCost : ℕ → ℕ → Cost
  | _, 0 => missCost
  | 0, _ + 1 => hitCost
  | i + 1, n + 1 => seekCost + lookupCost i n

/-- Exact multiplication-loop cost, including the final zero test. -/
def powerCost (e : ℕ) : Cost := ⟨0, e, e + 1, 5 * e + 1, 2 * e + 1, 0⟩

/-- Exact factor-list cost, excluding the enclosing term's addition. -/
def factorsCost (n : ℕ) : List (ℕ × ℕ) → Cost
  | [] => 0
  | (i, e) :: fs => factorCost + (lookupCost i n + (powerCost e + factorsCost n fs))

/-- Exact full cost from a term-list header through scalar emission. -/
def evaluationCost (n : ℕ) : List (Term F) → Cost
  | [] => emitCost
  | (_, fs) :: ts => termCost + (factorsCost n fs + (addCost + evaluationCost n ts))

/-- Number of transitions for factor processing, including lookup and all multiplications. -/
def factorsSteps (n : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (i, e) :: fs => min i n + e + 3 + factorsSteps n fs

/-- Exact fuel; each term adds two transitions and final emission adds one. -/
def evaluationSteps (n : ℕ) : List (Term F) → ℕ
  | [] => 1
  | (_, fs) :: ts => factorsSteps n fs + 2 + evaluationSteps n ts

/-- Factor fuel is the sum of each lookup length, exponent, and three phase transitions. -/
theorem factorsSteps_eq_sum (n : ℕ) (fs : List (ℕ × ℕ)) :
    factorsSteps n fs = (fs.map fun p => min p.1 n + p.2 + 3).sum := by
  induction fs with
  | nil => rfl
  | cons p fs ih => cases p; simp [factorsSteps, ih]

omit [CommSemiring F] in
/-- Closed input-size formula for the exact terminating fuel. -/
theorem evaluationSteps_eq_sum (n : ℕ) (ts : List (Term F)) :
    evaluationSteps n ts = 1 + 2 * ts.length +
      ((ts.flatMap Prod.snd).map fun p => min p.1 n + p.2 + 3).sum := by
  induction ts with
  | nil => rfl
  | cons term ts ih =>
      obtain ⟨c, fs⟩ := term
      simp [evaluationSteps, factorsSteps_eq_sum, ih, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Mathematical factor value. Powers occur here only in the specification. -/
def factorValue (values : List F) : List (ℕ × ℕ) → F
  | [] => 1
  | (i, e) :: fs => values.getD i 0 ^ e * factorValue values fs

/-- Mathematical sum of term values, without any assumption of normalization. -/
def termValue (values : List F) : List (Term F) → F
  | [] => 0
  | (c, fs) :: ts => c * factorValue values fs + termValue values ts

/-- Lookup is implemented by exactly `min index length + 1` transitions, including failure. -/
theorem lookup_trace (values xs : List F) (ts : List (Term F)) (a p : F)
    (fs : List (ℕ × ℕ)) (e i : ℕ) :
    Trace values (min i xs.length + 1) (.lookup ts a p fs e i xs) (lookupCost i xs.length)
      (.power ts a p fs (xs.getD i 0) e) := by
  induction xs generalizing i with
  | nil => simpa [lookupCost, missCost] using
      Trace.cons (Step.miss (values := values) (ts := ts) (a := a) (p := p)
        (fs := fs) (e := e) (i := i)) (Trace.nil _)
  | cons x xs ih =>
      cases i with
      | zero => simpa [lookupCost] using
          Trace.cons (Step.hit (values := values) (ts := ts) (a := a) (p := p)
            (fs := fs) (e := e) (x := x) (xs := xs)) (Trace.nil _)
      | succ i => simpa [lookupCost, Nat.add_assoc] using Trace.cons Step.seek (ih i)

/-- A power consumes one multiplication per exponent unit; no power primitive is executed. -/
theorem power_trace (values : List F) (ts : List (Term F)) (a p x : F)
    (fs : List (ℕ × ℕ)) (e : ℕ) :
    Trace values (e + 1) (.power ts a p fs x e) (powerCost e)
      (.factors ts a (p * x ^ e) fs) := by
  induction e generalizing p with
  | zero => simpa [powerCost, powerDoneCost] using
      Trace.cons (Step.powerDone (values := values) (ts := ts) (a := a) (p := p)
        (fs := fs) (x := x)) (Trace.nil _)
  | succ e ih =>
      simpa [powerCost, multiplyCost, pow_succ, mul_assoc, mul_comm, mul_left_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add, Nat.add_mul] using
          Trace.cons Step.multiply (ih (p * x))

/-- Every factor uses the independent lookup and multiplication traces. -/
theorem factors_trace (values : List F) (ts : List (Term F)) (a p : F)
    (fs : List (ℕ × ℕ)) :
    Trace values (factorsSteps values.length fs) (.factors ts a p fs)
      (factorsCost values.length fs) (.factors ts a (p * factorValue values fs) []) := by
  induction fs generalizing p with
  | nil => simpa [factorsSteps, factorsCost, factorValue] using
      Trace.nil (values := values) (.factors ts a p [])
  | cons pair fs ih =>
      obtain ⟨i, e⟩ := pair
      have h := Trace.cons Step.factor
        ((lookup_trace values values ts a p fs e i).trans
          ((power_trace values ts a p (values.getD i 0) fs e).trans
            (ih (p * values.getD i 0 ^ e))))
      convert h using 1 <;>
        simp [factorsSteps, factorsCost, factorValue, mul_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega

/-- Term accumulation terminates with its semantic value and exact transition charges. -/
theorem evaluation_trace (values : List F) (ts : List (Term F)) (a : F) :
    Trace values (evaluationSteps values.length ts) (.terms ts a)
      (evaluationCost values.length ts) (.done (a + termValue values ts)) := by
  induction ts generalizing a with
  | nil => simpa [evaluationSteps, evaluationCost, termValue] using
      Trace.cons (Step.emit (values := values) (a := a)) (Trace.nil _)
  | cons term ts ih =>
      obtain ⟨c, fs⟩ := term
      have h := Trace.cons Step.term
        ((factors_trace values ts a c fs).trans
          (Trace.cons Step.add (ih (a + c * factorValue values fs))))
      convert h using 1 <;>
        simp [evaluationSteps, evaluationCost, termValue, add_assoc,
          Nat.add_comm, Nat.add_left_comm]
      omega

/-- Exact executable result and cost for the materialized input. -/
theorem evaluation_runFuel (values : List F) (ts : List (Term F)) :
    runFuel values (evaluationSteps values.length ts) (.terms ts 0) =
      (.done (termValue values ts), evaluationCost values.length ts) := by
  simpa using (evaluation_trace values ts 0).runFuel_eq

/-- The exact cost is at most nine operations per transition in the explicit input-size formula. -/
theorem evaluationCost_total_le (values : List F) (ts : List (Term F)) :
    (evaluationCost values.length ts).total ≤ 9 * evaluationSteps values.length ts :=
  (evaluation_trace values ts 0).total_le

/-- Canonical multivariate monomial product denoted by a factor list. -/
noncomputable def factorsPolynomial : List (ℕ × ℕ) → MvPolynomial ℕ F
  | [] => 1
  | (i, e) :: fs => MvPolynomial.X i ^ e * factorsPolynomial fs

/-- Canonical multivariate polynomial denoted by the materialized sparse terms. -/
noncomputable def sparsePolynomial : List (Term F) → MvPolynomial ℕ F
  | [] => 0
  | (c, fs) :: ts => MvPolynomial.C c * factorsPolynomial fs + sparsePolynomial ts

/-- The factor specification is canonical evaluation with out-of-range indices assigned zero. -/
theorem eval_factorsPolynomial (values : List F) (fs : List (ℕ × ℕ)) :
    MvPolynomial.eval (fun i => values.getD i 0) (factorsPolynomial fs) =
      factorValue values fs := by
  induction fs with
  | nil => simp [factorsPolynomial, factorValue]
  | cons pair fs ih =>
      obtain ⟨i, e⟩ := pair
      simp only [factorsPolynomial, factorValue, eval_mul, eval_pow, eval_X, ih]

/-- The term specification evaluates the canonical polynomial, including duplicate entries. -/
theorem eval_sparsePolynomial (values : List F) (ts : List (Term F)) :
    MvPolynomial.eval (fun i => values.getD i 0) (sparsePolynomial ts) = termValue values ts := by
  induction ts with
  | nil => simp [sparsePolynomial, termValue]
  | cons term ts ih =>
      obtain ⟨c, fs⟩ := term
      simp only [sparsePolynomial, termValue, eval_add, eval_mul, eval_C, ih,
        eval_factorsPolynomial]

/-- Closed execution refines canonical multivariate evaluation with exactly the proved cost. -/
theorem evaluation_runFuel_eq_eval (values : List F) (ts : List (Term F)) :
    runFuel values (evaluationSteps values.length ts) (.terms ts 0) =
      (.done (MvPolynomial.eval (fun i => values.getD i 0) (sparsePolynomial ts)),
        evaluationCost values.length ts) := by
  rw [eval_sparsePolynomial, evaluation_runFuel]

end MvPolynomial.EvaluationMachine
