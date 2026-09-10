/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.EvaluationMachine
public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine

/-!
# Sparse evaluation lowered to quadratic coordinate programs

Inputs are already materialized lists of coordinate pairs and sparse terms. Lookup traverses the
same list cells as `EvaluationMachine`; no function-valued environment or callback is executed.
Addition and multiplication suspend evaluation and run `ArithmeticMachine` one instruction at a
time. Retained frames share their immutable lists. Launch reads the operands and parameter and
allocates an input record; every child dispatch pays two root accesses; return reads the pair and
writes the continuation. A missing variable explicitly allocates the two-coordinate zero.

The semantic encoding/decoding of whole inputs is not an executable conversion. Input preparation,
host fuel bookkeeping and bit complexity remain outside this primitive-operation model.
-/

@[expose] public section

namespace MvPolynomial.QuadraticEvaluationMachine

open QuadraticAlgebra

abbrev Pair (F : Type*) := F × F

/-- Base-field instructions and natural lookup/exponent operations remain separate. -/
@[ext] structure Cost where
  base : ArithmeticMachine.Cost
  natural : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0⟩⟩
instance : Add Cost := ⟨fun c d => ⟨c.base + d.base, c.natural + d.natural⟩⟩

/-- Sum of the actual base and administrative instruction categories. -/
def Cost.total (c : Cost) : ℕ := c.base.total + c.natural

@[simp] theorem cost_add_zero (c : Cost) : c + 0 = c := by cases c; rfl
@[simp] theorem cost_zero_add (c : Cost) : 0 + c = c := by
  ext <;> change 0 + _ = _ <;> omega

/-- Componentwise addition is associative. -/
theorem cost_assoc (c d e : Cost) : (c + d) + e = c + (d + e) := by
  ext <;> change (_ + _) + _ = _ + (_ + _) <;> omega

@[simp] theorem total_add (c d : Cost) : (c + d).total = c.total + d.total := by
  change (c.base.additions + d.base.additions) +
    (c.base.multiplications + d.base.multiplications) + (c.base.negations + d.base.negations) +
    (c.base.inversions + d.base.inversions) + (c.base.equalities + d.base.equalities) +
    (c.base.control + d.base.control) + (c.base.data + d.base.data) +
    (c.base.constants + d.base.constants) + (c.base.output + d.base.output) +
    (c.natural + d.natural) = _
  simp only [Cost.total, ArithmeticMachine.Cost.total]
  omega

/-- Preserve an evaluator's administrative charge without executing extension arithmetic. -/
def administrative (c : EvaluationMachine.Cost) : Cost :=
  ⟨{ control := c.control, data := c.data, output := c.output }, c.natural⟩

/-- One delegated instruction retains its exact base ledger plus its parent wrapper. -/
def delegated (c : ArithmeticMachine.Cost) : Cost := ⟨c + { control := 1, data := 2 }, 0⟩

/-- Operand/parameter reads and input-record writes at an arithmetic call. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩

/-- Consume the emitted pair and restore the suspended continuation. -/
def returned : Cost := ⟨{ control := 1, data := 3 }, 0⟩

/-- Allocate the missing-variable coordinate zero, including two literal writes. -/
def zeroPair : Cost := ⟨{ data := 2, constants := 2 }, 0⟩

/-- Only the destination of the scalar result is suspended; other frames remain shared. -/
inductive Continuation (F : Type*) where
  | add (remaining : List (EvaluationMachine.Term (Pair F)))
  | multiply (remaining : List (EvaluationMachine.Term (Pair F))) (acc : Pair F)
      (factors : List (ℕ × ℕ)) (base : Pair F) (exponent : ℕ)
  deriving DecidableEq, Repr

/-- Install an already materialized coordinate result; this performs no field arithmetic. -/
def resume {F : Type*} :
    Continuation F → Pair F → EvaluationMachine.Configuration (Pair F)
  | .add ts, p => .terms ts p
  | .multiply ts acc fs base e, p => .power ts acc p fs base e

inductive Configuration (F : Type*) where
  | ready (state : EvaluationMachine.Configuration (Pair F))
  | call (continuation : Continuation F) (input : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Each transition either changes evaluator control or executes one base-field instruction. -/
def step (parameter : F) (values : List (Pair F)) :
    Configuration F → Option (Configuration F × Cost)
  | .ready (.done _) => none
  | .ready (.terms [] acc) => some (.ready (.done acc), administrative EvaluationMachine.emitCost)
  | .ready (.terms ((c, fs) :: ts) acc) =>
      some (.ready (.factors ts acc c fs), administrative EvaluationMachine.termCost)
  | .ready (.factors ts acc p []) =>
      some (.call (.add ts) ⟨parameter, acc, p⟩ (.start .add),
        administrative EvaluationMachine.addCost + launch)
  | .ready (.factors ts acc p ((i, e) :: fs)) =>
      some (.ready (.lookup ts acc p fs e i values),
        administrative EvaluationMachine.factorCost)
  | .ready (.lookup ts acc p fs e _ []) =>
      some (.ready (.power ts acc p fs (0, 0) e),
        administrative EvaluationMachine.missCost + zeroPair)
  | .ready (.lookup ts acc p fs e 0 (x :: _)) =>
      some (.ready (.power ts acc p fs x e), administrative EvaluationMachine.hitCost)
  | .ready (.lookup ts acc p fs e (i + 1) (_ :: xs)) =>
      some (.ready (.lookup ts acc p fs e i xs), administrative EvaluationMachine.seekCost)
  | .ready (.power ts acc p fs _ 0) =>
      some (.ready (.factors ts acc p fs),
        administrative EvaluationMachine.powerDoneCost)
  | .ready (.power ts acc p fs x (e + 1)) =>
      some (.call (.multiply ts acc fs x e) ⟨parameter, p, x⟩ (.start .mul),
        administrative EvaluationMachine.multiplyCost + launch)
  | .call k _ (.done (.pair p)) => some (.ready (resume k p), returned)
  | .call k input s => (ArithmeticMachine.step input s).map
      (fun z => (.call k input z.1, delegated z.2))

/-- The trace records the executable successor and its full concrete ledger. -/
inductive Trace (parameter : F) (values : List (Pair F)) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace parameter values 0 s 0 s
  | cons {n s u t c d} (head : step parameter values s = some (u, c))
      (tail : Trace parameter values n u d t) : Trace parameter values (n + 1) s (c + d) t

/-- Concatenate actual lowered executions. -/
theorem Trace.trans {a : F} {vs : List (Pair F)} {n m : ℕ} {s u t : Configuration F}
    {c d : Cost} (h : Trace a vs n s c u) (h' : Trace a vs m u d t) :
    Trace a vs (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel advances actual base instructions and preserves suspended calls on exhaustion. -/
def runFuel (a : F) (vs : List (Pair F)) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a vs s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel a vs n t; (z.1, c + z.2)

/-- Exact-length traces coincide with the executable run. -/
theorem Trace.runFuel_eq {a : F} {vs : List (Pair F)} {n : ℕ} {s t : Configuration F}
    {c : Cost} (h : Trace a vs n s c t) : runFuel a vs n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end MvPolynomial.QuadraticEvaluationMachine
