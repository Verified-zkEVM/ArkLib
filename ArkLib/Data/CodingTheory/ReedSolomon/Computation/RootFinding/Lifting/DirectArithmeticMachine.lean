/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.QuadraticEvaluationMachine
/-!
# Base-instruction execution of the direct coefficient arithmetic tail

Only the local arithmetic phases are represented. Residual recovery, coefficient update and
lookup must deliver the two already materialized coordinate operands before this machine starts.
No residual callback or inherited residual cost is assumed. Negation, addition, equality, inverse
and product each suspend into the existing quadratic arithmetic instruction program.

Launch charges two control operations (phase selection and call setup) and ten data accesses
for operand/parameter reads, the three input registers and the saved continuation. The zero-test
also allocates two zero coordinates with two literal writes. Every child retains its complete
base ledger and a parent wrapper. Pair return charges one dispatch and five accesses; Boolean
return charges two dispatches and six accesses for branch selection and retained operands.
Immutable operands are shared. Host fuel, input preparation and bit costs remain outside scope.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.DirectArithmeticMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost cost_assoc total_add cost_add_zero
  cost_zero_add delegated)

abbrev Pair (F : Type*) := F × F

/-- Precisely the arithmetic suffix of the direct coefficient control graph. -/
inductive Phase (K : Type*) where
  | negate (beta one : K)
  | slope (negativeBeta one : K)
  | test (negativeBeta slope : K)
  | invert (negativeBeta slope : K)
  | multiply (negativeBeta inverse : K)
  | emit (result : Option K)
  | done (result : Option K)
  deriving DecidableEq, Repr

/-- A fixed result destination, with no function-valued continuation. -/
inductive Continuation (F : Type*) where
  | negate (one : Pair F)
  | slope (negativeBeta : Pair F)
  | test (negativeBeta slope : Pair F)
  | invert (negativeBeta : Pair F)
  | multiply
  deriving DecidableEq, Repr

/-- Install the emitted scalar, or branch on the actual Boolean emitted by equality. -/
def resume {F : Type*} : Continuation F → ArithmeticMachine.Result F → Option (Phase (Pair F))
  | .negate one, .pair p => some (.slope p one)
  | .slope b, .pair p => some (.test b p)
  | .test b s, .boolean flag => some (if flag then .emit none else .invert b s)
  | .invert b, .pair p => some (.multiply b p)
  | .multiply, .pair p => some (.emit (some p))
  | _, _ => none

/-- Call setup retains the operands and parameter as already materialized pair registers. -/
def launch : Cost := ⟨{ control := 2, data := 10 }, 0⟩
/-- Equality constructs its explicit zero argument. -/
def zeroArgument : Cost := ⟨{ data := 2, constants := 2 }, 0⟩
/-- Pair installation and Boolean branching have separate administrative ledgers. -/
def returned {F : Type*} : ArithmeticMachine.Result F → Cost
  | .pair _ => ⟨{ control := 1, data := 5 }, 0⟩
  | .boolean _ => ⟨{ control := 2, data := 6 }, 0⟩
/-- Emit the final tagged scalar after all arithmetic has completed. -/
def emitCost : Cost := ⟨{ control := 1, data := 2, output := 1 }, 0⟩

inductive Configuration (F : Type*) where
  | ready (phase : Phase (Pair F))
  | call (continuation : Continuation F) (input : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)

variable {F : Type*} [Field F] [DecidableEq F]

/-- No extension-field operation occurs in dispatch or continuation resumption. -/
def step (a : F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.negate b one) => some (.call (.negate one) ⟨a, b, b⟩ (.start .neg), launch)
  | .ready (.slope b one) => some (.call (.slope b) ⟨a, one, b⟩ (.start .add), launch)
  | .ready (.test b s) =>
      some (.call (.test b s) ⟨a, s, (0, 0)⟩ (.start .equal), launch + zeroArgument)
  | .ready (.invert b s) => some (.call (.invert b) ⟨a, s, s⟩ (.start .inv), launch)
  | .ready (.multiply b v) => some (.call .multiply ⟨a, b, v⟩ (.start .mul), launch)
  | .ready (.emit out) => some (.ready (.done out), emitCost)
  | .ready (.done _) => none
  | .call k _ (.done r) => (resume k r).map (fun p => (.ready p, returned r))
  | .call k input s => (ArithmeticMachine.step input s).map
      (fun z => (.call k input z.1, delegated z.2))

/-- Every trace edge is the actual executable successor and complete charge. -/
inductive Trace (a : F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a 0 s 0 s
  | cons {n s u t c d} (head : step a s = some (u, c)) (tail : Trace a n u d t) :
      Trace a (n + 1) s (c + d) t

/-- One instruction, including its actual ledger. -/
theorem single {a : F} {s t : Configuration F} {c : Cost} (h : step a s = some (t, c)) :
    Trace a 1 s c t := by simpa using (Trace.cons h (Trace.nil t))

/-- Append actual lowered phase executions. -/
theorem Trace.trans {a : F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a n s c u) (h' : Trace a m u d t) : Trace a (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- A bounded interpreter preserves suspended arithmetic on exhaustion. -/
def runFuel (a : F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a n t; (r.1, c + r.2)

/-- The certified local trace is the same execution as the interpreter. -/
theorem Trace.runFuel_eq {a : F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a n s c t) : runFuel a n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end ReedSolomon.HiddenDerivative.DirectArithmeticMachine
