/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.JetHornerMachine
public import ArkLib.Data.MvPolynomial.QuadraticEvaluationMachine

/-!
# Quadratic jet Horner evaluation by base instructions

The point and descending coefficient list are materialized coordinate pairs. Initialization
allocates every coordinate zero and jet cell explicitly. An update suspends into multiplication
and addition programs, retains the OLD jet entry as the next carry, and allocates the updated
list cell in a separate save phase. Reversal and output traverse the actual materialized list.

Input construction and semantic decoding are outside execution. Each child instruction retains
its complete base ledger plus a dispatch/root wrapper. Launch reads operands/parameter and writes
the three input registers; return reads and installs the pair. Retained list roots are shared.
The model counts primitive operations, not compiled execution, interpreter fuel or bit complexity.
-/

@[expose] public section

namespace Polynomial.QuadraticJetHornerMachine

open QuadraticAlgebra
open MvPolynomial.QuadraticEvaluationMachine (Cost delegated cost_assoc cost_zero_add
  cost_add_zero total_add)

abbrev Pair (F : Type*) := F × F

/-- Preserve the source phase's administrative fields, removing its abstract arithmetic counts. -/
def administrative (c : JetHornerMachine.Cost) : Cost :=
  ⟨{ control := c.control, data := c.data, output := c.output }, c.natural⟩
/-- Explicit coordinate-zero allocation and literal writes, beyond the source cell allocation. -/
def zeroPair : Cost := ⟨{ data := 2, constants := 2 }, 0⟩
/-- Arithmetic input-record setup: one control dispatch and six reads/writes. -/
def launch : Cost := ⟨{ control := 1, data := 6 }, 0⟩
/-- Read the emitted pair and restore the retained continuation registers. -/
def returned : Cost := ⟨{ control := 1, data := 4 }, 0⟩
/-- Allocate one updated jet cell and advance the retained old-list and carry registers. -/
def saveCost : Cost := ⟨{ control := 1, data := 5 }, 0⟩

/-- The multiply continuation retains the old head separately from its product and sum. -/
inductive Continuation (F : Type*) where
  | multiply (coefficients tail reversed : List (Pair F)) (old carry : Pair F)
  | add (coefficients tail reversed : List (Pair F)) (old : Pair F)
  deriving DecidableEq, Repr

inductive Configuration (F : Type*) where
  | ready (state : JetHornerMachine.Configuration (Pair F))
  | call (continuation : Continuation F) (input : ArithmeticMachine.Input F)
      (state : ArithmeticMachine.Configuration F)
  | save (coefficients tail reversed : List (Pair F)) (old value : Pair F)

/-- Multiplication returns into a real addition call; addition returns into explicit cell save. -/
def resume {F : Type*} (a : F) : Continuation F → Pair F → Configuration F
  | .multiply cs hs rev old carry, p =>
      .call (.add cs hs rev old) ⟨a, p, carry⟩ (.start .add)
  | .add cs hs rev old, p => .save cs hs rev old p

/-- Multiplication return also constructs the next input record and selects its program. -/
def returnCost {F : Type*} : Continuation F → Cost
  | .multiply _ _ _ _ _ => returned + launch
  | .add _ _ _ _ => returned

variable {F : Type*} [Field F] [DecidableEq F]

/-- Only individual base instructions, list accesses, allocations and control are executed. -/
def step (a : F) (x : Pair F) : Configuration F → Option (Configuration F × Cost)
  | .ready (.initialize cs (n + 1) zs) =>
      some (.ready (.initialize cs n ((0, 0) :: zs)),
        administrative JetHornerMachine.initCost + zeroPair)
  | .ready (.initialize cs 0 zs) =>
      some (.ready (.coefficients cs zs), administrative JetHornerMachine.initDoneCost)
  | .ready (.coefficients (c :: cs) js) =>
      some (.ready (.update cs js [] c), administrative JetHornerMachine.takeCost)
  | .ready (.coefficients [] js) =>
      some (.ready (.emit js js), administrative JetHornerMachine.outputStartCost)
  | .ready (.update cs (h :: hs) rev carry) =>
      some (.call (.multiply cs hs rev h carry) ⟨a, x, h⟩ (.start .mul),
        administrative JetHornerMachine.updateCost + launch)
  | .ready (.update cs [] rev _) =>
      some (.ready (.reverse cs rev []), administrative JetHornerMachine.updateDoneCost)
  | .ready (.reverse cs (h :: hs) out) =>
      some (.ready (.reverse cs hs (h :: out)), administrative JetHornerMachine.reverseCost)
  | .ready (.reverse cs [] out) =>
      some (.ready (.coefficients cs out), administrative JetHornerMachine.reverseDoneCost)
  | .ready (.emit (_ :: hs) out) =>
      some (.ready (.emit hs out), administrative JetHornerMachine.outputCost)
  | .ready (.emit [] out) =>
      some (.ready (.done out), administrative JetHornerMachine.outputDoneCost)
  | .ready (.done _) => none
  | .call k _ (.done (.pair p)) => some (resume a k p, returnCost k)
  | .call k input s => (ArithmeticMachine.step input s).map
      (fun z => (.call k input z.1, delegated z.2))
  | .save cs hs rev old value => some (.ready (.update cs hs (value :: rev) old), saveCost)

/-- Traces accumulate the actual concrete costs. -/
inductive Trace (a : F) (x : Pair F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a x 0 s 0 s
  | cons {n s u t c d} (head : step a x s = some (u, c)) (tail : Trace a x n u d t) :
      Trace a x (n + 1) s (c + d) t

/-- One actual instruction, including its emitted cost. -/
theorem single {a : F} {x : Pair F} {s t : Configuration F} {c : Cost}
    (h : step a x s = some (t, c)) : Trace a x 1 s c t := by
  simpa using (Trace.cons h (Trace.nil t))

/-- Compose real lowered traces without an extensional arithmetic callback. -/
theorem Trace.trans {a : F} {x : Pair F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace a x n s c u) (h' : Trace a x m u d t) : Trace a x (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel executes individual instructions and exposes suspended calls on exhaustion. -/
def runFuel (a : F) (x : Pair F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step a x s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a x n t; (r.1, c + r.2)

/-- Exact trace length runs to the same endpoint with the same ledger. -/
theorem Trace.runFuel_eq {a : F} {x : Pair F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a x n s c t) : runFuel a x n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

end Polynomial.QuadraticJetHornerMachine
