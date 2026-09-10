/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.QuadraticInputMachine
public import ArkLib.Data.MvPolynomial.CoordinateNormalizeRefinement
/-!
# Literal pair input preparation

Each base-field coefficient allocates its actual zero imaginary coordinate, coefficient pair,
term and outer cell. Factor tails are shared. Reversal retains input order and duplicates.
The executable state contains only base-field values and pairs, never quadratic-algebra values.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticPreparedInputMachine

abbrev Cost := QuadraticAlgebra.ArithmeticMachine.Cost
abbrev Term := MvPolynomial.EvaluationMachine.Term
abbrev charge := MvPolynomial.QuadraticInputMachine.charge

inductive Configuration (F : Type*) where
  | scan (remaining : List (Term F)) (saved : List (Term (F × F)))
  | reverse (remaining output : List (Term (F × F)))
  | emit (output : List (Term (F × F)))
  | done (output : List (Term (F × F)))

variable {F : Type*} [Zero F]

/-- One bounded allocation or list edge per instruction; no whole-list map is executed. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .scan ((c, fs) :: ts) out => some (.scan ts (((c, 0), fs) :: out), charge 10 1 0)
  | .scan [] out => some (.reverse out [], charge 3 0 0)
  | .reverse (t :: ts) out => some (.reverse ts (t :: out), charge 5 0 0)
  | .reverse [] out => some (.emit out, charge 2 0 0)
  | .emit out => some (.done out, charge 2 0 1)
  | .done _ => none

inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : step s = some (u, c))
      (tail : Trace n u d t) : Trace (n + 1) s (c + d) t

/-- Interpret literal conversion instructions, retaining partial states. -/
def runFuel : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel n t; (r.1, c + r.2)

theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration F} {c : Cost} (h : Trace n s c t) :
    runFuel n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

/-- Logical representation of already materialized extension coefficients. -/
def represent {a : F} : MvPolynomial.QuadraticInputMachine.Configuration F a → Configuration F
  | .scan ts out => .scan ts (MvPolynomial.QuadraticNormalizeMachine.mapTerms
      MvPolynomial.QuadraticEvaluationMachine.encode out)
  | .reverse ts out => .reverse
      (MvPolynomial.QuadraticNormalizeMachine.mapTerms
        MvPolynomial.QuadraticEvaluationMachine.encode ts)
      (MvPolynomial.QuadraticNormalizeMachine.mapTerms
        MvPolynomial.QuadraticEvaluationMachine.encode out)
  | .emit out => .emit (MvPolynomial.QuadraticNormalizeMachine.mapTerms
      MvPolynomial.QuadraticEvaluationMachine.encode out)
  | .done out => .done (MvPolynomial.QuadraticNormalizeMachine.mapTerms
      MvPolynomial.QuadraticEvaluationMachine.encode out)

/-- Exact same instruction and ledger as the independently specified coefficient allocator. -/
theorem step_lowering {a : F} {s t : MvPolynomial.QuadraticInputMachine.Configuration F a}
    {c : Cost} (h : MvPolynomial.QuadraticInputMachine.Step s c t) :
    step (represent s) = some (represent t, c) := by
  cases h <;> rfl

/-- Preserve the same number of instructions, with no conversion overhead hidden in a map. -/
theorem trace_lowering {a : F} {n : ℕ}
    {s t : MvPolynomial.QuadraticInputMachine.Configuration F a} {c : Cost}
    (h : MvPolynomial.QuadraticInputMachine.Trace n s c t) :
    Trace n (represent s) c (represent t) := by
  induction h with
  | nil s => exact .nil _
  | cons head tail ih => exact .cons (step_lowering head) ih

/-- Raw base coefficients execute to their ordered literal pairs with exact linear work. -/
theorem execution_correct (a : F) (ts : List (Term F)) :
    ∃ c, runFuel (2 * ts.length + 3) (.scan ts []) =
      (.done (ts.map (fun t ↦ ((t.1, 0), t.2))), c) ∧ c.total = 18 * ts.length + 11 := by
  obtain ⟨c, ht, hc⟩ := MvPolynomial.QuadraticInputMachine.scan_trace
    ts ([] : List (Term (QuadraticAlgebra F a 0)))
  have h := (trace_lowering ht).runFuel_eq
  refine ⟨c, ?_, by simpa using hc⟩
  simpa [represent, MvPolynomial.QuadraticInputMachine.embedded,
    MvPolynomial.QuadraticNormalizeMachine.mapTerms, MvPolynomial.QuadraticNormalizeMachine.mapTerm,
    List.map_map, Function.comp_def, MvPolynomial.QuadraticEvaluationMachine.encode] using h

end ReedSolomon.ListDecoding.QuadraticPreparedInputMachine
