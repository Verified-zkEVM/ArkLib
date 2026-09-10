/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AlgebraicMachine.Horner
public import ArkLib.Data.Polynomial.HornerMachine
-- The polynomial refinement intentionally reduces CompPoly's array representation.
import all CompPoly.Univariate.Basic

/-!
# Algebraic-machine refinement of polynomial evaluation

The materialized coefficient list is an input. Its relation to a computational polynomial
is a precondition, not an uncharged conversion performed by the program. The same fixed
program works for every list length and field. Its output agrees with the existing Horner
reference machine; the two machines have different, separately proved cost models.
-/

@[expose] public section

namespace AlgebraicMachine.Horner

variable {F : Type*} [Field F] [DecidableEq F]

/-- The restricted machine returns the same scalar as the existing Horner reference code. -/
theorem reference_execution (xs : List F) (s : State F 8) (root : Value F) (x : F)
    (hw : s.heap.WellFormed) (hr : RepresentsList s.heap root (xs.map Value.field))
    (hc : s.registers cursor = root) (hp : s.registers point = .field x) :
    ∃ t v, Executes program s (12 * xs.length + 7) t ∧
      t.registers accumulator = .field v ∧
      Polynomial.HornerMachine.runFuel Polynomial.HornerMachine.hornerCode x
        (3 * xs.length + 3) (.running 0 xs 0 0) =
        (.halted v, Polynomial.HornerMachine.hornerCost xs.length) := by
  obtain ⟨t, he, hv, _⟩ := program_executes xs s root x hw hr hc hp
  exact ⟨t, _, he, hv, Polynomial.HornerMachine.horner_runFuel x xs⟩

/-- A represented polynomial is evaluated by a terminating trace of the fixed program.
Both the trace and the observer use the exact bound; no coefficient conversion is executed. -/
theorem polynomial_execution (p : CompPoly.CPolynomial F) (xs : List F)
    (hxs : xs = p.val.toList.reverse) (s : State F 8) (root : Value F) (x : F)
    (hw : s.heap.WellFormed) (hr : RepresentsList s.heap root (xs.map Value.field))
    (hc : s.registers cursor = root) (hp : s.registers point = .field x) :
    ∃ t, Steps (12 * xs.length + 7) ⟨s, [.execute program]⟩ ⟨t, []⟩ ∧
      AlgebraicMachine.run (12 * xs.length + 7) ⟨s, [.execute program]⟩ = some t ∧
      t.registers accumulator = .field (p.eval x) ∧
      t.heap = s.heap ∧ t.heap.WellFormed ∧ Preserves s t := by
  obtain ⟨t, he, hv, _, hh, hw', hf⟩ := program_executes xs s root x hw hr hc hp
  refine ⟨t, he.steps [], he.run, ?_, hh, hw', hf⟩
  rw [hv]
  congr 1
  rw [hxs, List.foldl_reverse]
  change p.val.toList.foldr (fun c a => a * x + c) 0 = p.eval x
  rw [Array.foldr_toList]
  exact CompPoly.CPolynomial.eval_horner_eq_eval x p

end AlgebraicMachine.Horner
