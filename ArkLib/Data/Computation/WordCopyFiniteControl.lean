/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FiniteHeadProgram
public import ArkLib.Data.Computation.WordCopyMachine

/-!
# Literal finite-head implementation of retained word copying

Four finite control labels select clearing, saving, restoration and halt. Only the destination,
source or scratch head is inspected in its respective phase. The three physical tapes remain
source zero, scratch one and destination two. Every original word-copy transition, including
arbitrary suspended entries and halt, is exactly one step of this finite-head program.
-/

@[expose] public section

namespace Computation.WordCopyFiniteControl

open FiniteHeadProgram

/-- The complete finite table: no branch receives or computes with a whole word. -/
def program : Program 4 3 where
  dispatch phase heads := match phase.val with
    | 0 => match heads 2 with
        | none => some (1, ![.keep, .keep, .keep])
        | some _ => some (0, ![.keep, .keep, .pop])
    | 1 => match heads 0 with
        | none => some (2, ![.keep, .keep, .keep])
        | some b => some (1, ![.pop, .push b, .keep])
    | 2 => match heads 1 with
        | none => some (3, ![.keep, .keep, .keep])
        | some b => some (2, ![.push b, .pop, .push b])
    | _ => none

/-- The finite label stores only the original phase, never an unbounded word. -/
def phase : WordCopyMachine.Control → Fin 4
  | .clear _ _ => 0
  | .save _ _ => 1
  | .restore _ _ _ => 2
  | .done _ _ => 3

/-- Proof-side representation preserves all three fixed tape positions. -/
def represent (s : WordCopyMachine.Control) : Configuration 4 3 :=
  ⟨phase s, WordCopyMachine.tapes s⟩

/-- Every literal source successor, and its halted case, matches the actual finite-head table. -/
theorem step_refines (s : WordCopyMachine.Control) :
    step program (represent s) = (WordCopyMachine.step s).map represent := by
  cases s with
  | clear source destination => cases destination <;> all_goals
      apply congrArg some
      dsimp only [represent, phase, WordCopyMachine.tapes]
      congr 1
      funext i
      fin_cases i <;> rfl
  | save source scratch => cases source <;> all_goals
      apply congrArg some
      dsimp only [represent, phase, WordCopyMachine.tapes]
      congr 1
      funext i
      fin_cases i <;> rfl
  | restore scratch source destination => cases scratch <;> all_goals
      apply congrArg some
      dsimp only [represent, phase, WordCopyMachine.tapes]
      congr 1
      funext i
      fin_cases i <;> rfl
  | done source destination => rfl

/-- Exact trace transport preserves every instruction, not merely tape locality. -/
theorem trace_refines {n : ℕ} {s t : WordCopyMachine.Control}
    (h : WordCopyMachine.Trace n s t) : Trace program n (represent s) (represent t) := by
  induction h with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (by rw [step_refines, head]; rfl) ih

/-- All fuel prefixes, including early halt and malformed phase entries, commute exactly. -/
theorem run_refines (fuel : ℕ) (s : WordCopyMachine.Control) :
    runFuel program fuel (represent s) = represent (WordCopyMachine.runFuel fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFuel, step_refines, WordCopyMachine.runFuel]
      cases WordCopyMachine.step s with
      | none => rfl
      | some t => exact ih t

/-- Clearing the old destination, preserving the source and copying all bits use the same count. -/
theorem copy_correct (source destination : List Bool) :
    Trace program (destination.length + 2 * source.length + 3)
      (represent (.clear source destination)) (represent (.done source source)) ∧
    runFuel program (destination.length + 2 * source.length + 3)
      (represent (.clear source destination)) = represent (.done source source) := by
  have h := WordCopyMachine.copy_correct source destination
  exact ⟨trace_refines h.1, by rw [run_refines, h.2]⟩

end Computation.WordCopyFiniteControl
