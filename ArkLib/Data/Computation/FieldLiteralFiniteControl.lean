/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FiniteHeadProgram
public import ArkLib.Data.Computation.FieldLiteralMachine

/-!
# Finite-head control for physical field literals

The literal controller has twenty-four finite labels and six fixed tapes. Its table includes
both zero/one entries and all suspended shape or padding child phases. Output remains tape zero,
scratch tape two, reference tape four and the padding child's spare output tape five. Every
branch inspects only current heads. Every original transition and all fuel prefixes are matched
exactly, including a zero-width one request and halted or rejected child entries.
-/

@[expose] public section

namespace Computation.FieldLiteralFiniteControl

open FiniteHeadProgram
open BinaryWordMachine (Word value)

/-- Only four tapes are active; positions one and three are always retained. -/
def actions (output saved reference spare : Action) : Fin 6 → Action :=
  ![output, .keep, saved, .keep, reference, spare]

/-- The complete literal table uses only finite phase labels and optional current bits. -/
def program : Program 24 6 where
  dispatch phase heads := match phase.val with
    | 0 => some (7, actions .keep .keep .keep .keep)
    | 1 => some (16, actions .keep .keep .keep .keep)
    | 2 => some (3, actions .keep .keep .keep .keep)
    | 3 => match heads 4, heads 0 with
        | none, none => some (4, actions .keep .keep .keep .keep)
        | some _, none => some (6, actions .keep .keep .keep .keep)
        | none, some _ => some (3, actions .pop (.push false) .keep .keep)
        | some b, some _ => some (3, actions .pop (.push b) .pop .keep)
    | 4 => match heads 2 with
        | none => some (5, actions .keep .keep .keep .keep)
        | some b => some (4, actions .keep .pop .keep (.push b))
    | 7 => some (8, actions .keep .keep .keep .keep)
    | 8 => match heads 4 with
        | none => some (9, actions .keep .keep .keep .keep)
        | some b => some (8, actions .keep (.push b) .pop .keep)
    | 9 => match heads 2 with
        | none => some (10, actions .keep .keep .keep .keep)
        | some b => some (9, actions (.push false) .pop (.push b) .keep)
    | 10 => some (22, actions .keep .keep .keep .keep)
    | 11 => some (12, actions .keep .keep .keep .keep)
    | 12 => match heads 4, heads 0 with
        | none, none => some (13, actions .keep .keep .keep .keep)
        | some _, none => some (15, actions .keep .keep .keep .keep)
        | none, some _ => some (12, actions .pop (.push false) .keep .keep)
        | some b, some _ => some (12, actions .pop (.push b) .pop .keep)
    | 13 => match heads 2 with
        | none => some (14, actions .keep .keep .keep .keep)
        | some b => some (13, actions .keep .pop .keep (.push b))
    | 16 => some (17, actions .keep .keep .keep .keep)
    | 17 => match heads 4 with
        | none => some (18, actions .keep .keep .keep .keep)
        | some b => some (17, actions .keep (.push b) .pop .keep)
    | 18 => match heads 2 with
        | none => some (19, actions .keep .keep .keep .keep)
        | some b => some (18, actions (.push false) .pop (.push b) .keep)
    | 19 => some (20, actions .keep .keep .keep .keep)
    | 20 => match heads 0 with
        | none => some (23, actions .keep .keep .keep .keep)
        | some _ => some (21, actions .pop .keep .keep .keep)
    | 21 => some (22, actions (.push true) .keep .keep .keep)
    | _ => none

/-- The two copies of the child phase graph retain the finite one/zero selector. -/
def childPhase (one : Bool) : FixedWidthWordMachine.Control → Fin 24
  | .start _ _ => if one then 11 else 2
  | .scan _ _ _ => if one then 12 else 3
  | .reverse _ _ => if one then 13 else 4
  | .done _ => if one then 14 else 5
  | .rejected _ _ => if one then 15 else 6
  | .shapeStart _ => if one then 16 else 7
  | .shapeCopy _ _ => if one then 17 else 8
  | .shapeRestore _ _ _ => if one then 18 else 9
  | .shapeDone _ _ => if one then 19 else 10

/-- The finite label contains no reference word, length, output or child tape. -/
def phase : FieldLiteralMachine.Control → Fin 24
  | .start _ one => if one then 1 else 0
  | .shaping one child => childPhase one child
  | .onePop _ _ => 20
  | .onePush _ _ => 21
  | .done _ _ => 22
  | .rejected _ _ => 23

/-- Proof-only representation preserves all six original physical positions. -/
def represent (s : FieldLiteralMachine.Control) : Configuration 24 6 :=
  ⟨phase s, FieldLiteralMachine.tapes s⟩

/-- The finite table agrees exactly with every source transition, including halted children. -/
theorem step_refines (s : FieldLiteralMachine.Control) :
    step program (represent s) = (FieldLiteralMachine.step s).map represent := by
  cases s
  case' start reference one => cases one
  case' shaping one child =>
    cases child
    case' scan word shape saved => cases word <;> cases shape
    case' reverse saved output => cases saved
    case' shapeCopy reference saved => cases reference
    case' shapeRestore saved reference shape => cases saved
    all_goals cases one
  case' onePop reference output => cases output
  all_goals first | rfl | apply congrArg some
  all_goals dsimp only [represent, phase, childPhase, FieldLiteralMachine.tapes,
    FixedWidthWordMachine.tapes]
  all_goals congr 1
  all_goals funext i
  all_goals fin_cases i <;> rfl

/-- Exact trace transport keeps the count of every bit action and handoff. -/
theorem trace_refines {n : ℕ} {s t : FieldLiteralMachine.Control}
    (h : FieldLiteralMachine.Trace n s t) : Trace program n (represent s) (represent t) := by
  induction h with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (by rw [step_refines, head]; rfl) ih

/-- Every fuel prefix commutes, including arbitrary suspended child states and early halt. -/
theorem run_refines (fuel : ℕ) (s : FieldLiteralMachine.Control) :
    runFuel program fuel (represent s) = represent (FieldLiteralMachine.runFuel fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFuel, step_refines, FieldLiteralMachine.runFuel]
      cases FieldLiteralMachine.step s with
      | none => rfl
      | some t => exact ih t

/-- Zero is physically produced at full reference width by this finite-head execution. -/
theorem zero_correct (reference : Word) :
    ∃ out : Word,
      Trace program (2 * reference.length + 5) (represent (.start reference false))
        (represent (.done reference out)) ∧
      runFuel program (2 * reference.length + 5) (represent (.start reference false)) =
        represent (.done reference out) ∧ out.length = reference.length ∧ value out = 0 := by
  obtain ⟨out, ht, hr, hl, hv⟩ := FieldLiteralMachine.zero_correct reference
  exact ⟨out, trace_refines ht, by rw [run_refines, hr], hl, hv⟩

/-- One uses the same shape execution and two actual low-bit replacement instructions. -/
theorem one_correct (reference : Word) (hq : 1 < value reference) :
    ∃ out : Word,
      Trace program (2 * reference.length + 7) (represent (.start reference true))
        (represent (.done reference out)) ∧
      runFuel program (2 * reference.length + 7) (represent (.start reference true)) =
        represent (.done reference out) ∧ out.length = reference.length ∧
          value out = 1 ∧ value out < value reference := by
  obtain ⟨out, ht, hr, hl, hv, hlt⟩ := FieldLiteralMachine.one_correct reference hq
  exact ⟨out, trace_refines ht, by rw [run_refines, hr], hl, hv, hlt⟩

/-- The zero-width one request rejects in exactly the same six finite-head transitions. -/
theorem one_empty : Trace program 6 (represent (.start [] true)) (represent (.rejected [] [])) ∧
    runFuel program 6 (represent (.start [] true)) = represent (.rejected [] []) := by
  have h := trace_refines FieldLiteralMachine.one_empty
  exact ⟨h, h.runFuel_eq⟩

end Computation.FieldLiteralFiniteControl
