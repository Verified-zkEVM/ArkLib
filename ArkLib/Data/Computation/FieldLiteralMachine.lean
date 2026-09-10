/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FixedWidthWordMachine
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Physically materialized scalar zero and one

The literal shape child copies and restores the modulus reference while producing one zero bit
per reference bit. The one entry then pops the low zero and pushes a true bit in two charged
transitions. A zero-width one request rejects. No arbitrary-length literal is an instruction.
The six physical tapes keep output at zero and reference at four through every handoff.
-/

@[expose] public section

namespace Computation.FieldLiteralMachine

open BinaryWordMachine (Word value)

inductive Control where
  | start (reference : Word) (one : Bool)
  | shaping (one : Bool) (child : FixedWidthWordMachine.Control)
  | onePop (reference output : Word)
  | onePush (reference output : Word)
  | done (reference output : Word)
  | rejected (reference output : Word)
  deriving DecidableEq, Repr

def step : Control → Option Control
  | .start reference one => some (.shaping one (.shapeStart reference))
  | .shaping one child =>
      match FixedWidthWordMachine.step child with
      | some next => some (.shaping one next)
      | none => match child with
          | .shapeDone reference output =>
              some (if one then .onePop reference output else .done reference output)
          | _ => none
  | .onePop reference [] => some (.rejected reference [])
  | .onePop reference (_ :: rest) => some (.onePush reference rest)
  | .onePush reference output => some (.done reference (true :: output))
  | .done _ _ | .rejected _ _ => none

/-- Shape left maps to reference four, right to output zero, saved to two, spare output to five. -/
def tapes : Control → Fin 6 → Word
  | .start reference _ => ![[], [], [], [], reference, []]
  | .shaping _ child =>
      let t := FixedWidthWordMachine.tapes child
      ![t.right, [], t.saved, [], t.left, t.output]
  | .onePop reference output | .onePush reference output | .done reference output |
      .rejected reference output => ![output, [], [], [], reference, []]

theorem start_handoff (reference : Word) (one : Bool) :
    tapes (.start reference one) = tapes (.shaping one (.shapeStart reference)) := rfl

theorem shape_handoff (reference output : Word) (one : Bool) :
    tapes (.shaping one (.shapeDone reference output)) =
      tapes (if one then .onePop reference output else .done reference output) := by
  cases one <;> rfl

private theorem bank_six {a b c d e f a' b' c' d' e' f' : Word}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f') :
    BitLocalActions.BankStep ![a, b, c, d, e, f] ![a', b', c', d', e', f'] := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf

theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  cases s with
  | start reference one => cases h; apply bank_six <;> constructor
  | shaping one child =>
      cases hs : FixedWidthWordMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := FixedWidthWordMachine.step_local hs
          exact bank_six hl.2.1 (.keep _) hl.2.2.1 (.keep _) hl.1 hl.2.2.2
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child <;> try cases h
          rw [shape_handoff]
          intro i
          exact .keep _
  | onePop reference output =>
      cases output <;> cases h <;> apply bank_six <;> constructor
  | onePush reference output => cases h; apply bank_six <;> constructor
  | done _ _ | rejected _ _ => cases h

inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

def runFuel : ℕ → Control → Control
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem Trace.append {n m : ℕ} {s u t : Control}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_eq {n : ℕ} {s t : Control} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

theorem lift_shape (one : Bool) {n : ℕ} {s t : FixedWidthWordMachine.Control}
    (h : FixedWidthWordMachine.Trace n s t) : Trace n (.shaping one s) (.shaping one t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Shape construction plus both control handoffs materializes a full-width zero word. -/
theorem zero_trace (reference : Word) :
    Trace (2 * reference.length + 5) (.start reference false)
      (.done reference (List.replicate reference.length false)) := by
  have hs := lift_shape false (FixedWidthWordMachine.shape_correct reference).1
  have hi : Trace 1 (.start reference false) (.shaping false (.shapeStart reference)) :=
    .cons rfl (.nil _)
  have ho : Trace 1 (.shaping false
      (.shapeDone reference (List.replicate reference.length false)))
      (.done reference (List.replicate reference.length false)) := .cons rfl (.nil _)
  convert (hi.append hs).append ho using 1
  omega

theorem zero_value (n : ℕ) : value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, BinaryWordMachine.bitValue, ih]

/-- This one word is both physically produced at the stated count and numerically zero. -/
theorem zero_correct (reference : Word) :
    ∃ out : Word,
      Trace (2 * reference.length + 5) (.start reference false) (.done reference out) ∧
      runFuel (2 * reference.length + 5) (.start reference false) = .done reference out ∧
      out.length = reference.length ∧ value out = 0 := by
  refine ⟨_, zero_trace reference, (zero_trace reference).runFuel_eq, by simp, ?_⟩
  exact zero_value _

/-- One uses the same physical width construction, then a charged low-bit replacement. -/
theorem one_trace (b : Bool) (reference : Word) :
    Trace (2 * (b :: reference).length + 7) (.start (b :: reference) true)
      (.done (b :: reference) (true :: List.replicate reference.length false)) := by
  have hs := lift_shape true (FixedWidthWordMachine.shape_correct (b :: reference)).1
  have hi : Trace 1 (.start (b :: reference) true)
      (.shaping true (.shapeStart (b :: reference))) := .cons rfl (.nil _)
  have ho : Trace 3 (.shaping true
      (.shapeDone (b :: reference) (List.replicate (b :: reference).length false)))
      (.done (b :: reference) (true :: List.replicate reference.length false)) :=
    .cons rfl (.cons rfl (.cons rfl (.nil _)))
  convert (hi.append hs).append ho using 1
  omega

/-- Width zero cannot hold one; the failure is explicit and retains the empty tapes. -/
theorem one_empty : Trace 6 (.start [] true) (.rejected [] []) :=
  .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))

/-- Full-width scalar one is a valid reduced representation when the modulus exceeds one. -/
theorem one_correct (reference : Word) (hq : 1 < value reference) :
    ∃ out : Word,
      Trace (2 * reference.length + 7) (.start reference true) (.done reference out) ∧
      runFuel (2 * reference.length + 7) (.start reference true) = .done reference out ∧
      out.length = reference.length ∧ value out = 1 ∧ value out < value reference := by
  cases reference with
  | nil => simp [value] at hq
  | cons b bs =>
      have hz := zero_value bs.length
      have hv : value (true :: List.replicate bs.length false) = 1 := by
        simp [value, BinaryWordMachine.bitValue, hz]
      exact ⟨_, one_trace b bs, (one_trace b bs).runFuel_eq, by simp, hv, by simpa [hv]⟩

/-- The scalar instruction's RAM component is retained literally. -/
def ramStep (s : AddressedBits.Memory × Control) : Option (AddressedBits.Memory × Control) :=
  (step s.2).map fun t ↦ (s.1, t)

def ramRunFuel : ℕ → AddressedBits.Memory × Control → AddressedBits.Memory × Control
  | 0, s => s
  | n + 1, s => match ramStep s with
      | none => s
      | some t => ramRunFuel n t

theorem ramRunFuel_eq (mem : AddressedBits.Memory) (n : ℕ) (s : Control) :
    ramRunFuel n (mem, s) = (mem, runFuel n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => cases hs : step s <;> simp [ramRunFuel, ramStep, runFuel, hs, ih]

end Computation.FieldLiteralMachine
