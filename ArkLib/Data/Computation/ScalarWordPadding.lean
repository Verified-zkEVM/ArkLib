/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FixedWidthWordMachine
public import ArkLib.Data.Computation.BinaryWordBounds
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Physical scalar padding with its own width-tape construction

A retained reference word supplies the target width. The first child constructs that width's
marker tape by a literal copy/restore. One tape-preserving handoff starts the padding child,
which consumes the operand and markers and produces the fixed-width output. The six tapes are
fixed throughout; neither the width tape nor an input copy is provided by an uncharged oracle.

The initial reference and operand are already materialized. Numeric interpretation and the
input-width comparison are proof-side contracts, not runtime instructions. The RAM lift retains
the same memory. The exact count describes this stated bit machine, not native Lean execution.
-/

@[expose] public section

namespace Computation.ScalarWordPadding

open BinaryWordMachine (Word value)

/-- The operand stays on its physical input tape while the reference is restored. -/
inductive Control where
  | shaping (word : Word) (child : FixedWidthWordMachine.Control)
  | padding (reference : Word) (child : FixedWidthWordMachine.Control)
  deriving DecidableEq, Repr

/-- Literal children and one finite-control, tape-preserving handoff. -/
def step : Control → Option Control
  | .shaping word child =>
      match FixedWidthWordMachine.step child with
      | some next => some (.shaping word next)
      | none => match child with
          | .shapeDone reference shape => some (.padding reference (.start word shape))
          | _ => none
  | .padding reference child =>
      (FixedWidthWordMachine.step child).map (.padding reference)

/-- Fixed slots: reference 0, shape 1, saved 2, operand 3, output 4, spare output 5. -/
def tapes : Control → Fin 6 → Word
  | .shaping word child =>
      let t := FixedWidthWordMachine.tapes child
      ![t.left, t.right, t.saved, word, [], t.output]
  | .padding reference child =>
      let t := FixedWidthWordMachine.tapes child
      ![reference, t.right, t.saved, t.left, t.output, []]

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

/-- Every combined successor satisfies the same shared local-cell bank semantics. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  cases s with
  | shaping word child =>
      cases hs : FixedWidthWordMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := FixedWidthWordMachine.step_local hs
          exact bank_six hl.1 hl.2.1 hl.2.2.1 (.keep _) (.keep _) hl.2.2.2
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          exact bank_six (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
  | padding reference child =>
      obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
      cases ht
      have hl := FixedWidthWordMachine.step_local hs
      exact bank_six (.keep _) hl.2.1 hl.2.2.1 hl.1 hl.2.2.2 (.keep _)

/-- Counts of actual complete fixed-bank instructions. -/
inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- Fuel is an external observer of this same controller. -/
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

/-- The operand is retained while the actual reference-copying child executes. -/
theorem lift_shape (word : Word) {n : ℕ} {s t : FixedWidthWordMachine.Control}
    (h : FixedWidthWordMachine.Trace n s t) : Trace n (.shaping word s) (.shaping word t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- The reference is retained while the actual padding child executes. -/
theorem lift_padding (reference : Word) {n : ℕ} {s t : FixedWidthWordMachine.Control}
    (h : FixedWidthWordMachine.Trace n s t) :
    Trace n (.padding reference s) (.padding reference t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head, Option.map_some]) ih

/-- The exact run includes width-tape construction, the actual handoff, and physical padding. -/
theorem padding_correct (reference word : Word) (hw : word.length ≤ reference.length) :
    ∃ out : Word,
      Trace (4 * reference.length + 7) (.shaping word (.shapeStart reference))
        (.padding reference (.done out)) ∧
      runFuel (4 * reference.length + 7) (.shaping word (.shapeStart reference)) =
        .padding reference (.done out) ∧
      out.length = reference.length ∧ value out = value word := by
  have hs := lift_shape word (FixedWidthWordMachine.shape_correct reference).1
  obtain ⟨out, hp, _hr, hlen, hv⟩ := FixedWidthWordMachine.pad_correct word
    (List.replicate reference.length false) (by simpa using hw)
  have hh : Trace 1
      (.shaping word (.shapeDone reference (List.replicate reference.length false)))
      (.padding reference (.start word (List.replicate reference.length false))) :=
    .cons rfl (.nil _)
  have he : Trace (4 * reference.length + 7) (.shaping word (.shapeStart reference))
      (.padding reference (.done out)) := by
    convert (hs.append hh).append (lift_padding reference hp) using 1
    simp only [List.length_replicate]
    omega
  exact ⟨out, he, he.runFuel_eq, by simpa using hlen, hv⟩

/-- The same physical program runs in RAM without changing any memory bit. -/
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

/-- The same bounded RAM execution retains the reference and returns a value-preserving word. -/
theorem padding_ramRunFuel (mem : AddressedBits.Memory) (reference word : Word)
    (hw : word.length ≤ reference.length) :
    ∃ out : Word,
      ramRunFuel (4 * reference.length + 7) (mem, .shaping word (.shapeStart reference)) =
        (mem, .padding reference (.done out)) ∧
      out.length = reference.length ∧ value out = value word := by
  obtain ⟨out, _ht, hr, hlen, hv⟩ := padding_correct reference word hw
  exact ⟨out, by rw [ramRunFuel_eq, hr], hlen, hv⟩

/-- A canonical reduced scalar fits its modulus word; the same physical execution pads it
without changing its value or the retained modulus. -/
theorem padding_reduced (modulus word : Word) (hc : BinaryWordMachine.Canonical word)
    (hv : value word < value modulus) :
    ∃ out : Word,
      Trace (4 * modulus.length + 7) (.shaping word (.shapeStart modulus))
        (.padding modulus (.done out)) ∧
      runFuel (4 * modulus.length + 7) (.shaping word (.shapeStart modulus)) =
        .padding modulus (.done out) ∧
      out.length = modulus.length ∧ value out = value word ∧ value out < value modulus := by
  obtain ⟨out, ht, hr, hlen, he⟩ := padding_correct modulus word
    (hc.width_le_of_value_lt word modulus hv)
  exact ⟨out, ht, hr, hlen, he, he ▸ hv⟩

end Computation.ScalarWordPadding
