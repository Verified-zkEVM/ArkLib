/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryWordSemantics

/-!
# Literal fixed-width words and physical width markers

Padding consumes an explicit marker tape, emits one bit per marker, and physically reverses
the result. Excess input is rejected without clearing any remaining tape. A separate entry
constructs a marker tape from an existing reference word, preserving that word by copying and
restoring every bit. Neither entry decodes an integer length or performs a whole-list operation.
-/

@[expose] public section

namespace Computation.FixedWidthWordMachine

open BinaryWordMachine (Word value bitValue)

inductive Control where
  | start (word shape : Word)
  | scan (word shape saved : Word)
  | reverse (saved output : Word)
  | done (output : Word)
  | rejected (word saved : Word)
  | shapeStart (reference : Word)
  | shapeCopy (reference saved : Word)
  | shapeRestore (saved reference shape : Word)
  | shapeDone (reference shape : Word)
  deriving DecidableEq, Repr

/-- Fixed local-cell successors; the values of width-marker bits are irrelevant. -/
def step : Control → Option Control
  | .start word shape => some (.scan word shape [])
  | .scan [] [] saved => some (.reverse saved [])
  | .scan (x :: xs) [] saved => some (.rejected (x :: xs) saved)
  | .scan [] (_ :: shape) saved => some (.scan [] shape (false :: saved))
  | .scan (x :: xs) (_ :: shape) saved => some (.scan xs shape (x :: saved))
  | .reverse (x :: xs) output => some (.reverse xs (x :: output))
  | .reverse [] output => some (.done output)
  | .shapeStart reference => some (.shapeCopy reference [])
  | .shapeCopy (x :: xs) saved => some (.shapeCopy xs (x :: saved))
  | .shapeCopy [] saved => some (.shapeRestore saved [] [])
  | .shapeRestore (x :: xs) reference shape =>
      some (.shapeRestore xs (x :: reference) (false :: shape))
  | .shapeRestore [] reference shape => some (.shapeDone reference shape)
  | .done _ | .rejected _ _ | .shapeDone _ _ => none

/-- Both entries use the same four fixed physical tapes. -/
def tapes : Control → BitLocalActions.Tapes
  | .start word shape => { left := word, right := shape }
  | .scan word shape saved => { left := word, right := shape, saved := saved }
  | .reverse saved output => { saved := saved, output := output }
  | .done output => { output := output }
  | .rejected word saved => { left := word, saved := saved }
  | .shapeStart reference => { left := reference }
  | .shapeCopy reference saved => { left := reference, saved := saved }
  | .shapeRestore saved reference shape => { left := reference, right := shape, saved := saved }
  | .shapeDone reference shape => { left := reference, right := shape }

/-- Every successor performs at most one push, pop, or keep per physical tape. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.Step (tapes s) (tapes t) := by
  cases s with
  | start word shape => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
  | scan word shape saved =>
      cases word <;> cases shape <;> cases h
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.keep _, .pop _ _, .push _ _, .keep _⟩
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.pop _ _, .pop _ _, .push _ _, .keep _⟩
  | reverse saved output =>
      cases saved <;> cases h
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.keep _, .keep _, .pop _ _, .push _ _⟩
  | shapeStart reference => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
  | shapeCopy reference saved =>
      cases reference <;> cases h
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.pop _ _, .keep _, .push _ _, .keep _⟩
  | shapeRestore saved reference shape =>
      cases saved <;> cases h
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.push _ _, .push _ _, .pop _ _, .keep _⟩
  | done output => cases h
  | rejected word saved => cases h
  | shapeDone reference shape => cases h

/-- Trace length counts only actual successors of this controller. -/
inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- External fuel observes the literal local-bit program. -/
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

/-- Proof-side padded word. The successor never calls this function. -/
def padded : Word → Word → Word
  | word, [] => word
  | [], _ :: shape => false :: padded [] shape
  | x :: xs, _ :: shape => x :: padded xs shape

theorem padded_length (word shape : Word) (h : word.length ≤ shape.length) :
    (padded word shape).length = shape.length := by
  induction shape generalizing word with
  | nil => have hw : word = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
           subst word; rfl
  | cons b bs ih =>
      cases word with
      | nil => simpa [padded] using congrArg Nat.succ (ih [] (by simp))
      | cons x xs => simpa [padded] using congrArg Nat.succ (ih xs (by simpa using h))

theorem padded_value (word shape : Word) : value (padded word shape) = value word := by
  induction shape generalizing word with
  | nil => rfl
  | cons b bs ih =>
      cases word <;> simp [padded, value, bitValue, ih]

/-- The scan emits the exact supplied low bits followed by enough high zero bits. -/
theorem scan_trace (word shape saved : Word) (h : word.length ≤ shape.length) :
    Trace (shape.length + 1) (.scan word shape saved)
      (.reverse ((padded word shape).reverse ++ saved) []) := by
  induction shape generalizing word saved with
  | nil =>
      have hw : word = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
      subst word
      exact .cons rfl (.nil _)
  | cons b bs ih =>
      cases word with
      | nil =>
          simpa [padded, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
            Trace.cons (by rfl) (ih [] (false :: saved) (by simp))
      | cons x xs =>
          simpa [padded, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
            Trace.cons (by rfl) (ih xs (x :: saved) (by simpa using h))

/-- The reversed temporary is transferred into its physical output one bit per step. -/
theorem reverse_trace (saved output : Word) :
    Trace (saved.length + 1) (.reverse saved output) (.done (saved.reverse ++ output)) := by
  induction saved generalizing output with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: output))

/-- Padding has exact input-width-only cost and preserves the represented numeric value. -/
theorem pad_correct (word shape : Word) (h : word.length ≤ shape.length) :
    ∃ out : Word,
      Trace (2 * shape.length + 3) (.start word shape) (.done out) ∧
      runFuel (2 * shape.length + 3) (.start word shape) = .done out ∧
      out.length = shape.length ∧ value out = value word := by
  have hs := scan_trace word shape [] h
  have hr := reverse_trace (padded word shape).reverse []
  simp only [List.append_nil] at hs
  simp only [List.reverse_reverse, List.append_nil] at hr
  have ht := Trace.cons (s := .start word shape) (by rfl) (hs.append hr)
  have hlen := padded_length word shape h
  have he : Trace (2 * shape.length + 3) (.start word shape) (.done (padded word shape)) := by
    convert ht using 1
    simp only [List.length_reverse, hlen]
    omega
  exact ⟨_, he, he.runFuel_eq, hlen, padded_value word shape⟩

/-- The reference is copied into a saved tape, preserving every original bit. -/
theorem shapeCopy_trace (reference saved : Word) :
    Trace (reference.length + 1) (.shapeCopy reference saved)
      (.shapeRestore (reference.reverse ++ saved) [] []) := by
  induction reference generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: saved))

/-- Restoring the reference simultaneously pushes one explicit marker per restored bit. -/
theorem shapeRestore_trace (saved reference shape : Word) :
    Trace (saved.length + 1) (.shapeRestore saved reference shape)
      (.shapeDone (saved.reverse ++ reference) (List.replicate saved.length false ++ shape)) := by
  induction saved generalizing reference shape with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.replicate_add, List.replicate_one] using
        Trace.cons (by rfl) (ih (x :: reference) (false :: shape))

/-- Constructing a physical width tape retains the exact reference and has linear literal cost. -/
theorem shape_correct (reference : Word) :
    Trace (2 * reference.length + 3) (.shapeStart reference)
        (.shapeDone reference (List.replicate reference.length false)) ∧
      runFuel (2 * reference.length + 3) (.shapeStart reference) =
        .shapeDone reference (List.replicate reference.length false) := by
  have hc := shapeCopy_trace reference []
  have hr := shapeRestore_trace reference.reverse [] []
  simp only [List.append_nil] at hc
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at hr
  have ht := Trace.cons (s := .shapeStart reference) (by rfl) (hc.append hr)
  have he : Trace (2 * reference.length + 3) (.shapeStart reference)
      (.shapeDone reference (List.replicate reference.length false)) := by
    convert ht using 1
    omega
  exact ⟨he, he.runFuel_eq⟩

end Computation.FixedWidthWordMachine
