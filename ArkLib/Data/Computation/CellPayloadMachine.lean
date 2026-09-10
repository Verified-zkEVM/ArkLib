/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BitLocalActions
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Literal cell payload materialization

Five fixed local bit tapes hold the head word, its saved copy, the tail pointer, its saved copy,
and the output. Copy/restore phases preserve both supplied words while pushing their bits onto
the output in the required order. A final bit push adds the live-cell tag. No successor performs
a whole-word concatenation, reversal, or copy; these operations occur only in the specification.

The input words are already materialized. Their interpretation as scalar values or fixed-width
address prefixes is outside this controller. The exact local transition count does not include
pointer selection, heap writes, a handoff to another controller, or native Lean evaluation.
-/

@[expose] public section

namespace Computation.CellPayloadMachine

/-- Finite phase control and five physical bit tapes, with no integer-valued state registers. -/
inductive Control where
  | copyTail (head source saved output : List Bool)
  | restoreTail (head source tail output : List Bool)
  | copyHead (source saved tail output : List Bool)
  | restoreHead (source head tail output : List Bool)
  | tag (head tail output : List Bool)
  | done (head tail payload : List Bool)
  deriving DecidableEq, Repr

/-- Each successor inspects or moves only the current bits of fixed local tapes. -/
def step : Control → Option Control
  | .copyTail head (b :: bs) saved output => some (.copyTail head bs (b :: saved) output)
  | .copyTail head [] saved output => some (.restoreTail head saved [] output)
  | .restoreTail head (b :: bs) tail output =>
      some (.restoreTail head bs (b :: tail) (b :: output))
  | .restoreTail head [] tail output => some (.copyHead head [] tail output)
  | .copyHead (b :: bs) saved tail output => some (.copyHead bs (b :: saved) tail output)
  | .copyHead [] saved tail output => some (.restoreHead saved [] tail output)
  | .restoreHead (b :: bs) head tail output =>
      some (.restoreHead bs (b :: head) tail (b :: output))
  | .restoreHead [] head tail output => some (.tag head tail output)
  | .tag head tail output => some (.done head tail (true :: output))
  | .done _ _ _ => none

/-- Exact counts of actual local bit transitions. -/
inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- Fuel is an external trace observer, not an integer register in this bit controller. -/
def runFuel : ℕ → Control → Control
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

/-- Composition retains the intermediate physical control and counts every successor. -/
theorem Trace.append {n m : ℕ} {s u t : Control} (h : Trace n s u) (h' : Trace m u t) :
    Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Exact fuel reaches the same final physical tapes as the literal trace. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Control} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- Restore the head while prepending each restored bit onto the actual output tape. -/
theorem restoreHead_trace (source head tail output : List Bool) :
    Trace (source.length + 1) (.restoreHead source head tail output)
      (.tag (source.reverse ++ head) tail (source.reverse ++ output)) := by
  induction source generalizing head output with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b :: head) (b :: output))

/-- Save the head bit by bit before restoring it into both retained and output tapes. -/
theorem copyHead_trace (source saved tail output : List Bool) :
    Trace (source.length + 1) (.copyHead source saved tail output)
      (.restoreHead (source.reverse ++ saved) [] tail output) := by
  induction source generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b :: saved))

/-- Restore the tail pointer while materializing its bits on the output tape. -/
theorem restoreTail_trace (head source tail output : List Bool) :
    Trace (source.length + 1) (.restoreTail head source tail output)
      (.copyHead head [] (source.reverse ++ tail) (source.reverse ++ output)) := by
  induction source generalizing tail output with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b :: tail) (b :: output))

/-- Save the supplied pointer bits without decoding or re-encoding them. -/
theorem copyTail_trace (head source saved output : List Bool) :
    Trace (source.length + 1) (.copyTail head source saved output)
      (.restoreTail head (source.reverse ++ saved) [] output) := by
  induction source generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b :: saved))

/-- Materialize the tag/head/tail payload, preserving both original supplied words. -/
theorem materialize_trace (head tail : List Bool) :
    Trace (2 * head.length + 2 * tail.length + 5) (.copyTail head tail [] [])
      (.done head tail (true :: (head ++ tail))) := by
  have hc := copyTail_trace head tail [] []
  have hr := restoreTail_trace head tail.reverse [] []
  have hc' := copyHead_trace head [] tail tail
  have hr' := restoreHead_trace head.reverse [] tail tail
  simp only [List.append_nil] at hc hc'
  simp only [List.reverse_reverse, List.append_nil] at hr hr'
  have ht : Trace 1 (.tag head tail (head ++ tail)) (.done head tail (true :: (head ++ tail))) :=
    .cons rfl (.nil _)
  have h := (((hc.append hr).append hc').append hr').append ht
  convert h using 1
  simp only [List.length_reverse]
  omega

/-- The bounded observer produces exactly the physically materialized payload and retained words. -/
theorem materialize_runFuel (head tail : List Bool) :
    runFuel (2 * head.length + 2 * tail.length + 5) (.copyTail head tail [] []) =
      .done head tail (true :: (head ++ tail)) := (materialize_trace head tail).runFuel_eq

/-- Five fixed tapes retain their physical assignments through every control phase. -/
def physicalTapes : Control → Fin 5 → List Bool
  | .copyTail head source saved output => ![head, [], source, saved, output]
  | .restoreTail head source tail output => ![head, [], tail, source, output]
  | .copyHead source saved tail output => ![source, saved, tail, [], output]
  | .restoreHead source head tail output => ![head, source, tail, [], output]
  | .tag head tail output | .done head tail output => ![head, [], tail, [], output]

private theorem bank_five {a b c d e a' b' c' d' e' : List Bool}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') :
    BitLocalActions.BankStep ![a, b, c, d, e] ![a', b', c', d', e'] := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he

/-- Every literal successor performs at most one pop/push/keep action per fixed bit tape. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (physicalTapes s) (physicalTapes t) := by
  cases s with
  | copyTail head source saved output =>
      cases source <;> cases h <;> apply bank_five <;> constructor
  | restoreTail head source tail output =>
      cases source <;> cases h <;> apply bank_five <;> constructor
  | copyHead source saved tail output =>
      cases source <;> cases h <;> apply bank_five <;> constructor
  | restoreHead source head tail output =>
      cases source <;> cases h <;> apply bank_five <;> constructor
  | tag head tail output => cases h; apply bank_five <;> constructor
  | done head tail payload => cases h

end Computation.CellPayloadMachine
