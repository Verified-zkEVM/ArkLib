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
# Retained bit-word copying with physical destination clearing

Three fixed tapes hold source, scratch, and destination. The destination is cleared one bit at
a time, then two passes restore the source and produce an identical destination. No whole-word
assignment executes. The count includes the old destination's length, so overwriting a register
cannot hide its cleanup. Source and destination are distinct physical tape positions.
-/

@[expose] public section

namespace Computation.WordCopyMachine

abbrev Word := List Bool

inductive Control where
  | clear (source destination : Word)
  | save (source scratch : Word)
  | restore (scratch source destination : Word)
  | done (source destination : Word)
  deriving DecidableEq, Repr

/-- Each transition inspects a head or emptiness and updates at most one bit on each tape. -/
def step : Control → Option Control
  | .clear source (_ :: rest) => some (.clear source rest)
  | .clear source [] => some (.save source [])
  | .save (b :: rest) scratch => some (.save rest (b :: scratch))
  | .save [] scratch => some (.restore scratch [] [])
  | .restore (b :: rest) source destination =>
      some (.restore rest (b :: source) (b :: destination))
  | .restore [] source destination => some (.done source destination)
  | .done _ _ => none

/-- Source zero, scratch one, destination two remain fixed across all phases. -/
def tapes : Control → Fin 3 → Word
  | .clear source destination => ![source, [], destination]
  | .save source scratch => ![source, scratch, []]
  | .restore scratch source destination => ![source, scratch, destination]
  | .done source destination => ![source, [], destination]

private theorem bank_three {a b c a' b' c' : Word}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') :
    BitLocalActions.BankStep ![a, b, c] ![a', b', c'] := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- Even suspended or malformed phase entries obey the literal three-tape bit-local rule. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  cases s with
  | clear source destination =>
      cases destination <;> cases h <;> apply bank_three <;> constructor
  | save source scratch =>
      cases source <;> cases h <;> apply bank_three <;> constructor
  | restore scratch source destination =>
      cases scratch <;> cases h <;> apply bank_three <;> constructor
  | done _ _ => cases h

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

theorem clear_trace (source destination : Word) :
    Trace (destination.length + 1) (.clear source destination) (.save source []) := by
  induction destination with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih => exact .cons rfl ih

theorem save_trace (source scratch : Word) :
    Trace (source.length + 1) (.save source scratch)
      (.restore (source.reverse ++ scratch) [] []) := by
  induction source generalizing scratch with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc] using Trace.cons (by rfl) (ih (b :: scratch))

theorem restore_trace (scratch source destination : Word) :
    Trace (scratch.length + 1) (.restore scratch source destination)
      (.done (scratch.reverse ++ source) (scratch.reverse ++ destination)) := by
  induction scratch generalizing source destination with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc] using
        Trace.cons (by rfl) (ih (b :: source) (b :: destination))

/-- Exact copying cost, including destruction of the previous destination and all handoffs. -/
theorem copy_correct (source destination : Word) :
    Trace (destination.length + 2 * source.length + 3) (.clear source destination)
      (.done source source) ∧
    runFuel (destination.length + 2 * source.length + 3) (.clear source destination) =
      .done source source := by
  have hc := clear_trace source destination
  have hs := save_trace source []
  have hr := restore_trace source.reverse [] []
  simp only [List.append_nil] at hs
  simp only [List.reverse_reverse, List.append_nil] at hr
  have ht : Trace (destination.length + 2 * source.length + 3)
      (.clear source destination) (.done source source) := by
    convert (hc.append hs).append hr using 1
    simp only [List.length_reverse]
    omega
  exact ⟨ht, ht.runFuel_eq⟩

end Computation.WordCopyMachine
