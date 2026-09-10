/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine

/-!
# Explicit materialization of a quadratic alphabet's coordinate pairs

The setup program returns lists of quadratic-algebra records. This controller reads their two
scalar fields and allocates raw pairs and list cells individually, then reverses the result.
Its logical specification uses a list map; dispatch does not. The same trace counts all record,
cell and cursor operations in the field-level data-access model, not in a bit-time model.
-/

@[expose] public section

namespace QuadraticAlgebra.CoordinateAlphabetMachine

inductive Configuration (F : Type*) (a b : F) where
  | scan (remaining : List (QuadraticAlgebra F a b)) (saved : List (F × F))
  | reverse (remaining output : List (F × F))
  | done (output : List (F × F))
  deriving DecidableEq

variable {F : Type*} {a b : F}

/-- Scan charges one control step and eight record/cell accesses. Reversal charges six
primitives per cell; its final handoff charges control, output, and two root accesses. -/
def step : Configuration F a b → Option (Configuration F a b × ℕ)
  | .scan (x :: xs) saved => some (.scan xs ((x.re, x.im) :: saved), 9)
  | .scan [] saved => some (.reverse saved [], 4)
  | .reverse (x :: xs) out => some (.reverse xs (x :: out), 6)
  | .reverse [] out => some (.done out, 4)
  | .done _ => none

inductive Trace : ℕ → Configuration F a b → ℕ → Configuration F a b → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : step s = some (u, c)) (tail : Trace n u d t) :
      Trace (n + 1) s (c + d) t

def runFuel : ℕ → Configuration F a b → Configuration F a b × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel n t; (r.1, c + r.2)

/-- Surplus observation fuel preserves the completed result and its exact cost. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration F a b} {c : ℕ} {out}
    (h : Trace n s c (.done out)) (extra : ℕ) :
    runFuel (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head]
      dsimp only
      rw [ih he]

theorem reverse_trace (xs out : List (F × F)) :
    Trace (xs.length + 1) (.reverse xs out : Configuration F a b)
      (6 * xs.length + 4) (.done (xs.reverse ++ out)) := by
  induction xs generalizing out with
  | nil =>
      simpa using Trace.cons (s := .reverse [] out) (c := 4) (by rfl) (Trace.nil (.done out))
  | cons x xs ih =>
      convert Trace.cons (show step (.reverse (x :: xs) out) = _ from rfl) (ih (x :: out)) using 1
      all_goals simp [List.reverse_cons, List.append_assoc] <;> omega

/-- Proof-only coordinate representation of the supplied alphabet. -/
def coordinates (xs : List (QuadraticAlgebra F a b)) : List (F × F) :=
  xs.map (fun x ↦ (x.re, x.im))

/-- Every supplied record is processed and its input order is retained, including duplicates. -/
theorem scan_trace (xs : List (QuadraticAlgebra F a b)) (saved : List (F × F)) :
    Trace (2 * xs.length + saved.length + 2) (.scan xs saved)
      (15 * xs.length + 6 * saved.length + 8) (.done (saved.reverse ++ coordinates xs)) := by
  induction xs generalizing saved with
  | nil =>
      convert Trace.cons (show step (.scan [] saved : Configuration F a b) = _ from rfl)
        (reverse_trace (a := a) (b := b) saved []) using 1
      all_goals simp [coordinates] <;> omega
  | cons x xs ih =>
      convert Trace.cons (show step (.scan (x :: xs) saved) = _ from rfl)
        (ih ((x.re, x.im) :: saved)) using 1
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · simp [coordinates, List.reverse_cons, List.append_assoc]

/-- A supplied length bound gives an explicit execution fuel, not a runtime list-length oracle. -/
theorem evaluation_runFuel (xs : List (QuadraticAlgebra F a b)) (bound : ℕ)
    (hb : xs.length ≤ bound) :
    runFuel (2 * bound + 2) (.scan xs []) =
      (.done (coordinates xs), 15 * xs.length + 8) := by
  have ht := (scan_trace xs []).runFuel_done (2 * (bound - xs.length))
  simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.mul_zero,
    Nat.add_zero] at ht
  have hn : 2 * xs.length + 2 + 2 * (bound - xs.length) = 2 * bound + 2 := by omega
  rw [hn] at ht
  exact ht

end QuadraticAlgebra.CoordinateAlphabetMachine
