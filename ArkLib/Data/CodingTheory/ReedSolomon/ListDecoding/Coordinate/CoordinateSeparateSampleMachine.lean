/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinatePreparedMachine
/-!
# Coordinate decoding with separate recovery and guard grids

Only collection reads the guard grid. Root recovery retains the supplied residual samples.
Both modes execute the same coordinate children and retain every nested charge.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticSeparateSampleDecoder

open QuadraticPreparedDecoderMachine (Input Configuration)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Override only collection's sample register, with no runtime map or grid reconstruction. -/
def step (a : F) (input : Input F) (guards : List (F × F)) :
    Configuration F → Option (Configuration F × ℕ)
  | s@(.collect _) => QuadraticPreparedDecoderMachine.step a { input with samples := guards } s
  | s => QuadraticPreparedDecoderMachine.step a input s

/-- Identical grids retain the original coordinate instruction and full charge. -/
theorem step_same (a : F) (input : Input F) (s : Configuration F) :
    step a input input.samples s = QuadraticPreparedDecoderMachine.step a input s := by
  cases s <;> rfl

/-- Actual successor equations and full accumulated scalar primitive totals. -/
inductive Trace (a : F) (input : Input F) (guards : List (F × F)) :
    ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace a input guards 0 s 0 s
  | cons {n s u t c d} (head : step a input guards s = some (u, c))
      (tail : Trace a input guards n u d t) : Trace a input guards (n + 1) s (c + d) t

theorem single {a : F} {input : Input F} {guards : List (F × F)} {s t : Configuration F} {c : ℕ}
    (h : step a input guards s = some (t, c)) : Trace a input guards 1 s c t := by
  simpa using Trace.cons h (Trace.nil t)

theorem Trace.trans {a : F} {input : Input F} {guards : List (F × F)}
    {n m : ℕ} {s u t : Configuration F} {c d : ℕ}
    (h : Trace a input guards n s c u) (h' : Trace a input guards m u d t) :
    Trace a input guards (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Finite fuel retains the actual suspended state and all work already performed. -/
def runFuel (a : F) (input : Input F) (guards : List (F × F)) :
    ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step a input guards s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input guards n t; (r.1, c + r.2)

theorem Trace.runFuel_eq {a : F} {input : Input F} {guards : List (F × F)}
    {n c : ℕ} {s t : Configuration F}
    (h : Trace a input guards n s c t) : runFuel a input guards n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]


/-- Equal raw grids preserve every finite interpreted prefix and exact cost. -/
theorem runFuel_same (a : F) (input : Input F) (n : ℕ) (s : Configuration F) :
    runFuel a input input.samples n s = QuadraticPreparedDecoderMachine.runFuel a input n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [runFuel, QuadraticPreparedDecoderMachine.runFuel, step_same]
      cases QuadraticPreparedDecoderMachine.step a input s with
      | none => rfl
      | some p => simp only [ih]

/-- Completed execution is fixed under surplus fuel, with exactly the same accumulated work. -/
theorem Trace.runFuel_done {a : F} {input : Input F} {guards : List (F × F)}
    {n c : ℕ} {s : Configuration F} {out : Option (List (List F))}
    (h : Trace a input guards n s c (.done out)) (extra : ℕ) :
    runFuel a input guards (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head]
      dsimp only
      rw [ih he]

end ReedSolomon.ListDecoding.QuadraticSeparateSampleDecoder
