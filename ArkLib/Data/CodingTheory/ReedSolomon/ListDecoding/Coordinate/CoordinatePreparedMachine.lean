/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinatePreparedInput
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Coordinates.StagesMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateOutputMachine
/-!
# Prepared decoder over literal base-field coordinate pairs

The three actual children allocate input pairs, enumerate stage roots, and collect base outputs.
All extension values in runtime states are literal pairs. Parent steps preserve each complete
child cost and add their own dispatch charge. Only already materialized samples are supplied.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticPreparedDecoderMachine

abbrev Term := MvPolynomial.EvaluationMachine.Term

/-- Raw pair samples and base received rows, with the original integer parameters. -/
structure Input (F : Type*) where
  alphabet : List (F × F)
  samples : List (F × F)
  received : List (F × F)
  order : ℕ
  degree : ℕ
  residualLength : ℕ
  dimension : ℕ
  agreement : ℕ

/-- Actual suspended coordinate children and retained root input records. -/
inductive Configuration (F : Type*) where
  | start (terms : List (Term F))
  | convert (inner : QuadraticPreparedInputMachine.Configuration F)
  | roots (input : HiddenDerivative.QuadraticStageRootsMachine.Input F)
      (inner : HiddenDerivative.QuadraticStageRootsMachine.Configuration F)
  | collect (inner : QuadraticCanonicalOutputMachine.Configuration F)
  | emit (output : Option (List (List F)))
  | done (output : Option (List (List F)))

/-- Allocate one bounded record of immutable roots at the child handoff. -/
def rootInput {F : Type*} (input : Input F) (terms : List (Term (F × F))) :
    HiddenDerivative.QuadraticStageRootsMachine.Input F := ⟨input.alphabet, terms, input.order⟩

variable {F : Type*} [Field F] [DecidableEq F]

/-- No decoding, algebra-map callback, or declarative child output is executed here. -/
def step (a : F) (input : Input F) : Configuration F → Option (Configuration F × ℕ)
  | .start ts => some (.convert (.scan ts []), 4)
  | .convert s => match QuadraticPreparedInputMachine.step s with
      | some (t, c) => some (.convert t, c.total + 3)
      | none => match s with
          | .done ts => some (.roots (rootInput input ts) (.start input.samples), 8)
          | _ => none
  | .roots ri s => match HiddenDerivative.QuadraticStageRootsMachine.step a ri input.degree
      input.residualLength s with
      | some (t, c) => some (.roots ri t, c.total + 3)
      | none => match s with
          | .done none => some (.emit none, 3)
          | .done (some records) => some (.collect (.start records), 4)
          | _ => none
  | .collect s => match QuadraticCanonicalOutputMachine.step a input.order input.samples
      (input.degree + 1) input.dimension input.agreement input.received s with
      | some (t, c) => some (.collect t, c + 3)
      | none => match s with
          | .done out => some (.emit (some out), 4)
          | _ => none
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- Actual successor equations and full accumulated scalar primitive totals. -/
inductive Trace (a : F) (input : Input F) :
    ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace a input 0 s 0 s
  | cons {n s u t c d} (head : step a input s = some (u, c))
      (tail : Trace a input n u d t) : Trace a input (n + 1) s (c + d) t

theorem single {a : F} {input : Input F} {s t : Configuration F} {c : ℕ}
    (h : step a input s = some (t, c)) : Trace a input 1 s c t := by
  simpa using Trace.cons h (Trace.nil t)

theorem Trace.trans {a : F} {input : Input F} {n m : ℕ} {s u t : Configuration F} {c d : ℕ}
    (h : Trace a input n s c u) (h' : Trace a input m u d t) :
    Trace a input (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Finite fuel retains the actual suspended state and all work already performed. -/
def runFuel (a : F) (input : Input F) : ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step a input s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel a input n t; (r.1, c + r.2)

theorem Trace.runFuel_eq {a : F} {input : Input F} {n c : ℕ} {s t : Configuration F}
    (h : Trace a input n s c t) : runFuel a input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp only [runFuel, head, ih]

/-- Completed execution is fixed under surplus fuel, with exactly the same accumulated work. -/
theorem Trace.runFuel_done {a : F} {input : Input F}
    {n c : ℕ} {s : Configuration F} {out : Option (List (List F))}
    (h : Trace a input n s c (.done out)) (extra : ℕ) :
    runFuel a input (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head]
      dsimp only
      rw [ih he]

end ReedSolomon.ListDecoding.QuadraticPreparedDecoderMachine
