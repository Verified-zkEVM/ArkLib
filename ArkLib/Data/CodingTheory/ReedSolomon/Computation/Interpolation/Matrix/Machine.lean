/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.PointMachine
/-!
# Materialized received-point interpolation matrices

The input is a materialized list of received point/value pairs and a supplied ambient D. Actual
support enumeration and a charged cell count determine the common width, even on empty input.
Each point executes the proved point-block assembler; row counting and concatenation visit and
charge every copied cell. Counters record the actual point and row counts. No list length,
flatten, or matrix-entry callback is executed. Point order and support-column order are preserved.

Each recursive clause charges 32 primitive units plus its executed callees. These cover control,
scalar-input reads, natural counter updates, cursor/register accesses, and result allocation.
List tails are shared immutably. Bit costs, garbage collection and host fuel are outside this
unit-operation model. The initial support enumeration is additional to each point's enumeration.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine

abbrev Row (F : Type*) := Matrix.PivotSelectionMachine.Row F

/-- Explicit dimension metadata accompanies the solver-compatible augmented rows. -/
structure Result (F : Type*) where
  columns : ℕ
  points : ℕ
  rowCount : ℕ
  rows : List (Row F)
  deriving DecidableEq, Repr

/-- Compute a length by visiting every actual cell, including the terminal test. -/
def countCells {α : Type*} : List α → ℕ × ℕ
  | [] => (0, 32)
  | _ :: xs =>
      let r := countCells xs
      (r.1 + 1, 32 + r.2)

theorem countCells_correct {α : Type*} (xs : List α) :
    countCells xs = (xs.length, 32 * (xs.length + 1)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countCells, ih]; omega

variable {F : Type*} [CommRing F]

/-- Materialize every point block at strict jet cutoff `J` and concatenate with explicit counting
and copying. -/
def traverseWithBudget (D d m J A width : ℕ) : List (F × F) → Option (Result F) × ℕ
  | [] => (some ⟨width, 0, 0, []⟩, 32)
  | p :: ps =>
      let head := InterpolationPointBlockMachine.assembleWithBudget D d m J A p.1 p.2
      match head.1 with
      | none => (none, 32 + head.2)
      | some rs =>
          let counted := countCells rs
          let tail := traverseWithBudget D d m J A width ps
          match tail.1 with
          | none => (none, 32 + head.2 + counted.2 + tail.2)
          | some rest =>
              let joined := LocalColumnRewriteMachine.appendCells rs rest.rows
              (some ⟨width, rest.points + 1, counted.1 + rest.rowCount, joined.1⟩,
                32 + head.2 + counted.2 + tail.2 + joined.2)

/-- Legacy traversal specializes the strict jet cutoff to `2 * m`. -/
def traverse (D d m A width : ℕ) (received : List (F × F)) : Option (Result F) × ℕ :=
  traverseWithBudget D d m (2 * m) A width received

/-- Full received matrix construction at strict jet cutoff `J`. -/
def runWithBudget (D d m J A : ℕ) (received : List (F × F)) : Option (Result F) × ℕ :=
  let support := InterpolationSupportMachine.enumerateWithBudget D d m J A
  match support.1 with
  | .done vs =>
      let width := countCells vs
      let result := traverseWithBudget D d m J A width.1 received
      (result.1, 32 + support.2 + width.2 + result.2)
  | _ => (none, 32 + support.2)

/-- Legacy received-matrix construction specializes the strict jet cutoff to `2 * m`. -/
def run (D d m A : ℕ) (received : List (F × F)) : Option (Result F) × ℕ :=
  runWithBudget D d m (2 * m) A received

/-- Successful traversal preserves block order, counts dimensions, and charges all cell work.
The function spec is a proof-only description of the already executed point blocks. -/
theorem traverseWithBudget_correct (D d m J A width B R : ℕ) (received : List (F × F))
    (spec : F × F → List (Row F))
    (h : ∀ p ∈ received, ∃ c,
      InterpolationPointBlockMachine.assembleWithBudget D d m J A p.1 p.2 =
        (some (spec p), c) ∧
      (spec p).length ≤ R ∧ c ≤ B) :
    ∃ c, traverseWithBudget D d m J A width received =
      (some ⟨width, received.length, (received.flatMap spec).length, received.flatMap spec⟩, c) ∧
      (received.flatMap spec).length ≤ R * received.length ∧
      c ≤ (B + 64 * (R + 1) + 64) * (received.length + 1) := by
  induction received with
  | nil => exact ⟨32, rfl, by simp, by simp⟩
  | cons p ps ih =>
    obtain ⟨c, hc, hl, hb⟩ := h p (by simp)
    obtain ⟨k, hk, hlen, hcost⟩ := ih (fun p hp => h p (by simp [hp]))
    refine ⟨32 + c + 32 * ((spec p).length + 1) + k + 32 * ((spec p).length + 1),
      ?_, ?_, ?_⟩
    · simp [traverseWithBudget, hc, countCells_correct, hk,
        LocalColumnRewriteMachine.appendCells_correct]
    · simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith
    · simp only [List.length_cons]
      nlinarith

/-- Correctness of legacy traversal at strict cutoff `2 * m`. -/
theorem traverse_correct (D d m A width B R : ℕ) (received : List (F × F))
    (spec : F × F → List (Row F))
    (h : ∀ p ∈ received, ∃ c,
      InterpolationPointBlockMachine.assemble D d m A p.1 p.2 = (some (spec p), c) ∧
      (spec p).length ≤ R ∧ c ≤ B) :
    ∃ c, traverse D d m A width received =
      (some ⟨width, received.length, (received.flatMap spec).length, received.flatMap spec⟩, c) ∧
      (received.flatMap spec).length ≤ R * received.length ∧
      c ≤ (B + 64 * (R + 1) + 64) * (received.length + 1) := by
  have hg : ∀ p ∈ received, ∃ c,
      InterpolationPointBlockMachine.assembleWithBudget D d m (2 * m) A p.1 p.2 =
        (some (spec p), c) ∧ (spec p).length ≤ R ∧ c ≤ B := by
    intro p hp
    obtain ⟨c, hc, hr, hb⟩ := h p hp
    exact ⟨c, by simpa [InterpolationPointBlockMachine.assemble] using hc, hr, hb⟩
  simpa [traverse] using
    traverseWithBudget_correct D d m (2 * m) A width B R received spec hg

end ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine
