/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.List.Basic
/-!
# Charged constant and empty decoder leaf

Inputs are materialized immutable rows and integer block length and threshold. The leaf first
checks oversizing, then reads at most two rows and compares their received symbols. Equal symbols
produce one descending coefficient cell and one output-list cell in separate instructions.
This leaf uses the flattened primitive-total model of the prepared decoder: natural comparisons,
field equality, dispatch, reads, writes and allocations each have unit charge. It is not a bit-cost
model. No field arithmetic, field enumeration or quadratic setup occurs. Malformed nonoversized
row lists return empty; correctness uses the explicit two-row shape.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SmallBlockDecoderMachine

/-- Fixed-size registers; coefficient and outer-list allocation are separate states. -/
inductive Configuration (F : Type*) where
  | start
  | load
  | compare (left right : F)
  | coefficient (value : F)
  | output (coefficients : List F)
  | empty
  | done (output : List (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [DecidableEq F]

/-- Each charge includes dispatch and its state write. Header: two reads, comparison and branch
plus dispatch/write (6). Load: three list tags, two row projections and register reads/writes (12).
Comparison uses two reads, equality, branch and dispatch/write (6). Each cons allocation costs
read, nil/pointer access, allocation, dispatch and write (5). Empty emission costs 3. -/
def step (n A : ℕ) (rows : List (F × F)) :
    Configuration F → Option (Configuration F × ℕ)
  | .start => some ((if n < A then .empty else .load), 6)
  | .load => match rows with
      | [(_, y), (_, z)] => some (.compare y z, 12)
      | _ => some (.empty, 12)
  | .compare y z => some ((if y = z then .coefficient y else .empty), 6)
  | .coefficient y => some (.output [y], 5)
  | .output cs => some (.done [cs], 5)
  | .empty => some (.done [], 3)
  | .done _ => none

/-- Actual transition traces retain all flattened primitive charges. -/
inductive Trace (n A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace n A rows 0 s 0 s
  | cons {k s u t c e} (head : step n A rows s = some (u, c))
      (tail : Trace n A rows k u e t) : Trace n A rows (k + 1) s (c + e) t

/-- Bounded interpreter for this leaf, with no uncharged candidate construction. -/
def runFuel (n A : ℕ) (rows : List (F × F)) :
    ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | k + 1, s => match step n A rows s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel n A rows k t; (r.1, c + r.2)

/-- Every execution prefix carries its exact operational trace. -/
theorem runFuel_refines (n A : ℕ) (rows : List (F × F)) (fuel : ℕ) (s : Configuration F) :
    ∃ k ≤ fuel, Trace n A rows k s (runFuel n A rows fuel s).2
      (runFuel n A rows fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, Nat.le_refl _, .nil _⟩
  | succ fuel ih =>
      cases hs : step n A rows s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some p =>
          obtain ⟨k, hk, ht⟩ := ih p.1
          exact ⟨k + 1, by omega, by simpa [runFuel, hs] using Trace.cons hs ht⟩

/-- Oversizing executes the threshold check and an explicit empty-output instruction. -/
theorem oversized_run (n A : ℕ) (rows : List (F × F)) (h : n < A) :
    runFuel n A rows 5 .start = (.done [], 9) := by
  simp [runFuel, step, h]

/-- The equal-symbol branch allocates both output cells, with exact charge 34. -/
theorem equal_run (n A : ℕ) (x y z : F) (h : A ≤ n) :
    runFuel n A [(x, y), (z, y)] 5 .start = (.done [[y]], 34) := by
  simp [runFuel, step, Nat.not_lt.mpr h]

/-- Different symbols execute an equality test and an explicit empty emission. -/
theorem different_run (n A : ℕ) (x y z w : F) (h : A ≤ n) (hne : y ≠ w) :
    runFuel n A [(x, y), (z, w)] 5 .start = (.done [], 27) := by
  simp [runFuel, step, Nat.not_lt.mpr h, hne]

/-- Fixed input-independent fuel and primitive bound, including malformed row shapes. -/
theorem run_bounded (n A : ℕ) (rows : List (F × F)) :
    ∃ out c, runFuel n A rows 5 .start = (.done out, c) ∧ c ≤ 34 ∧
      ∃ k ≤ 5, Trace n A rows k .start c (.done out) := by
  have hb : ∃ out c, runFuel n A rows 5 .start = (.done out, c) ∧ c ≤ 34 := by
    by_cases h : n < A
    · exact ⟨[], 9, oversized_run n A rows h, by decide⟩
    have hAn : A ≤ n := by omega
    rcases rows with _ | ⟨⟨x, y⟩, rows⟩
    · exact ⟨[], 21, by simp [runFuel, step, h], by decide⟩
    rcases rows with _ | ⟨⟨z, w⟩, rows⟩
    · exact ⟨[], 21, by simp [runFuel, step, h], by decide⟩
    rcases rows with _ | ⟨p, rows⟩
    · by_cases he : y = w
      · subst w
        exact ⟨[[y]], 34, equal_run n A x y z hAn, Nat.le_refl _⟩
      · exact ⟨[], 27, different_run n A x y z w hAn he, by decide⟩
    · exact ⟨[], 21, by simp [runFuel, step, h], by decide⟩
  obtain ⟨out, c, hr, hc⟩ := hb
  refine ⟨out, c, hr, hc, ?_⟩
  simpa only [hr] using runFuel_refines n A rows 5 .start

end ReedSolomon.ListDecoding.SmallBlockDecoderMachine
