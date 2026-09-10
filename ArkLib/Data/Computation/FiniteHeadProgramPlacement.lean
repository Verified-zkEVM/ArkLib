/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FiniteHeadProgram

/-!
# Static physical placement of a finite-head program

An immutable finite wiring selects distinct physical tapes. The placed program reads only their
heads and directs its literal actions to those positions; every unowned position receives keep.
There is one runtime bank. Projection and framing are proof-side descriptions of that bank,
never instructions that copy, mirror or rename whole words. Placement preserves the exact count
of simultaneous finite-head transitions; it is not a serial bit-RAM or heap compiler.
-/

@[expose] public section

namespace Computation.FiniteHeadProgramPlacement

open FiniteHeadProgram

/-- A finite injection and an executable ownership table, certified to agree. -/
structure Wiring (inner outer : ℕ) where
  place : Fin inner ↪ Fin outer
  owner : Fin outer → Option (Fin inner)
  owner_place : ∀ i, owner (place i) = some i
  place_owner : ∀ j i, owner j = some i → place i = j

/-- Route literal actions by the fixed ownership table, retaining all unowned tapes. -/
def placeActions {inner outer : ℕ} (w : Wiring inner outer) (actions : Fin inner → Action) :
    Fin outer → Action := fun j ↦ match w.owner j with
      | none => .keep
      | some i => actions i

/-- The new table receives only finite head observations and retains the original finite control. -/
def placeProgram {states inner outer : ℕ} (w : Wiring inner outer) (p : Program states inner) :
    Program states outer where
  dispatch control heads :=
    (p.dispatch control (fun i ↦ heads (w.place i))).map fun instruction ↦
      (instruction.1, placeActions w instruction.2)

/-- Proof-only projection: each inner tape denotes its one actual physical position. -/
def project {states inner outer : ℕ} (w : Wiring inner outer) (s : Configuration states outer) :
    Configuration states inner := ⟨s.control, fun i ↦ s.bank (w.place i)⟩

/-- Proof-only framing uses the supplied outside contents only at unowned physical positions. -/
def frame {states inner outer : ℕ} (w : Wiring inner outer) (s : Configuration states inner)
    (outside : Fin outer → List Bool) : Configuration states outer :=
  ⟨s.control, fun j ↦ match w.owner j with
    | none => outside j
    | some i => s.bank i⟩

/-- Every owned tape projects back to exactly the original word. -/
theorem project_frame {states inner outer : ℕ} (w : Wiring inner outer)
    (s : Configuration states inner) (outside : Fin outer → List Bool) :
    project w (frame w s outside) = s := by
  cases s with
  | mk control bank =>
      apply congrArg (Configuration.mk control)
      funext i
      simp only [frame, w.owner_place]

/-- Any physical state decomposes into its owned view and unchanged outside contents. -/
theorem frame_project {states inner outer : ℕ} (w : Wiring inner outer)
    (s : Configuration states outer) : frame w (project w s) s.bank = s := by
  cases s with
  | mk control bank =>
      apply congrArg (Configuration.mk control)
      funext j
      cases ho : w.owner j with
      | none => rfl
      | some i => simp only [project, w.place_owner j i ho]

/-- Framed instruction selection sees precisely the same current heads as the inner table. -/
theorem decision_frame {states inner outer : ℕ} (w : Wiring inner outer)
    (p : Program states inner) (s : Configuration states inner)
    (outside : Fin outer → List Bool) :
    decision (placeProgram w p) (frame w s outside) =
      (decision p s).map (fun instruction ↦ (instruction.1, placeActions w instruction.2)) := by
  simp only [decision, placeProgram, frame, observe, w.owner_place]
  rfl

/-- One inner edge is exactly one placed edge, with the same unchanged outside frame. -/
theorem step_frame {states inner outer : ℕ} (w : Wiring inner outer)
    (p : Program states inner) (s : Configuration states inner)
    (outside : Fin outer → List Bool) :
    step (placeProgram w p) (frame w s outside) =
      (step p s).map (fun t ↦ frame w t outside) := by
  simp only [step, decision_frame]
  cases hd : decision p s with
  | none => rfl
  | some instruction =>
      apply congrArg some
      dsimp only
      apply congrArg (Configuration.mk instruction.1)
      funext j
      cases ho : w.owner j <;> simp only [applyActions, placeActions, frame, ho, Action.apply]

/-- Trace placement preserves every instruction count and leaves the outside frame fixed. -/
theorem trace_frame {states inner outer n : ℕ} (w : Wiring inner outer)
    {p : Program states inner} {s t : Configuration states inner}
    (outside : Fin outer → List Bool) (h : Trace p n s t) :
    Trace (placeProgram w p) n (frame w s outside) (frame w t outside) := by
  induction h with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (by rw [step_frame, head]; rfl) ih

/-- The actual placed interpreter preserves every complete, partial and surplus-fuel run. -/
theorem runFuel_frame {states inner outer : ℕ} (w : Wiring inner outer)
    (p : Program states inner) (fuel : ℕ) (s : Configuration states inner)
    (outside : Fin outer → List Bool) :
    runFuel (placeProgram w p) fuel (frame w s outside) = frame w (runFuel p fuel s) outside := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFuel, step_frame]
      cases step p s with
      | none => rfl
      | some t => exact ih t

/-- Any actual physical initial bank runs with the exact projected inner execution. -/
theorem runFuel_project {states inner outer : ℕ} (w : Wiring inner outer)
    (p : Program states inner) (fuel : ℕ) (s : Configuration states outer) :
    project w (runFuel (placeProgram w p) fuel s) = runFuel p fuel (project w s) := by
  have h := runFuel_frame w p fuel (project w s) s.bank
  rw [frame_project] at h
  rw [h, project_frame]

/-- Arbitrary unowned physical words survive every actual run without copying or reconstruction. -/
theorem runFuel_unowned {states inner outer : ℕ} (w : Wiring inner outer)
    (p : Program states inner) (fuel : ℕ) (s : Configuration states outer)
    (j : Fin outer) (hj : w.owner j = none) :
    (runFuel (placeProgram w p) fuel s).bank j = s.bank j := by
  have h := runFuel_frame w p fuel (project w s) s.bank
  rw [frame_project] at h
  rw [h]
  simp only [frame, hj]

/-- A contiguous placement with program-fixed banks before and after the owned interval. -/
def offset (inner before after : ℕ) : Wiring inner (before + inner + after) where
  place :=
    { toFun := fun i ↦ ⟨before + i.val, by omega⟩
      inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega }
  owner j := if h : before ≤ j.val ∧ j.val < before + inner then
    some ⟨j.val - before, by omega⟩ else none
  owner_place i := by
    change (if h : before ≤ before + i.val ∧ before + i.val < before + inner then
      some (⟨before + i.val - before, by omega⟩ : Fin inner) else none) = some i
    have h : before ≤ before + i.val ∧ before + i.val < before + inner := by omega
    rw [dif_pos h]
    congr 1
    apply Fin.ext
    change before + i.val - before = i.val
    omega
  place_owner j i h := by
    change (⟨before + i.val, by omega⟩ : Fin (before + inner + after)) = j
    split_ifs at h with hj
    cases h
    apply Fin.ext
    change before + (j.val - before) = j.val
    omega

end Computation.FiniteHeadProgramPlacement
