/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.CellPayloadMachine
public import ArkLib.Data.Computation.FixedWidthWordMachine
public import ArkLib.Data.Computation.SharedListCellReadMachine

/-!
# Shared-list cell reads with physically constructed width markers

The input is a pointer and a retained scalar-width reference, such as the modulus. Actual
payload construction copies these words into a block marker; actual shape construction copies
and restores the reference to produce the head marker. Both markers feed the existing literal
cell reader on one fixed sixteen-tape bank. Their bit values are irrelevant to the reader.

The live-cell theorem needs no caller-provided length tapes. Nil testing remains a separate
instruction: this entry reads a cell and does not interpret the all-zero pointer as an empty
list. A malformed tag remains the child's retained rejection state. No validity check or
list-level operation is assumed free. Costs count this explicit bit-RAM program only.
-/

@[expose] public section

namespace Computation.SharedListPreparedRead

open AddressedBits (Memory)
open SharedListHeap (Cell RepList)

inductive Control where
  | building (child : CellPayloadMachine.Control)
  | shaping (pointer blockShape : List Bool) (child : FixedWidthWordMachine.Control)
  | reading (reference : List Bool) (child : SharedListCellRead.Control)
  deriving DecidableEq, Repr

structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- Only literal child instructions and tape-preserving handoffs run here. -/
def step : Configuration → Option Configuration
  | ⟨mem, .building child⟩ =>
      match CellPayloadMachine.step child with
      | some next => some ⟨mem, .building next⟩
      | none => match child with
          | .done reference pointer block =>
              some ⟨mem, .shaping pointer block (.shapeStart reference)⟩
          | _ => none
  | ⟨mem, .shaping pointer block child⟩ =>
      match FixedWidthWordMachine.step child with
      | some next => some ⟨mem, .shaping pointer block next⟩
      | none => match child with
          | .shapeDone reference shape =>
              some ⟨mem, .reading reference (.reading shape (.next pointer [] block []))⟩
          | _ => none
  | ⟨mem, .reading reference child⟩ =>
      match SharedListCellRead.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .reading reference next.control⟩
      | none => none

/-- Pointer zero, block marker four, head marker twelve, head output thirteen, reference
fourteen and reference scratch fifteen are fixed across all phases. -/
def tapes : Control → Fin 16 → List Bool
  | .building child =>
      let t := CellPayloadMachine.physicalTapes child
      ![t 2, t 3, [], [], t 4, [], [], [], [], [], [], [], [], [], t 0, t 1]
  | .shaping pointer block child =>
      let t := FixedWidthWordMachine.tapes child
      ![pointer, [], [], [], block, [], [], [], [], [], [], [],
        t.right, t.output, t.left, t.saved]
  | .reading reference child =>
      let t := SharedListCellRead.physicalTapes child
      ![t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7, t 8, t 9, t 10, t 11,
        t 12, t 13, reference, []]

theorem build_handoff_tapes (reference pointer block : List Bool) :
    tapes (.building (.done reference pointer block)) =
      tapes (.shaping pointer block (.shapeStart reference)) := by
  funext i
  fin_cases i <;> rfl

theorem shape_handoff_tapes (reference pointer block shape : List Bool) :
    tapes (.shaping pointer block (.shapeDone reference shape)) =
      tapes (.reading reference (.reading shape (.next pointer [] block []))) := by
  funext i
  fin_cases i <;> rfl

private theorem bank_sixteen
    {a b c d e f g h i j k l m n o p a' b' c' d' e' f' g' h' i' j' k' l' m' n' o' p' : List Bool}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f')
    (hg : BitLocalActions.CellStep g g') (hh : BitLocalActions.CellStep h h')
    (hi : BitLocalActions.CellStep i i') (hj : BitLocalActions.CellStep j j')
    (hk : BitLocalActions.CellStep k k') (hl : BitLocalActions.CellStep l l')
    (hm : BitLocalActions.CellStep m m') (hn : BitLocalActions.CellStep n n')
    (ho : BitLocalActions.CellStep o o') (hp : BitLocalActions.CellStep p p') :
    BitLocalActions.BankStep ![a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p]
      ![a', b', c', d', e', f', g', h', i', j', k', l', m', n', o', p'] := by
  intro x
  fin_cases x
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf
  · exact hg
  · exact hh
  · exact hi
  · exact hj
  · exact hk
  · exact hl
  · exact hm
  · exact hn
  · exact ho
  · exact hp

/-- Every successor is local on the same physical tape bank, including both handoffs. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s.control) (tapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | building child =>
      cases hs : CellPayloadMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := CellPayloadMachine.step_local hs
          exact bank_sixteen (hl 2) (hl 3) (.keep _) (.keep _) (hl 4)
            (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
            (.keep _) (.keep _) (hl 0) (hl 1)
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child <;> try cases h
          rw [build_handoff_tapes]
          intro i
          exact .keep _
  | shaping pointer block child =>
      cases hs : FixedWidthWordMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := FixedWidthWordMachine.step_local hs
          exact bank_sixteen (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
            (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
            hl.2.1 hl.2.2.2 hl.1 hl.2.2.1
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child <;> try cases h
          rw [shape_handoff_tapes]
          intro i
          exact .keep _
  | reading reference child =>
      cases hs : SharedListCellRead.step ⟨mem, child⟩ with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := SharedListCellRead.step_local hs
          exact bank_sixteen (hl 0) (hl 1) (hl 2) (hl 3) (hl 4) (hl 5) (hl 6)
            (hl 7) (hl 8) (hl 9) (hl 10) (hl 11) (hl 12) (hl 13) (.keep _) (.keep _)
      | none => simp only [step, hs] at h; cases h

inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

theorem lift_build (mem : Memory) {n : ℕ} {s t : CellPayloadMachine.Control}
    (h : CellPayloadMachine.Trace n s t) :
    Trace n ⟨mem, .building s⟩ ⟨mem, .building t⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_shape (mem : Memory) (pointer block : List Bool) {n : ℕ}
    {s t : FixedWidthWordMachine.Control} (h : FixedWidthWordMachine.Trace n s t) :
    Trace n ⟨mem, .shaping pointer block s⟩ ⟨mem, .shaping pointer block t⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_read (reference : List Bool) {n : ℕ} {s t : SharedListCellRead.Configuration}
    (h : SharedListCellRead.Trace n s t) :
    Trace n ⟨s.memory, .reading reference s.control⟩
      ⟨t.memory, .reading reference t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Includes block construction, head-shape construction, two handoffs and the complete reader. -/
def steps (w h : ℕ) : ℕ := 4 * h + 2 * w + 10 + SharedListCellRead.steps w h

/-- Both physically constructed markers feed the same cell read, retaining the exact reference. -/
theorem read_trace {mem : Memory} {w h : ℕ} {p head tail : List Bool}
    (hc : Cell mem w h p head tail) (reference : List Bool) (href : reference.length = h) :
    Trace (steps w h) ⟨mem, .building (.copyTail reference p [] [])⟩
      ⟨mem, .reading reference (.done p (List.replicate (1 + h + w) true) head tail)⟩ := by
  have hb := lift_build mem (CellPayloadMachine.materialize_trace reference p)
  have hs := lift_shape mem p (true :: (reference ++ p))
    (FixedWidthWordMachine.shape_correct reference).1
  have hr := lift_read reference (SharedListCellRead.cell_read_trace hc
    (true :: (reference ++ p)) (List.replicate reference.length false)
    (by simp [href, hc.pointer_width]; omega) (by simp [href]))
  have hh₁ : Trace 1 ⟨mem, .building (.done reference p (true :: (reference ++ p)))⟩
      ⟨mem, .shaping p (true :: (reference ++ p)) (.shapeStart reference)⟩ :=
    .cons rfl (.nil _)
  have hh₂ : Trace 1
      ⟨mem, .shaping p (true :: (reference ++ p))
        (.shapeDone reference (List.replicate reference.length false))⟩
      ⟨mem, .reading reference (.reading (List.replicate reference.length false)
        (.next p [] (true :: (reference ++ p)) []))⟩ := .cons rfl (.nil _)
  convert (((hb.append hh₁).append hs).append hh₂).append hr using 1
  simp only [steps, href, hc.pointer_width]
  omega

/-- Exact head/tail, unchanged RAM and all old represented lists refer to this one final run. -/
theorem read_execution {mem : Memory} {w h : ℕ} {p head tail : List Bool}
    (hc : Cell mem w h p head tail) (reference : List Bool) (href : reference.length = h) :
    ∃ final : Configuration,
      Trace (steps w h) ⟨mem, .building (.copyTail reference p [] [])⟩ final ∧
      runFuel (steps w h) ⟨mem, .building (.copyTail reference p [] [])⟩ = final ∧
      final.memory = mem ∧
      final.control = .reading reference
        (.done p (List.replicate (1 + h + w) true) head tail) ∧
      (∀ old ys, RepList mem w h old ys → RepList final.memory w h old ys) := by
  have ht := read_trace hc reference href
  exact ⟨_, ht, ht.runFuel_eq, rfl, rfl, fun _ _ hr ↦ hr⟩

end Computation.SharedListPreparedRead
