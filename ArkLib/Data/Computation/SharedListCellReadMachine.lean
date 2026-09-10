/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListRead

/-!
# Literal cell reads with physical head and tail extraction

The block reader produces an actual payload on tape 10. Its live tag is checked, then a
materialized head-length tape controls a bitwise split. The head is reversed onto tape 13;
the untouched payload suffix stays on tape 10 as the tail pointer. All fourteen physical
tape positions are fixed through every handoff. No list `take`, `drop`, length computation,
whole-word movement, or uncharged parsing runs in the successor.

Both length tapes and the pointer are caller-provided physical inputs. A represented live cell
returns its exact head/tail and unchanged memory. Nil-pointer testing and construction of the
length tapes are separate obligations; malformed tag/short payload rejection retains the tapes.
-/

@[expose] public section

namespace Computation.SharedListCellRead

open AddressedBits (Memory)
open SharedListHeap (Cell RepList)

/-- Fixed-phase read and parser controls, with no numeric registers. -/
inductive Control where
  | reading (headShape : List Bool) (child : BitMemoryRead.Control)
  | tag (base index payload headShape : List Bool)
  | scan (base index payload headShape reversed : List Bool)
  | reverse (base index tail source head : List Bool)
  | done (base index head tail : List Bool)
  | rejected (base index payload headShape reversed : List Bool)
  deriving DecidableEq, Repr

/-- The actual memory flows unchanged through parsing and through valid block reads. -/
structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- Literal read instructions, tag inspection, head-bit extraction and reversal. -/
def step : Configuration → Option Configuration
  | ⟨mem, .reading shape child⟩ =>
      match BitMemoryRead.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .reading shape next.control⟩
      | none => match child with
          | .done base index payload => some ⟨mem, .tag base index payload shape⟩
          | _ => none
  | ⟨mem, .tag base index (true :: rest) shape⟩ =>
      some ⟨mem, .scan base index rest shape []⟩
  | ⟨mem, .tag base index payload shape⟩ =>
      some ⟨mem, .rejected base index payload shape []⟩
  | ⟨mem, .scan base index payload [] reversed⟩ =>
      some ⟨mem, .reverse base index payload reversed []⟩
  | ⟨mem, .scan base index (b :: rest) (_ :: shape) reversed⟩ =>
      some ⟨mem, .scan base index rest shape (b :: reversed)⟩
  | ⟨mem, .scan base index [] (marker :: shape) reversed⟩ =>
      some ⟨mem, .rejected base index [] (marker :: shape) reversed⟩
  | ⟨mem, .reverse base index tail (b :: rest) head⟩ =>
      some ⟨mem, .reverse base index tail rest (b :: head)⟩
  | ⟨mem, .reverse base index tail [] head⟩ => some ⟨mem, .done base index head tail⟩
  | ⟨_, .done _ _ _ _⟩ | ⟨_, .rejected _ _ _ _ _⟩ => none

/-- Counts of the actual combined read/parser successors. -/
inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- External observation fuel is not a machine register. -/
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

theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) :
    runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- The retained block child operates on the same memory and keeps the separate head-length tape. -/
theorem lift_reader (shape : List Bool) {n : ℕ} {s t : BitMemoryRead.Configuration}
    (h : BitMemoryRead.Trace n s t) :
    Trace n ⟨s.memory, .reading shape s.control⟩ ⟨t.memory, .reading shape t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- The already-read head prefix is removed one bit per transition; the tail is never copied. -/
theorem scan_trace (mem : Memory) (base index head tail shape saved : List Bool)
    (hlen : shape.length = head.length) :
    Trace (head.length + 1) ⟨mem, .scan base index (head ++ tail) shape saved⟩
      ⟨mem, .reverse base index tail (head.reverse ++ saved) []⟩ := by
  induction head generalizing shape saved with
  | nil =>
      have hs : shape = [] := List.length_eq_zero_iff.mp hlen
      subst shape
      exact .cons rfl (.nil _)
  | cons b bs ih =>
      cases shape with
      | nil => simp at hlen
      | cons marker shape =>
          have hlen' : shape.length = bs.length := by simpa using hlen
          simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
            Trace.cons (by rfl) (ih shape (b :: saved) hlen')

/-- Head reversal uses separate fixed source/output tapes and retains the tail pointer. -/
theorem reverse_trace (mem : Memory) (base index tail source head : List Bool) :
    Trace (source.length + 1) ⟨mem, .reverse base index tail source head⟩
      ⟨mem, .done base index (source.reverse ++ head) tail⟩ := by
  induction source generalizing head with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b :: head))

/-- The read/parser handoff, tag check, physical split and reversal all contribute to this count. -/
def steps (w h : ℕ) : ℕ := BitMemoryRead.steps w 0 (1 + h + w) + 2 * h + 4

/-- A represented live cell is physically read and split into the exact head and tail words. -/
theorem cell_read_trace {mem : Memory} {w h : ℕ} {p head tail : List Bool}
    (hc : Cell mem w h p head tail) (blockShape headShape : List Bool)
    (hb : blockShape.length = 1 + h + w) (hh : headShape.length = h) :
    Trace (steps w h) ⟨mem, .reading headShape (.next p [] blockShape [])⟩
      ⟨mem, .done p (List.replicate (1 + h + w) true) head tail⟩ := by
  have hr := BitMemoryRead.load_trace mem p [] blockShape
  rw [hc.pointer_width, hb, SharedListRead.load_cell hc blockShape hb] at hr
  simp only [List.length_nil, List.append_nil] at hr
  have hs := scan_trace mem p (List.replicate (1 + h + w) true) head tail headShape []
    (hh.trans hc.head_width.symm)
  simp only [List.append_nil] at hs
  have hv := reverse_trace mem p (List.replicate (1 + h + w) true) tail head.reverse []
  simp only [List.reverse_reverse, List.append_nil] at hv
  have ht : Trace 2
      ⟨mem, .reading headShape (.done p (List.replicate (1 + h + w) true)
        (true :: (head ++ tail)))⟩
      ⟨mem, .scan p (List.replicate (1 + h + w) true) (head ++ tail) headShape []⟩ :=
    .cons rfl (.cons rfl (.nil _))
  convert (((lift_reader headShape hr).append ht).append hs).append hv using 1
  simp only [steps, List.length_reverse, hc.head_width]
  omega

/-- The same complete run returns both physical words and preserves every represented list. -/
theorem cell_read_execution {mem : Memory} {w h : ℕ} {p head tail : List Bool}
    (hc : Cell mem w h p head tail) (blockShape headShape : List Bool)
    (hb : blockShape.length = 1 + h + w) (hh : headShape.length = h) :
    ∃ final : Configuration,
      Trace (steps w h) ⟨mem, .reading headShape (.next p [] blockShape [])⟩ final ∧
      runFuel (steps w h) ⟨mem, .reading headShape (.next p [] blockShape [])⟩ = final ∧
      final.memory = mem ∧
      final.control = .done p (List.replicate (1 + h + w) true) head tail ∧
      (∀ old ys, RepList mem w h old ys → RepList final.memory w h old ys) := by
  have ht := cell_read_trace hc blockShape headShape hb hh
  exact ⟨_, ht, ht.runFuel_eq, rfl, rfl, fun _ _ hr ↦ hr⟩

/-- Fixed positions: reader 0--10, reversed head 11, head-length tape 12, final head 13. -/
def physicalTapes : Control → Fin 14 → List Bool
  | .reading shape child =>
      let t := BitMemoryRead.physicalTapes child
      ![t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7, t 8, t 9, t 10, [], shape, []]
  | .tag base index payload shape =>
      ![base, [], index, [], [], [], [], [], [], [], payload, [], shape, []]
  | .scan base index payload shape saved | .rejected base index payload shape saved =>
      ![base, [], index, [], [], [], [], [], [], [], payload, saved, shape, []]
  | .reverse base index tail source head =>
      ![base, [], index, [], [], [], [], [], [], [], tail, source, [], head]
  | .done base index head tail =>
      ![base, [], index, [], [], [], [], [], [], [], tail, [], [], head]

private theorem bank_fourteen
    {a b c d e f g h i j k l m n a' b' c' d' e' f' g' h' i' j' k' l' m' n' : List Bool}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f')
    (hg : BitLocalActions.CellStep g g') (hh : BitLocalActions.CellStep h h')
    (hi : BitLocalActions.CellStep i i') (hj : BitLocalActions.CellStep j j')
    (hk : BitLocalActions.CellStep k k') (hl : BitLocalActions.CellStep l l')
    (hm : BitLocalActions.CellStep m m') (hn : BitLocalActions.CellStep n n') :
    BitLocalActions.BankStep ![a, b, c, d, e, f, g, h, i, j, k, l, m, n]
      ![a', b', c', d', e', f', g', h', i', j', k', l', m', n'] := by
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

private theorem reader_none (mem : Memory) (child : BitMemoryRead.Control)
    (h : BitMemoryRead.step ⟨mem, child⟩ = none) :
    (∃ b i out, child = .done b i out) ∨
      ∃ b i rest out c, child = .failed b i rest out c := by
  cases child with
  | next base index remaining out => cases remaining <;> simp [BitMemoryRead.step] at h
  | copyBase index remaining source saved bus out =>
      cases source <;> simp [BitMemoryRead.step] at h
  | restoreBase index remaining source base bus out =>
      cases source <;> simp [BitMemoryRead.step] at h
  | copyIndex base remaining source saved bus out =>
      cases source <;> simp [BitMemoryRead.step] at h
  | restoreIndex base remaining source index bus out =>
      cases source <;> simp [BitMemoryRead.step] at h
  | reading base index remaining out c =>
      cases hs : AddressedBits.step ⟨mem, c⟩ with
      | some t => simp [BitMemoryRead.step, hs] at h
      | none =>
          cases c with
          | done result => cases result <;> simp [BitMemoryRead.step, hs] at h
          | _ => simp [BitMemoryRead.step, hs] at h
  | reverse base index source out => cases source <;> simp [BitMemoryRead.step] at h
  | done base index out => exact Or.inl ⟨base, index, out, rfl⟩
  | failed base index rest out c => exact Or.inr ⟨base, index, rest, out, c, rfl⟩

/-- All combined read/parse transitions satisfy the same fixed-bank local-cell invariant. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (physicalTapes s.control) (physicalTapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | reading shape child =>
      cases hs : BitMemoryRead.step ⟨mem, child⟩ with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := BitMemoryRead.step_local hs
          exact bank_fourteen (hl 0) (hl 1) (hl 2) (hl 3) (hl 4) (hl 5)
            (hl 6) (hl 7) (hl 8) (hl 9) (hl 10) (.keep _) (.keep _) (.keep _)
      | none =>
          rcases reader_none mem child hs with ⟨base, index, out, rfl⟩ | ⟨b, i, r, o, c, rfl⟩
          · cases h; apply bank_fourteen <;> constructor
          · cases h
  | tag base index payload shape =>
      cases payload with
      | nil => cases h; apply bank_fourteen <;> constructor
      | cons b bs => cases b <;> cases h <;> apply bank_fourteen <;> constructor
  | scan base index payload shape saved =>
      cases shape with
      | nil => cases h; apply bank_fourteen <;> constructor
      | cons b bs =>
          cases payload <;> cases h <;> apply bank_fourteen <;> constructor
  | reverse base index tail source head =>
      cases source <;> cases h <;> apply bank_fourteen <;> constructor
  | done base index head tail => cases h
  | rejected base index payload shape saved => cases h

end Computation.SharedListCellRead
