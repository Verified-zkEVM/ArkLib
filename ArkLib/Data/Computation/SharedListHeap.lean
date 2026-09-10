/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AddressedBits

/-!
# Structural shared lists in addressed bit memory

Pointers have a common fixed width; the all-zero pointer is reserved for nil. A cell stores a
true tag, a fixed-width bit word, and a tail pointer in consecutive unary-indexed slots. The
inductive representation describes actual memory observations independently of any successful
execution. Multiple lists may share a tail. A false tag provides freshness relative to every
represented list, without requiring unused bits elsewhere in that pointer block to be zero.

The finite write folds below are semantic specifications only. No allocation, lookup, or bit-cost
claim is made until a literal addressed-bit controller is proved to realize these observations.
-/

@[expose] public section

namespace Computation.SharedListHeap

open AddressedBits (Address Memory)

/-- Reserved nil pointer at the common width. -/
def nilPointer (w : ℕ) : Address := List.replicate w false

/-- Pointer block slot, matching the literal bit-block controller's unary within-word index. -/
def slot (p : Address) (i : ℕ) : Address := p ++ List.replicate i true ++ [false]

/-- Equal-width distinct pointer prefixes name disjoint slots at every index. -/
theorem slot_ne {p q : Address} (hlen : p.length = q.length) (hne : p ≠ q) (i j : ℕ) :
    slot p i ≠ slot q j := by
  intro h
  apply hne
  have ht := congrArg (List.take p.length) h
  have hp : List.take p.length (slot p i) = p := by simp [slot, List.append_assoc]
  have hq : List.take p.length (slot q j) = q := by
    rw [hlen]
    simp [slot, List.append_assoc]
  exact hp.symm.trans (ht.trans hq)

/-- Distinct indices in the same pointer block name distinct bit addresses. -/
theorem slot_injective (p : Address) : Function.Injective (slot p) := by
  intro i j h
  have := congrArg List.length h
  simp only [slot, List.length_append, List.length_replicate, List.length_singleton] at this
  omega

/-- A live cell is specified by the bits physically stored in its pointer block. -/
structure Cell (mem : Memory) (w h : ℕ) (p : Address) (head tail : List Bool) : Prop where
  pointer_width : p.length = w
  head_width : head.length = h
  tail_width : tail.length = w
  not_nil : p ≠ nilPointer w
  tag : mem.lookup (slot p 0) = true
  head_bits : ∀ i : Fin h, mem.lookup (slot p (1 + i.val)) = head[i.val]'(by omega)
  tail_bits : ∀ i : Fin w, mem.lookup (slot p (1 + h + i.val)) = tail[i.val]'(by omega)

/-- Finite structural lists, with unrestricted sharing of represented tails. -/
inductive RepList (mem : Memory) (w h : ℕ) : Address → List (List Bool) → Prop where
  | nil : RepList mem w h (nilPointer w) []
  | cons {p head tail xs} (cell : Cell mem w h p head tail)
      (rest : RepList mem w h tail xs) : RepList mem w h p (head :: xs)

/-- Every represented pointer has the designated width, including nil. -/
theorem RepList.pointer_width {mem w h p xs} (hr : RepList mem w h p xs) : p.length = w := by
  cases hr with
  | nil => simp [nilPointer]
  | cons cell _ => exact cell.pointer_width

/-- Every physically represented scalar word has the designated width. -/
theorem RepList.head_width {mem w h p xs} (hr : RepList mem w h p xs) :
    ∀ x ∈ xs, (x : List Bool).length = h := by
  induction hr with
  | nil => simp
  | cons cell rest ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact cell.head_width
      · exact ih x hx

/-- A cell's head and tail words are determined by its actual bit observations. -/
theorem Cell.unique {mem w h p head tail head' tail'}
    (hc : Cell mem w h p head tail) (hc' : Cell mem w h p head' tail') :
    head = head' ∧ tail = tail' := by
  constructor
  · apply List.ext_getElem
    · exact hc.head_width.trans hc'.head_width.symm
    · intro i hi hi'
      exact (hc.head_bits ⟨i, by simpa only [hc.head_width] using hi⟩).symm.trans
        (hc'.head_bits ⟨i, by simpa only [hc'.head_width] using hi'⟩)
  · apply List.ext_getElem
    · exact hc.tail_width.trans hc'.tail_width.symm
    · intro i hi hi'
      exact (hc.tail_bits ⟨i, by simpa only [hc.tail_width] using hi⟩).symm.trans
        (hc'.tail_bits ⟨i, by simpa only [hc'.tail_width] using hi'⟩)

/-- Finite represented contents are unique even when different lists share heap tails. -/
theorem RepList.unique {mem w h p xs ys} (hx : RepList mem w h p xs)
    (hy : RepList mem w h p ys) : xs = ys := by
  induction hx generalizing ys with
  | nil =>
      cases hy with
      | nil => rfl
      | cons cell _ => exact (cell.not_nil rfl).elim
  | cons cell rest ih =>
      cases hy with
      | nil => exact (cell.not_nil rfl).elim
      | cons cell' rest' =>
          obtain ⟨rfl, rfl⟩ := cell.unique cell'
          exact congrArg (_ :: ·) (ih rest')

/-- The length of a represented list is determined by the stored pointer and memory. -/
theorem RepList.length_eq {mem w h p xs ys} (hx : RepList mem w h p xs)
    (hy : RepList mem w h p ys) : xs.length = ys.length :=
  congrArg List.length (hx.unique hy)

/-- A false tag cannot be a live cell in any structurally represented list. -/
def Fresh (mem : Memory) (p : Address) : Prop := mem.lookup (slot p 0) = false

/-- A live cell differs from every pointer whose actual tag is false. -/
theorem Cell.ne_fresh {mem w h p head tail fresh} (hc : Cell mem w h p head tail)
    (hf : Fresh mem fresh) : p ≠ fresh := by
  intro he
  subst fresh
  have := hc.tag
  rw [hf] at this
  contradiction

/-- Changing only a fresh block preserves every old list, including arbitrarily shared tails.
The frame premise is an observational relation, not an instruction or executable callback. -/
theorem RepList.frame_fresh {mem mem' : Memory} {w h p xs fresh}
    (hr : RepList mem w h p xs) (hf : Fresh mem fresh)
    (hframe : ∀ q, q.length = w → q ≠ fresh → ∀ i,
      mem'.lookup (slot q i) = mem.lookup (slot q i)) : RepList mem' w h p xs := by
  induction hr with
  | nil => exact .nil
  | cons cell rest ih =>
      have he := hframe _ cell.pointer_width (cell.ne_fresh hf)
      exact .cons ⟨cell.pointer_width, cell.head_width, cell.tail_width, cell.not_nil,
        (he 0).trans cell.tag, fun i ↦ (he _).trans (cell.head_bits i),
        fun i ↦ (he _).trans (cell.tail_bits i)⟩ ih

/-- Semantic sequential bit writes; no whole-word operation is charged or postulated. -/
def writeBits : Memory → Address → ℕ → List Bool → Memory
  | mem, _, _, [] => mem
  | mem, p, start, b :: bs => writeBits (mem.write (slot p start) b) p (start + 1) bs

/-- A finite write to one pointer block leaves every disjoint equal-width block unchanged. -/
theorem writeBits_frame (mem : Memory) (p q : Address) (start : ℕ) (bits : List Bool)
    (hlen : q.length = p.length) (hne : q ≠ p) (i : ℕ) :
    (writeBits mem p start bits).lookup (slot q i) = mem.lookup (slot q i) := by
  induction bits generalizing mem start with
  | nil => rfl
  | cons b bs ih =>
      rw [writeBits, ih]
      simp only [Memory.lookup_write, if_neg (slot_ne hlen hne i start)]

/-- Earlier slots in the same block survive writes starting at a later index. -/
theorem writeBits_before (mem : Memory) (p : Address) (start : ℕ) (bits : List Bool)
    (i : ℕ) (hi : i < start) :
    (writeBits mem p start bits).lookup (slot p i) = mem.lookup (slot p i) := by
  induction bits generalizing mem start with
  | nil => rfl
  | cons b bs ih =>
      rw [writeBits, ih _ _ (by omega)]
      have hne : slot p i ≠ slot p start := fun h ↦ (by have := slot_injective p h; omega)
      simp only [Memory.lookup_write, if_neg hne]

/-- Every specified bit is observed at its actual slot after the sequential semantic writes. -/
theorem writeBits_hit (mem : Memory) (p : Address) (start : ℕ) (bits : List Bool)
    (i : ℕ) (hi : i < bits.length) :
    (writeBits mem p start bits).lookup (slot p (start + i)) = bits[i] := by
  induction bits generalizing mem start i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero, writeBits]
          rw [writeBits_before _ _ _ _ _ (by omega)]
          simp [Memory.lookup_write]
      | succ i =>
          simpa only [writeBits, Nat.add_assoc, Nat.add_comm 1 i, List.getElem_cons_succ] using
            ih (mem.write (slot p start) b) (start + 1) i (by simpa using hi)

/-- Semantic cell payload: live tag, scalar word, then the already materialized tail pointer. -/
def writeCell (mem : Memory) (p : Address) (head tail : List Bool) : Memory :=
  writeBits mem p 0 (true :: (head ++ tail))

/-- The semantic cell write establishes the representation from the bits it actually writes. -/
theorem writeCell_cell (mem : Memory) (w h : ℕ) (p head tail : List Bool)
    (hp : p.length = w) (hh : head.length = h) (ht : tail.length = w)
    (hnil : p ≠ nilPointer w) : Cell (writeCell mem p head tail) w h p head tail := by
  refine ⟨hp, hh, ht, hnil, ?_, ?_, ?_⟩
  · simpa [writeCell] using
      writeBits_hit mem p 0 (true :: (head ++ tail)) 0 (by simp)
  · intro i
    have hb := writeBits_hit mem p 0 (true :: (head ++ tail)) (1 + i.val) (by simp; omega)
    simpa only [writeCell, Nat.zero_add, Nat.add_comm 1 i.val, List.getElem_cons_succ,
      List.getElem_append_left (by omega : i.val < head.length)] using hb
  · intro i
    have hb := writeBits_hit mem p 0 (true :: (head ++ tail)) ((h + i.val) + 1) (by simp; omega)
    simp only [Nat.zero_add, List.getElem_cons_succ,
      List.getElem_append_right (by omega : head.length ≤ h + i.val),
      hh, Nat.add_sub_cancel_left] at hb
    simpa only [writeCell, show 1 + h + i.val = (h + i.val) + 1 by omega] using hb

/-- Every old list remains represented in the same memory returned by a fresh cell write. -/
theorem RepList.writeCell {mem : Memory} {w h p xs fresh head tail}
    (hr : RepList mem w h p xs) (hf : Fresh mem fresh) (hw : fresh.length = w) :
    RepList (writeCell mem fresh head tail) w h p xs := by
  apply hr.frame_fresh hf
  intro q hq hne i
  exact writeBits_frame mem fresh q 0 _ (hq.trans hw.symm) hne i

/-- Fresh cons allocation retains the old tail in the very same resulting memory. -/
theorem cons_allocation {mem : Memory} {w h p head tail xs}
    (hr : RepList mem w h tail xs) (hf : Fresh mem p) (hp : p.length = w)
    (hh : head.length = h) (hnil : p ≠ nilPointer w) :
    RepList (writeCell mem p head tail) w h p (head :: xs) ∧
      RepList (writeCell mem p head tail) w h tail xs := by
  have ht := hr.writeCell hf hp (head := head) (tail := tail)
  exact ⟨.cons (writeCell_cell mem w h p head tail hp hh hr.pointer_width hnil) ht, ht⟩

end Computation.SharedListHeap
