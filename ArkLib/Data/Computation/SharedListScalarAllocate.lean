/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListAllocator
public import ArkLib.Data.Computation.ScalarWordPadding

/-!
# Literal reduced-scalar allocation into a shared list

The same program constructs a width tape from the supplied modulus, pads the scalar bit by bit,
and hands its physical output to the actual allocator. Modulus tape twelve is retained; padding
output tape nine becomes the allocator's head input at that same position. The current pointer
and tail remain on tapes zero and ten. All fourteen tape positions are fixed throughout.

A canonical reduced scalar fits the modulus width by the existing binary-word bound. Numeric
interpretation is proof-side only. Initial words and the heap invariant remain caller contracts.
This lowers scalar cons allocation, not arithmetic or a complete decoder. Already fixed-width
operands can use `SharedListAllocator` directly without executing this padding entry again.
-/

@[expose] public section

namespace Computation.SharedListScalarAllocate

open AddressedBits (Memory Address)
open BinaryWordMachine (Word value Canonical)
open HeapPointerMachine (increment)
open HeapPointerSemantics (AboveFree)
open SharedListHeap (Cell RepList Fresh nilPointer writeCell)

/-- Finite phase control retains pointer/tail during padding and modulus during allocation. -/
inductive Control where
  | padding (current tail : Address) (child : ScalarWordPadding.Control)
  | allocating (modulus : Word) (child : SharedListAllocator.Control)
  deriving DecidableEq, Repr

/-- Both children operate on the same unique RAM. -/
structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- Actual child transitions and one tape-preserving padding-to-allocation handoff. -/
def step : Configuration → Option Configuration
  | ⟨mem, .padding current tail child⟩ =>
      match ScalarWordPadding.step child with
      | some next => some ⟨mem, .padding current tail next⟩
      | none => match child with
          | .padding modulus (.done out) =>
              some ⟨mem, .allocating modulus (.incrementing out tail (.scan current [] [] true))⟩
          | _ => none
  | ⟨mem, .allocating modulus child⟩ =>
      match SharedListAllocator.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .allocating modulus next.control⟩
      | none => none

/-- Counts of the actual combined scalar-allocation successors. -/
inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- External fuel observer; widths and scalar values are not runtime numeric registers. -/
def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

/-- Composition retains the exact intermediate memory and physical words. -/
theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Exact fuel returns the same final configuration as the literal trace. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- Padding retains both pointer words and all RAM bits. -/
theorem lift_padding (mem : Memory) (current tail : Address) {n : ℕ}
    {s t : ScalarWordPadding.Control} (h : ScalarWordPadding.Trace n s t) :
    Trace n ⟨mem, .padding current tail s⟩ ⟨mem, .padding current tail t⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- The allocator's actual memory updates are retained together with the modulus word. -/
theorem lift_allocator (modulus : Word) {n : ℕ} {s t : SharedListAllocator.Configuration}
    (h : SharedListAllocator.Trace n s t) :
    Trace n ⟨s.memory, .allocating modulus s.control⟩
      ⟨t.memory, .allocating modulus t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Width construction, padding, handoff and the full actual allocation cost. -/
def steps (w h : ℕ) : ℕ := 4 * h + 8 + SharedListAllocator.steps w h

/-- Padding and overflow handling are executed before stopping without any heap write. -/
def overflowSteps (w h : ℕ) : ℕ := 4 * h + 3 * w + 12

/-- The physically padded scalar is the very head passed to the actual successful allocator. -/
theorem success_trace (mem : Memory) (w : ℕ) (current tail modulus word : Word)
    (hw : current.length = w) (ht : tail.length = w) (hfit : word.length ≤ modulus.length)
    (hnext : (increment current true).2 = false) :
    ∃ out : Word, out.length = modulus.length ∧ value out = value word ∧
      Trace (steps w modulus.length)
        ⟨mem, .padding current tail (.shaping word (.shapeStart modulus))⟩
        ⟨writeCell mem current out tail, .allocating modulus (.writing (increment current true).1
          (.writing out tail (.done current (List.replicate (1 + modulus.length + w) true))))⟩ := by
  obtain ⟨out, hp, _hr, hlen, hv⟩ := ScalarWordPadding.padding_correct modulus word hfit
  have hp' := lift_padding mem current tail hp
  have hh : Trace 1 ⟨mem, .padding current tail (.padding modulus (.done out))⟩
      ⟨mem, .allocating modulus (.incrementing out tail (.scan current [] [] true))⟩ :=
    .cons rfl (.nil _)
  have ha := lift_allocator modulus
    (SharedListAllocator.success_trace mem w modulus.length current out tail hw hlen ht hnext)
  refine ⟨out, hlen, hv, ?_⟩
  convert (hp'.append hh).append ha using 1
  simp only [steps]

/-- The full reduced-scalar allocation retains its exact value and advances the heap invariant.
The modulus, stored head, returned pointers and memory all belong to this same execution. -/
theorem success_execution {mem : Memory} {w : ℕ} {current tail modulus word : Word}
    {xs : List Word} (hf : AboveFree mem w current) (hw : current.length = w)
    (hnil : current ≠ nilPointer w) (hr : RepList mem w modulus.length tail xs)
    (hc : Canonical word) (hvalue : value word < value modulus)
    (hnext : (increment current true).2 = false) :
    ∃ out : Word, ∃ final : Configuration,
      Trace (steps w modulus.length)
        ⟨mem, .padding current tail (.shaping word (.shapeStart modulus))⟩ final ∧
      runFuel (steps w modulus.length)
        ⟨mem, .padding current tail (.shaping word (.shapeStart modulus))⟩ = final ∧
      final.control = .allocating modulus (.writing (increment current true).1
        (.writing out tail (.done current (List.replicate (1 + modulus.length + w) true)))) ∧
      out.length = modulus.length ∧ value out = value word ∧ value out < value modulus ∧
      Cell final.memory w modulus.length current out tail ∧
      RepList final.memory w modulus.length current (out :: xs) ∧
      (∀ old ys, RepList mem w modulus.length old ys →
        RepList final.memory w modulus.length old ys) ∧
      AboveFree final.memory w (increment current true).1 ∧
      Fresh final.memory (increment current true).1 := by
  obtain ⟨out, hlen, hv, ht⟩ := success_trace mem w current tail modulus word hw hr.pointer_width
    (hc.width_le_of_value_lt word modulus hvalue) hnext
  have ha := SharedListHeap.cons_allocation hr (hf.current hw) hw hlen hnil
  refine ⟨out, _, ht, ht.runFuel_eq, rfl, hlen, hv, hv ▸ hvalue, ?_, ha.1, ?_,
    hf.writeCell hw hnext out tail, hf.next_fresh hw hnext out tail⟩
  · exact SharedListHeap.writeCell_cell mem w modulus.length current out tail
      hw hlen hr.pointer_width hnil
  · intro old ys hold
    exact hold.writeCell (hf.current hw) hw

/-- The actual overflow branch retains RAM, modulus and padded scalar and performs no allocation. -/
theorem overflow_execution (mem : Memory) (w : ℕ) (current tail modulus word : Word)
    (hw : current.length = w) (hfit : word.length ≤ modulus.length)
    (hov : (increment current true).2 = true) :
    ∃ out : Word,
      Trace (overflowSteps w modulus.length)
        ⟨mem, .padding current tail (.shaping word (.shapeStart modulus))⟩
        ⟨mem, .allocating modulus (.overflow current (nilPointer w) out tail)⟩ ∧
      runFuel (overflowSteps w modulus.length)
        ⟨mem, .padding current tail (.shaping word (.shapeStart modulus))⟩ =
        ⟨mem, .allocating modulus (.overflow current (nilPointer w) out tail)⟩ ∧
      out.length = modulus.length ∧ value out = value word := by
  obtain ⟨out, hp, _hr, hlen, hv⟩ := ScalarWordPadding.padding_correct modulus word hfit
  have hp' := lift_padding mem current tail hp
  have hh : Trace 1 ⟨mem, .padding current tail (.padding modulus (.done out))⟩
      ⟨mem, .allocating modulus (.incrementing out tail (.scan current [] [] true))⟩ :=
    .cons rfl (.nil _)
  have ha := lift_allocator modulus
    (SharedListAllocator.overflow_trace mem w current out tail hw hov)
  have he : Trace (overflowSteps w modulus.length)
      ⟨mem, .padding current tail (.shaping word (.shapeStart modulus))⟩
      ⟨mem, .allocating modulus (.overflow current (nilPointer w) out tail)⟩ := by
    convert (hp'.append hh).append ha using 1
    simp only [overflowSteps]
    omega
  exact ⟨out, he, he.runFuel_eq, hlen, hv⟩

/-- Permanent tape positions: modulus twelve, padded head nine, current zero, tail ten. -/
def physicalTapes : Control → Fin 14 → Word
  | .padding current tail child =>
      let t := ScalarWordPadding.tapes child
      ![current, t 1, t 2, t 3, [], [], [], [], [], t 4, tail, [], t 0, t 5]
  | .allocating modulus child =>
      let t := SharedListAllocator.physicalTapes child
      ![t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7, t 8, t 9, t 10, t 11, modulus, []]

/-- The physical padded output becomes the allocator head without moving any tape content. -/
theorem handoff_tapes (current tail modulus out : Word) :
    physicalTapes (.padding current tail (.padding modulus (.done out))) =
      physicalTapes (.allocating modulus (.incrementing out tail (.scan current [] [] true))) := rfl

private theorem bank_fourteen
    {a b c d e f g h i j k l m n a' b' c' d' e' f' g' h' i' j' k' l' m' n' : Word}
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

/-- All combined successors act locally on the same fixed fourteen bit tapes. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (physicalTapes s.control) (physicalTapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | padding current tail child =>
      cases hs : ScalarWordPadding.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := ScalarWordPadding.step_local hs
          exact bank_fourteen (.keep _) (hl 1) (hl 2) (hl 3) (.keep _) (.keep _) (.keep _)
            (.keep _) (.keep _) (hl 4) (.keep _) (.keep _) (hl 0) (hl 5)
      | none =>
          simp only [step, hs] at h
          cases child with
          | shaping word inner => cases h
          | padding modulus inner =>
              cases inner <;> cases h
              rw [handoff_tapes]
              intro i
              exact .keep _
  | allocating modulus child =>
      cases hs : SharedListAllocator.step ⟨mem, child⟩ with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := SharedListAllocator.step_local hs
          exact bank_fourteen (hl 0) (hl 1) (hl 2) (hl 3) (hl 4) (hl 5) (hl 6)
            (hl 7) (hl 8) (hl 9) (hl 10) (hl 11) (.keep _) (.keep _)
      | none => simp only [step, hs] at h; contradiction

end Computation.SharedListScalarAllocate
