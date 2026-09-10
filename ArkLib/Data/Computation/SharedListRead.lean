/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BitMemoryRead
public import ArkLib.Data.Computation.SharedListHeap

/-!
# Literal reads of represented shared-list cells

The cell representation is defined by memory observations, not by successful execution.
Here an actual block read recovers exactly those tag/head/tail bits, preserving the entire
memory and hence every shared tail. The length tape is an explicit already-materialized input.
Separating the returned payload into scalar/pointer registers is not asserted as a free step.
-/

@[expose] public section

namespace Computation.SharedListRead

open AddressedBits (Memory Address)
open SharedListHeap (Cell RepList)

/-- A cell's representation specifies every bit of the physically returned payload. -/
theorem load_cell {mem : Memory} {w h : ℕ} {p head tail : List Bool}
    (hc : Cell mem w h p head tail) (shape : List Bool)
    (hs : shape.length = 1 + h + w) :
    BitMemoryRead.load mem p [] shape = true :: (head ++ tail) := by
  apply List.ext_getElem
  · simp only [BitMemoryRead.load_length, hs, List.length_cons, List.length_append,
      hc.head_width, hc.tail_width]
    omega
  · intro i hi hi'
    rw [BitMemoryRead.load_getElem _ _ _ _ i (by
      rw [BitMemoryRead.load_length] at hi; exact hi)]
    simp only [List.append_nil, BitMemoryBlock.slot]
    change mem.lookup (SharedListHeap.slot p i) = _
    cases i with
    | zero => exact hc.tag
    | succ i =>
        simp only [List.getElem_cons_succ]
        by_cases hih : i < h
        · have hh : i < head.length := by rw [hc.head_width]; exact hih
          rw [List.getElem_append_left hh]
          simpa only [Nat.add_comm] using hc.head_bits ⟨i, hih⟩
        · have hiw : i - h < w := by
            rw [BitMemoryRead.load_length, hs] at hi
            omega
          have hh : head.length ≤ i := by rw [hc.head_width]; omega
          rw [List.getElem_append_right hh]
          have ht := hc.tail_bits ⟨i - h, hiw⟩
          simpa only [hc.head_width, show 1 + h + (i - h) = i + 1 by omega] using ht

/-- The same literal read trace returns a represented cell's payload and preserves all RAM. -/
theorem cell_read_execution {mem : Memory} {w h : ℕ} {p head tail : List Bool}
    (hc : Cell mem w h p head tail) (shape : List Bool)
    (hs : shape.length = 1 + h + w) :
    ∃ final : BitMemoryRead.Configuration,
      BitMemoryRead.Trace (BitMemoryRead.steps w 0 (1 + h + w))
        ⟨mem, .next p [] shape []⟩ final ∧
      BitMemoryRead.runFuel (BitMemoryRead.steps w 0 (1 + h + w))
        ⟨mem, .next p [] shape []⟩ = final ∧
      final.memory = mem ∧
      final.control = .done p (List.replicate (1 + h + w) true) (true :: (head ++ tail)) ∧
      (∀ old ys, RepList mem w h old ys → RepList final.memory w h old ys) := by
  have ht := BitMemoryRead.load_trace mem p [] shape
  rw [hc.pointer_width, hs, load_cell hc shape hs] at ht
  simp only [List.length_nil, List.append_nil] at ht
  exact ⟨_, ht, ht.runFuel_eq, rfl, rfl, fun _ _ hr ↦ hr⟩

end Computation.SharedListRead
