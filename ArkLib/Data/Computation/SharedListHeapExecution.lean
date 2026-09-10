/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListHeap
public import ArkLib.Data.Computation.BitMemoryBlock

/-!
# Literal shared-list cell writes

The supplied pointer and complete payload are already materialized local bit tapes. A payload
layout equation describes these existing bits; this module does not charge for or execute their
construction, concatenation, scalar encoding, or fresh-pointer selection. The literal block
controller then writes every bit through the addressed-bit access and reset machine.

The same final configuration carries the new represented cons cell, its old tail, all other old
represented lists, and unchanged observations on every disjoint equal-width pointer block.
The exact transition count is the block controller's count, not native Lean time. No read/lookup
controller, allocator, or full decoder bit-complexity claim is asserted here.
-/

@[expose] public section

namespace Computation.SharedListHeapExecution

open AddressedBits (Address Memory)
open SharedListHeap (Cell RepList Fresh nilPointer writeBits writeCell)

/-- The literal writer's semantic result is the same forward finite-write specification. -/
theorem store_eq_writeBits (mem : Memory) (p : Address) (start : ℕ) (bits : List Bool) :
    BitMemoryBlock.store mem p (List.replicate start true) bits = writeBits mem p start bits := by
  induction bits generalizing mem start with
  | nil => rfl
  | cons b bs ih =>
      simpa only [BitMemoryBlock.store, writeBits, List.replicate_succ,
        BitMemoryBlock.slot, SharedListHeap.slot] using
        ih (mem.write (SharedListHeap.slot p start) b) (start + 1)

/-- An already materialized cell payload executes to the actual semantically written memory.
The equation is a caller's input-layout contract, not a free concatenation instruction. -/
theorem writeCell_trace (mem : Memory) (p head tail payload : List Bool)
    (hpayload : payload = true :: (head ++ tail)) :
    BitMemoryBlock.Trace (BitMemoryBlock.steps p.length 0 payload.length)
      ⟨mem, .next p [] payload⟩
      ⟨writeCell mem p head tail, .done p (List.replicate payload.length true)⟩ := by
  have he : BitMemoryBlock.store mem p [] payload = writeCell mem p head tail := by
    have hs := store_eq_writeBits mem p 0 payload
    simpa only [List.replicate_zero, hpayload, writeCell] using hs
  simpa only [List.length_nil, List.append_nil, he] using
    BitMemoryBlock.store_trace mem p [] payload

/-- Physical payload width includes the tag, the head word and the tail pointer. -/
theorem payload_length {w h : ℕ} {head tail payload : List Bool}
    (hh : head.length = h) (ht : tail.length = w)
    (hpayload : payload = true :: (head ++ tail)) : payload.length = 1 + h + w := by
  simp only [hpayload, List.length_cons, List.length_append, hh, ht]
  omega

/-- The literal write of supplied bits allocates a represented cons at a supplied fresh pointer.
All conclusions refer to the final configuration of the same complete controller execution.
Payload construction and pointer selection precede this trace and are not priced by it. -/
theorem cons_allocation_execution {mem : Memory} {w h : ℕ} {p head tail : List Bool}
    {xs : List (List Bool)} (payload : List Bool)
    (hr : RepList mem w h tail xs) (hf : Fresh mem p) (hp : p.length = w)
    (hh : head.length = h) (hnil : p ≠ nilPointer w)
    (hpayload : payload = true :: (head ++ tail)) :
    ∃ final : BitMemoryBlock.Configuration,
      BitMemoryBlock.Trace (BitMemoryBlock.steps w 0 (1 + h + w))
        ⟨mem, .next p [] payload⟩ final ∧
      BitMemoryBlock.runFuel (BitMemoryBlock.steps w 0 (1 + h + w))
        ⟨mem, .next p [] payload⟩ = final ∧
      final.control = .done p (List.replicate (1 + h + w) true) ∧
      Cell final.memory w h p head tail ∧
      RepList final.memory w h p (head :: xs) ∧ RepList final.memory w h tail xs ∧
      (∀ old ys, RepList mem w h old ys → RepList final.memory w h old ys) ∧
      (∀ other, other.length = w → other ≠ p → ∀ i,
        final.memory.lookup (SharedListHeap.slot other i) =
          mem.lookup (SharedListHeap.slot other i)) := by
  have hlen := payload_length hh hr.pointer_width hpayload
  have ht := writeCell_trace mem p head tail payload hpayload
  rw [hp, hlen] at ht
  have halloc := SharedListHeap.cons_allocation hr hf hp hh hnil
  refine ⟨⟨writeCell mem p head tail, .done p (List.replicate (1 + h + w) true)⟩,
    ht, ht.runFuel_eq, rfl, ?_, halloc.1, halloc.2, ?_, ?_⟩
  · exact SharedListHeap.writeCell_cell mem w h p head tail hp hh hr.pointer_width hnil
  · intro old ys hold
    exact hold.writeCell hf hp
  · intro other hw hne i
    exact SharedListHeap.writeBits_frame mem p other 0 _ (hw.trans hp.symm) hne i

end Computation.SharedListHeapExecution
