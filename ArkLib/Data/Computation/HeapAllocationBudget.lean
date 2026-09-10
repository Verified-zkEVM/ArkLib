/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListAllocator

/-!
# Remaining capacity for actual shared-list allocations

A fixed-width bump pointer reserves one nonzero successor after the last permitted allocation.
The invariant below derives the allocator's no-overflow premise from an explicit remaining
allocation budget. Each successful execution preserves every old represented list and decreases
that budget by one. It does not assert that a whole decoder stays within a particular budget;
that requires the decoder's separate lifetime-allocation bound and input initialization proof.
-/

@[expose] public section

namespace Computation.HeapAllocationBudget

open AddressedBits (Memory Address)
open BinaryWordMachine (value)
open HeapPointerMachine (increment)
open HeapPointerSemantics (AboveFree)
open SharedListHeap (RepList nilPointer)

/-- Freshness and numeric capacity of an already materialized fixed-width bump pointer. -/
structure Available (mem : Memory) (w remaining : ℕ) (current : Address) : Prop where
  width : current.length = w
  nonzero : current ≠ nilPointer w
  freshAbove : AboveFree mem w current
  capacity : value current + remaining < 2 ^ w

/-- Positive remaining capacity rules out the actual increment controller's overflow flag. -/
theorem Available.no_overflow {mem : Memory} {w remaining : ℕ} {current : Address}
    (h : Available mem w (remaining + 1) current) :
    (increment current true).2 = false := by
  have hc := h.capacity
  have hw := h.width
  cases he : (increment current true).2 with
  | false => rfl
  | true =>
      have ho := (HeapPointerSemantics.overflow_iff current).mp he
      rw [hw] at ho
      omega

/-- Restrict a remaining budget without changing memory, pointer bits, or freshness. -/
theorem Available.mono {mem : Memory} {w a b : ℕ} {current : Address}
    (h : Available mem w a current) (hb : b ≤ a) : Available mem w b current := by
  refine ⟨h.width, h.nonzero, h.freshAbove, ?_⟩
  exact (Nat.add_le_add_left hb _).trans_lt h.capacity

/-- Empty RAM has the invariant for any supplied nonzero pointer with sufficient capacity.
This theorem does not fabricate a runtime pointer or claim its initialization has zero cost. -/
theorem available_empty {w remaining : ℕ} {current : Address}
    (hw : current.length = w) (hn : current ≠ nilPointer w)
    (hc : value current + remaining < 2 ^ w) : Available .empty w remaining current :=
  ⟨hw, hn, HeapPointerSemantics.aboveFree_empty w current, hc⟩

/-- One actual allocator run consumes one unit of reserved capacity, returns the new list,
and preserves all old lists on the very same final RAM. The count includes increment and write. -/
theorem allocate_execution {mem : Memory} {w h remaining : ℕ}
    {current head tail : Address} {xs : List (List Bool)}
    (hb : Available mem w (remaining + 1) current) (hh : head.length = h)
    (hr : RepList mem w h tail xs) :
    ∃ final : SharedListAllocator.Configuration,
      SharedListAllocator.Trace (SharedListAllocator.steps w h)
        ⟨mem, .incrementing head tail (.scan current [] [] true)⟩ final ∧
      SharedListAllocator.runFuel (SharedListAllocator.steps w h)
        ⟨mem, .incrementing head tail (.scan current [] [] true)⟩ = final ∧
      final.control = .writing (increment current true).1
        (.writing head tail (.done current (List.replicate (1 + h + w) true))) ∧
      RepList final.memory w h current (head :: xs) ∧
      (∀ old ys, RepList mem w h old ys → RepList final.memory w h old ys) ∧
      Available final.memory w remaining (increment current true).1 := by
  obtain ⟨final, ht, hf, ho, _hcell, hnew, _htail, hframe, habove, _hfresh,
    hwidth, hnonzero, hvalue⟩ :=
    SharedListAllocator.success_execution hb.freshAbove hb.width hb.nonzero hh hr hb.no_overflow
  refine ⟨final, ht, hf, ho, hnew, hframe, hwidth, hnonzero, habove, ?_⟩
  rw [hvalue]
  have hc := hb.capacity
  omega

end Computation.HeapAllocationBudget
