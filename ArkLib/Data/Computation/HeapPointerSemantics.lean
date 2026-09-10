/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.HeapPointerMachine
public import ArkLib.Data.Computation.BinaryWordSemantics
public import ArkLib.Data.Computation.SharedListCellMachine
public import Mathlib.Tactic.Linarith

/-!
# Fixed-width pointer labels and bump freshness

Little-endian natural values label fixed-width pointer codewords injectively. They are not the
architectural RAM address: the literal block controller still constructs its address from the
actual prefix bits and unary slot suffix. No conversion or address enumeration is executed here.

The heap invariant says that every codeword at or above the bump label has a false live tag.
Increment has explicit overflow and preserves width. A write at the current pointer preserves the
invariant at its successful successor, including when the cell is written by the actual writer.
Pointer increment and cell writing have separate traces here; no combined allocator handoff or
allocation cost certificate is assumed. Nil is reserved independently of overflow behavior.
-/

@[expose] public section

namespace Computation.HeapPointerSemantics

open AddressedBits (Memory Address)
open BinaryWordMachine (value bitValue)
open HeapPointerMachine (increment)
open SharedListHeap (Fresh RepList nilPointer writeCell)

/-- Equal-width codewords with equal little-endian labels have identical physical bits. -/
theorem value_injective {p q : List Bool} (hlen : p.length = q.length) (hv : value p = value q) :
    p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all
  | cons b bs ih =>
      cases q with
      | nil => simp at hlen
      | cons c cs =>
          have hlen' : bs.length = cs.length := by simpa using hlen
          have he : bitValue b + 2 * value bs = bitValue c + 2 * value cs := hv
          have hbc : b = c := by
            cases b <;> cases c <;> simp [bitValue] at he <;> first | rfl | omega
          subst c
          exact congrArg (List.cons b) (ih hlen' (by omega))

/-- The reserved all-zero pointer has label zero at every width. -/
theorem nil_value (w : ℕ) : value (nilPointer w) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simpa [nilPointer, List.replicate_succ, value, bitValue] using ih

/-- Label zero denotes exactly the reserved nil codeword at the fixed width. -/
theorem value_zero_iff {p : List Bool} {w : ℕ} (hp : p.length = w) :
    value p = 0 ↔ p = nilPointer w := by
  constructor
  · intro hv
    exact value_injective (by simpa [nilPointer] using hp) (hv.trans (nil_value w).symm)
  · intro he
    rw [he, nil_value]

/-- The exact arithmetic equation accounts for carry out without changing physical width. -/
theorem increment_value (p : List Bool) (carry : Bool) :
    value p + bitValue carry = value (increment p carry).1 +
      2 ^ p.length * bitValue (increment p carry).2 := by
  induction p generalizing carry with
  | nil => simp [increment, value]
  | cons b bs ih =>
      have hc : bitValue (b != carry) + 2 * bitValue (b && carry) =
          bitValue b + bitValue carry := by cases b <;> cases carry <;> decide
      have ht := ih (b && carry)
      simp only [increment, value, List.length_cons, Nat.pow_succ]
      nlinarith

/-- A successful increment strictly advances the label by one. -/
theorem increment_success (p : List Bool) (h : (increment p true).2 = false) :
    value (increment p true).1 = value p + 1 := by
  have hv := increment_value p true
  simp only [h, bitValue, if_true, Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at hv
  exact hv.symm

/-- Overflow occurs precisely when the increment reaches the excluded upper endpoint. -/
theorem overflow_iff (p : List Bool) :
    (increment p true).2 = true ↔ value p + 1 = 2 ^ p.length := by
  have hv := increment_value p true
  have hi := BinaryWordMachine.value_lt_width p
  have ho := BinaryWordMachine.value_lt_width (increment p true).1
  rw [HeapPointerMachine.increment_length] at ho
  cases he : (increment p true).2 <;> simp [he, bitValue] at hv
  all_goals (simp; omega)

/-- Overflow wraps to the reserved nil bit word and must not be treated as a fresh successor. -/
theorem increment_overflow_nil (p : List Bool) (h : (increment p true).2 = true) :
    (increment p true).1 = nilPointer p.length := by
  have hv := increment_value p true
  have hb := (overflow_iff p).mp h
  simp [h, bitValue] at hv
  apply (value_zero_iff (HeapPointerMachine.increment_length p true)).mp
  omega

/-- Every successful successor is non-nil, even if incrementing the reserved zero word. -/
theorem increment_not_nil (p : List Bool) (h : (increment p true).2 = false) :
    (increment p true).1 ≠ nilPointer p.length := by
  intro he
  have hv := increment_success p h
  rw [he, nil_value] at hv
  omega

/-- The next-pointer operation returns these exact fixed-width bits in the unchanged RAM. -/
theorem increment_execution (mem : Memory) (p : List Bool) :
    HeapPointerMachine.ramRunFuel (3 * p.length + 3) (mem, .scan p [] [] true) =
      (mem, .done p (increment p true).1 (increment p true).2) ∧
      (increment p true).1.length = p.length ∧
      ((increment p true).2 = false → value (increment p true).1 = value p + 1) ∧
      ((increment p true).2 = true ↔ value p + 1 = 2 ^ p.length) := by
  refine ⟨?_, HeapPointerMachine.increment_length p true, increment_success p, overflow_iff p⟩
  rw [HeapPointerMachine.ramRunFuel_eq, HeapPointerMachine.increment_runFuel]

/-- Every fixed-width block at or above the bump label has an actual false live tag. -/
def AboveFree (mem : Memory) (w : ℕ) (current : Address) : Prop :=
  ∀ p : Address, p.length = w → value current ≤ value p → Fresh mem p

/-- Empty physical memory satisfies the invariant at any proposed starting label. -/
theorem aboveFree_empty (w : ℕ) (current : Address) : AboveFree .empty w current := by
  intro p _hp _hvalue
  change Memory.empty.lookup (SharedListHeap.slot p 0) = false
  simp [Memory.lookup]

/-- The current fixed-width bump pointer is actually fresh under the heap invariant. -/
theorem AboveFree.current {mem w current} (hf : AboveFree mem w current)
    (hw : current.length = w) : Fresh mem current := hf current hw le_rfl

/-- A current-cell write preserves all blocks at or above the successfully incremented label. -/
theorem AboveFree.writeCell {mem w current} (hf : AboveFree mem w current)
    (hw : current.length = w) (hnext : (increment current true).2 = false)
    (head tail : List Bool) :
    AboveFree (SharedListHeap.writeCell mem current head tail) w (increment current true).1 := by
  intro p hp hv
  have hvalue := increment_success current hnext
  have hne : p ≠ current := by intro he; rw [he] at hv; omega
  have hold := hf p hp (by omega)
  change (SharedListHeap.writeCell mem current head tail).lookup (SharedListHeap.slot p 0) = false
  rw [SharedListHeap.writeCell,
    SharedListHeap.writeBits_frame mem current p 0 _ (hp.trans hw.symm) hne 0]
  exact hold

/-- The next codeword has a false tag after writing the old bump pointer. -/
theorem AboveFree.next_fresh {mem w current} (hf : AboveFree mem w current)
    (hw : current.length = w) (hnext : (increment current true).2 = false)
    (head tail : List Bool) :
    Fresh (SharedListHeap.writeCell mem current head tail) (increment current true).1 :=
  (hf.writeCell hw hnext head tail).current ((HeapPointerMachine.increment_length _ _).trans hw)

/-- The invariant advances on the actual cell writer's final RAM, with its exact complete trace.
The next pointer here is supplied by the separately verified increment; no combined allocator
handoff is asserted by this theorem. -/
theorem write_execution {mem : Memory} {w h : ℕ} {current head tail : List Bool}
    {xs : List (List Bool)} (hf : AboveFree mem w current) (hw : current.length = w)
    (hnext : (increment current true).2 = false) (hnil : current ≠ nilPointer w)
    (hh : head.length = h) (hr : RepList mem w h tail xs) :
    ∃ final : SharedListCellMachine.Configuration,
      SharedListCellMachine.Trace (SharedListCellMachine.steps w h)
        ⟨mem, .building current (.copyTail head tail [] [])⟩ final ∧
      SharedListCellMachine.runFuel (SharedListCellMachine.steps w h)
        ⟨mem, .building current (.copyTail head tail [] [])⟩ = final ∧
      AboveFree final.memory w (increment current true).1 ∧
      RepList final.memory w h current (head :: xs) ∧ RepList final.memory w h tail xs := by
  have ht := SharedListCellMachine.write_trace mem w h current head tail hw hh hr.pointer_width
  have ha := SharedListHeap.cons_allocation hr (hf.current hw) hw hh hnil
  exact ⟨_, ht, ht.runFuel_eq, hf.writeCell hw hnext head tail, ha.1, ha.2⟩

end Computation.HeapPointerSemantics
