/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AddressedBitsSemantics
public import ArkLib.Data.Computation.BitLocalActions
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Bit-by-bit writes to prefix-addressed memory blocks

A block bit has address `base ++ replicate i true ++ [false]`. The base is a binary pointer,
not a unary allocation counter. Only the within-word bit index is unary. Copying and restoring
the pointer and index is explicit, and the access/reset is the actual addressed-bit controller.
Input pointer and payload bits are already materialized; allocation and serialization are not
asserted here. This is a fixed bit-RAM controller, not a host running-time theorem.
-/

@[expose] public section

namespace Computation.BitMemoryBlock

open AddressedBits (Memory Address)

/-- Semantic slot address; address construction in the controller is bit-by-bit. -/
def slot (base : Address) (index : List Bool) : Address := base ++ index ++ [false]

/-- Fixed finite control together with finitely many local bit tapes. -/
inductive Control where
  | next (base index remaining : List Bool)
  | copyBase (bit : Bool) (index remaining source saved bus : List Bool)
  | restoreBase (bit : Bool) (index remaining source base bus : List Bool)
  | copyIndex (bit : Bool) (base remaining source saved bus : List Bool)
  | restoreIndex (bit : Bool) (base remaining source index bus : List Bool)
  | writing (base index remaining : List Bool) (child : AddressedBits.Control)
  | done (base index : List Bool)
  | failed (base index remaining : List Bool) (child : AddressedBits.Control)
  deriving DecidableEq, Repr

/-- The unique memory is the actual memory passed through the access controller. -/
structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- Each transition performs only fixed local bit actions or an actual addressed-bit successor. -/
def step : Configuration → Option Configuration
  | ⟨mem, .next base index []⟩ => some ⟨mem, .done base index⟩
  | ⟨mem, .next base index (b :: bs)⟩ =>
      some ⟨mem, .copyBase b index bs base [] [true]⟩
  | ⟨mem, .copyBase b index bs (x :: xs) saved bus⟩ =>
      some ⟨mem, .copyBase b index bs xs (x :: saved) (x :: bus)⟩
  | ⟨mem, .copyBase b index bs [] saved bus⟩ =>
      some ⟨mem, .restoreBase b index bs saved [] bus⟩
  | ⟨mem, .restoreBase b index bs (x :: xs) base bus⟩ =>
      some ⟨mem, .restoreBase b index bs xs (x :: base) bus⟩
  | ⟨mem, .restoreBase b index bs [] base bus⟩ =>
      some ⟨mem, .copyIndex b base bs index [] bus⟩
  | ⟨mem, .copyIndex b base bs (x :: xs) saved bus⟩ =>
      some ⟨mem, .copyIndex b base bs xs (x :: saved) (x :: bus)⟩
  | ⟨mem, .copyIndex b base bs [] saved bus⟩ =>
      some ⟨mem, .restoreIndex b base bs saved [] (false :: bus)⟩
  | ⟨mem, .restoreIndex b base bs (x :: xs) index bus⟩ =>
      some ⟨mem, .restoreIndex b base bs xs (x :: index) bus⟩
  | ⟨mem, .restoreIndex b base bs [] index bus⟩ =>
      some ⟨mem, .writing base index bs (.restore (.write b) bus [])⟩
  | ⟨mem, .writing base index bs child⟩ =>
      match AddressedBits.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .writing base index bs next.control⟩
      | none => match child with
          | .done (some _) => some ⟨mem, .next base (true :: index) bs⟩
          | _ => some ⟨mem, .failed base index bs child⟩
  | ⟨_, .done _ _⟩ | ⟨_, .failed _ _ _ _⟩ => none

/-- Actual bit-RAM transition count for this fixed controller. -/
inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- Fuel observes the literal transitions, without entering the machine state. -/
def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

/-- Concatenation preserves every transition and the intermediate memory. -/
theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Exact fuel returns the same final memory and control as the actual trace. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) :
    runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- The retained access child updates the unique memory of the parent execution. -/
theorem lift_access (base index remaining : List Bool) {n : ℕ}
    {s t : AddressedBits.Configuration} (h : AddressedBits.Trace n s t) :
    Trace n ⟨s.memory, .writing base index remaining s.control⟩
      ⟨t.memory, .writing base index remaining t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head tail ih =>
      exact .cons (by simp only [step, head]) ih

/-- Restore the saved unary bit index before executing the retained address bus. -/
theorem restoreIndex_trace (mem : Memory) (b : Bool)
    (base remaining source index bus : List Bool) :
    Trace (source.length + 1) ⟨mem, .restoreIndex b base remaining source index bus⟩
      ⟨mem, .writing base (source.reverse ++ index) remaining (.restore (.write b) bus [])⟩ := by
  induction source generalizing index with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: index))

/-- Copy every index bit onto both its saved tape and the reversed address bus. -/
theorem copyIndex_trace (mem : Memory) (b : Bool)
    (base remaining source saved bus : List Bool) :
    Trace (source.length + 1) ⟨mem, .copyIndex b base remaining source saved bus⟩
      ⟨mem, .restoreIndex b base remaining (source.reverse ++ saved) []
        (false :: (source.reverse ++ bus))⟩ := by
  induction source generalizing saved bus with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: saved) (x :: bus))

/-- Restore the original binary pointer without a whole-word copy operation. -/
theorem restoreBase_trace (mem : Memory) (b : Bool)
    (index remaining source base bus : List Bool) :
    Trace (source.length + 1) ⟨mem, .restoreBase b index remaining source base bus⟩
      ⟨mem, .copyIndex b (source.reverse ++ base) remaining index [] bus⟩ := by
  induction source generalizing base with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: base))

/-- Copy the binary pointer one bit at a time, also saving it for subsequent word bits. -/
theorem copyBase_trace (mem : Memory) (b : Bool)
    (index remaining source saved bus : List Bool) :
    Trace (source.length + 1) ⟨mem, .copyBase b index remaining source saved bus⟩
      ⟨mem, .restoreBase b index remaining (source.reverse ++ saved) []
        (source.reverse ++ bus)⟩ := by
  induction source generalizing saved bus with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: saved) (x :: bus))

/-- One stored bit includes pointer and index restoration, access, reset and loop return. -/
theorem write_bit_trace (mem : Memory) (base index remaining : List Bool) (b : Bool) :
    Trace (4 * base.length + 4 * index.length + 13)
      ⟨mem, .next base index (b :: remaining)⟩
      ⟨mem.write (slot base index) b, .next base (true :: index) remaining⟩ := by
  let bus := false :: (index.reverse ++ (base.reverse ++ [true]))
  have hb : bus.reverse = true :: slot base index := by
    simp [bus, slot, List.reverse_append, List.append_assoc]
  have hc := copyBase_trace mem b index remaining base [] [true]
  have hr := restoreBase_trace mem b index remaining base.reverse [] (base.reverse ++ [true])
  have hi := copyIndex_trace mem b base remaining index [] (base.reverse ++ [true])
  have hj := restoreIndex_trace mem b base remaining index.reverse [] bus
  simp only [List.append_nil] at hc hi
  simp only [List.reverse_reverse, List.append_nil] at hr hj
  have hrestore := AddressedBits.restore_trace mem (.write b) bus []
  rw [hb, List.append_nil] at hrestore
  have haccess := AddressedBits.access_trace mem (.write b) (slot base index)
  simp only [AddressedBits.effect] at haccess
  have hfinish : Trace 1
      ⟨mem.write (slot base index) b, .writing base index remaining (.done (some b))⟩
      ⟨mem.write (slot base index) b, .next base (true :: index) remaining⟩ :=
    .cons rfl (.nil _)
  have h := Trace.cons (show step ⟨mem, .next base index (b :: remaining)⟩ = _ from rfl)
    (((((hc.append hr).append hi).append hj).append
      (lift_access base index remaining (hrestore.append haccess))).append hfinish)
  convert h using 1
  simp only [bus, slot, List.length_cons, List.length_append, List.length_reverse,
    List.length_nil]
  omega

/-- Semantic word update, used only to specify the output of the literal bit controller. -/
def store : Memory → Address → List Bool → List Bool → Memory
  | mem, _, _, [] => mem
  | mem, base, index, b :: bs => store (mem.write (slot base index) b) base (true :: index) bs

/-- Exact transition count for a word of physical length L and an already materialized pointer.
Only the within-word index is unary; binary pointer length appears linearly. -/
def steps (B I L : ℕ) : ℕ := 2 * L ^ 2 + (4 * B + 4 * I + 11) * L + 1

/-- All word bits are actually written, with the same memory and explicit complete loop count. -/
theorem store_trace (mem : Memory) (base index bits : List Bool) :
    Trace (steps base.length index.length bits.length) ⟨mem, .next base index bits⟩
      ⟨store mem base index bits, .done base (List.replicate bits.length true ++ index)⟩ := by
  induction bits generalizing mem index with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      have h := (write_bit_trace mem base index bs b).append
        (ih (mem.write (slot base index) b) (true :: index))
      convert h using 1
      · simp only [List.length_cons, steps]
        ring
      · simp only [store, List.length_cons, List.replicate_add, List.replicate_one,
          List.singleton_append, List.append_assoc]

/-- The fuel observer returns precisely the specified fully written memory and preserved pointer. -/
theorem store_runFuel (mem : Memory) (base index bits : List Bool) :
    runFuel (steps base.length index.length bits.length) ⟨mem, .next base index bits⟩ =
      ⟨store mem base index bits, .done base (List.replicate bits.length true ++ index)⟩ :=
  (store_trace mem base index bits).runFuel_eq

/-- A word write preserves every bit outside its exact addressed footprint. -/
theorem store_frame (mem : Memory) (base index bits : List Bool) (query : Address)
    (hq : ∀ j < bits.length, query ≠ slot base (List.replicate j true ++ index)) :
    (store mem base index bits).lookup query = mem.lookup query := by
  induction bits generalizing mem index with
  | nil => rfl
  | cons b bs ih =>
      have hzero := hq 0 (by simp)
      simp only [List.replicate_zero, List.nil_append] at hzero
      rw [store, ih]
      · simp only [Memory.lookup_write, if_neg hzero]
      · intro j hj
        simpa only [List.replicate_add, List.replicate_one,
          List.singleton_append, List.append_assoc] using hq (j + 1) (by simpa using hj)

/-- Every addressed slot of the returned memory contains the corresponding supplied word bit. -/
theorem store_lookup (mem : Memory) (base index bits : List Bool) (i : ℕ) (hi : i < bits.length) :
    (store mem base index bits).lookup (slot base (List.replicate i true ++ index)) = bits[i] := by
  induction bits generalizing mem index i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          simp only [List.replicate_zero, List.nil_append, List.getElem_cons_zero, store]
          rw [store_frame]
          · simp [Memory.lookup_write]
          · intro j _hj he
            have hlen := congrArg List.length he
            simp only [slot, List.length_append, List.length_cons, List.length_nil,
              List.length_replicate] at hlen
            omega
      | succ i =>
          have hi' : i < bs.length := by simpa using hi
          simpa only [store, List.getElem_cons_succ, List.replicate_add,
            List.replicate_one, List.singleton_append, List.append_assoc] using
            ih (mem.write (slot base index) b) (true :: index) i hi'

/-- Fixed-width unequal binary pointers address disjoint memory blocks. -/
theorem slot_ne_of_base_ne (base other index queryIndex : List Bool)
    (hw : base.length = other.length) (hne : other ≠ base) :
    slot other queryIndex ≠ slot base index := by
  intro he
  apply hne
  have h := congrArg (List.take base.length) he
  have hleft : (slot other queryIndex).take base.length = other := by
    rw [hw]
    simp only [slot, List.append_assoc, List.take_left]
  have hright : (slot base index).take base.length = base := by
    simp only [slot, List.append_assoc, List.take_left]
  exact hleft.symm.trans (h.trans hright)

/-- Writing a new fixed-width pointer block retains every bit of every other pointer block. -/
theorem store_other_base (mem : Memory) (base other index bits queryIndex : List Bool)
    (hw : base.length = other.length) (hne : other ≠ base) :
    (store mem base index bits).lookup (slot other queryIndex) =
      mem.lookup (slot other queryIndex) := by
  apply store_frame
  intro j _hj
  exact slot_ne_of_base_ne base other _ queryIndex hw hne

/-- Fixed physical tape assignment; the bank size does not depend on any input length.
Saved copies remain on the same physical tape through changes of control phase. -/
def physicalTapes : Control → Fin 9 → List Bool
  | .next base index remaining => ![base, [], index, [], remaining, [], [], [], []]
  | .copyBase _ index remaining source saved bus =>
      ![source, saved, index, [], remaining, bus, [], [], []]
  | .restoreBase _ index remaining source base bus =>
      ![base, source, index, [], remaining, bus, [], [], []]
  | .copyIndex _ base remaining source saved bus =>
      ![base, [], source, saved, remaining, bus, [], [], []]
  | .restoreIndex _ base remaining source index bus =>
      ![base, [], index, source, remaining, bus, [], [], []]
  | .writing base index remaining child | .failed base index remaining child =>
      let tapes := BitLocalActions.addressTapes child
      ![base, [], index, [], remaining, tapes.right, tapes.left, tapes.saved, tapes.output]
  | .done base index => ![base, [], index, [], [], [], [], [], []]

private theorem bank_nine {a b c d e f g h i a' b' c' d' e' f' g' h' i' : List Bool}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f')
    (hg : BitLocalActions.CellStep g g') (hh : BitLocalActions.CellStep h h')
    (hi : BitLocalActions.CellStep i i') :
    BitLocalActions.BankStep ![a, b, c, d, e, f, g, h, i]
      ![a', b', c', d', e', f', g', h', i'] := by
  intro j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf
  · exact hg
  · exact hh
  · exact hi

private theorem access_none (mem : Memory) (child : AddressedBits.Control)
    (h : AddressedBits.step ⟨mem, child⟩ = none) : ∃ result, child = .done result := by
  cases child with
  | start => simp [AddressedBits.step] at h
  | transfer op remaining bus => cases remaining <;> simp [AddressedBits.step] at h
  | restore op remaining bus => cases remaining <;> simp [AddressedBits.step] at h
  | access op bus =>
      cases op <;> cases bus with
      | nil => simp [AddressedBits.step] at h
      | cons b bs => cases b <;> simp [AddressedBits.step] at h
  | reset result bus => cases bus <;> simp [AddressedBits.step] at h
  | done result => exact ⟨result, rfl⟩

/-- Every actual successor uses at most one cell action on each of nine fixed bit tapes.
The only memory action remains the explicitly declared addressed-bit RAM access. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (physicalTapes s.control) (physicalTapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | next base index remaining =>
      cases remaining <;> cases h <;> apply bank_nine <;> constructor
  | copyBase b index remaining source saved bus =>
      cases source <;> cases h <;> apply bank_nine <;> constructor
  | restoreBase b index remaining source base bus =>
      cases source <;> cases h <;> apply bank_nine <;> constructor
  | copyIndex b base remaining source saved bus =>
      cases source <;> cases h <;> apply bank_nine <;> constructor
  | restoreIndex b base remaining source index bus =>
      cases source <;> cases h <;> apply bank_nine <;> constructor
  | writing base index remaining child =>
      cases hs : AddressedBits.step ⟨mem, child⟩ with
      | some u =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := BitLocalActions.address_step hs
          exact bank_nine (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
            hl.2.1 hl.1 hl.2.2.1 hl.2.2.2
      | none =>
          obtain ⟨result, rfl⟩ := access_none mem child hs
          cases result <;> cases h <;> apply bank_nine <;> constructor
  | done base index => cases h
  | failed base index remaining child => cases h

end Computation.BitMemoryBlock
