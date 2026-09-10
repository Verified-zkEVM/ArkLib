/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AddressedBits

/-!
# Same-run address-controller correctness

The count is exactly `3 * address.length + 8` bit-RAM transitions: start, two bit traversals,
their phase changes, one architectural access, and complete bus reset. The initial path is already
materialized. The observer's Lean fuel recursion is not a measured host runtime. Both correctness
and frame properties refer to the actual memory returned by that same literal controller run.
-/

@[expose] public section

namespace Computation.AddressedBits

/-- Reset consumes every bus bit before emitting the result. -/
theorem reset_trace (mem : Memory) (result : Option Bool) (bus : List Bool) :
    Trace (bus.length + 1) ⟨mem, .reset result bus⟩ ⟨mem, .done result⟩ := by
  induction bus with
  | nil => exact Trace.cons rfl (Trace.nil _)
  | cons b bs ih => simpa [Nat.add_assoc] using Trace.cons (by rfl) ih

/-- Restoring wire order transfers one bit per transition and then changes phase. -/
theorem restore_trace (mem : Memory) (op : Operation) (remaining bus : List Bool) :
    Trace (remaining.length + 1) ⟨mem, .restore op remaining bus⟩
      ⟨mem, .access op (remaining.reverse ++ bus)⟩ := by
  induction remaining generalizing bus with
  | nil => exact Trace.cons rfl (Trace.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: bus))

/-- Input transfer consumes one bit per transition, preserving the actual reversed bus. -/
theorem transfer_trace (mem : Memory) (op : Operation) (remaining bus : List Bool) :
    Trace (remaining.length + 1) ⟨mem, .transfer op remaining bus⟩
      ⟨mem, .restore op (remaining.reverse ++ bus) []⟩ := by
  induction remaining generalizing bus with
  | nil => exact Trace.cons rfl (Trace.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: bus))

/-- Specification of one architectural access, never a callback accepted by the controller. -/
def effect (mem : Memory) (op : Operation) (address : Address) : Memory × Bool :=
  match op with
  | .read => (mem, mem.lookup address)
  | .write value => (mem.write address value, value)

/-- The actual access and complete reset return the architectural result. -/
theorem access_trace (mem : Memory) (op : Operation) (address : Address) :
    Trace (address.length + 3) ⟨mem, .access op (true :: address)⟩
      ⟨(effect mem op address).1, .done (some (effect mem op address).2)⟩ := by
  cases op <;>
    simpa [effect, Nat.add_assoc] using Trace.cons (by rfl) (reset_trace _ _ (true :: address))

/-- Starting from a canonical path, the same run transfers, accesses, and clears the entire bus. -/
theorem execution_trace (mem : Memory) (op : Operation) (address : Address) :
    Trace (3 * address.length + 8) ⟨mem, .start op address⟩
      ⟨(effect mem op address).1, .done (some (effect mem op address).2)⟩ := by
  have ht := transfer_trace mem op (true :: address) []
  have hr := restore_trace mem op (true :: address).reverse []
  have ha := access_trace mem op address
  simp only [List.append_nil] at ht
  simp only [List.reverse_reverse, List.append_nil] at hr
  have hs : step ⟨mem, .start op address⟩ = some ⟨mem, .transfer op (true :: address) []⟩ := rfl
  have h := Trace.cons hs ((ht.append hr).append ha)
  convert h using 1
  simp only [List.length_reverse, List.length_cons]
  omega

/-- The exact number of bit-RAM transitions for a materialized address path. -/
def fuel (address : Address) : ℕ := 3 * address.length + 8

/-- The observer returns the same complete state and architectural result as the literal trace. -/
theorem execution_runFuel (mem : Memory) (op : Operation) (address : Address) :
    runFuel (fuel address) ⟨mem, .start op address⟩ =
      ⟨(effect mem op address).1, .done (some (effect mem op address).2)⟩ :=
  (execution_trace mem op address).runFuel_eq

/-- Same-run read correctness, full-memory preservation, and the explicit linear bound. -/
theorem read_correct (mem : Memory) (address : Address) :
    ∃ n ≤ 3 * address.length + 8,
      Trace n ⟨mem, .start .read address⟩ ⟨mem, .done (some (mem.lookup address))⟩ ∧
      runFuel n ⟨mem, .start .read address⟩ = ⟨mem, .done (some (mem.lookup address))⟩ :=
  ⟨fuel address, Nat.le_refl _, execution_trace mem .read address,
    execution_runFuel mem .read address⟩

/-- Same-run write correctness and the frame property for every other address. -/
theorem write_correct (mem : Memory) (address : Address) (value : Bool) :
    ∃ n ≤ 3 * address.length + 8, ∃ out : Memory,
      Trace n ⟨mem, .start (.write value) address⟩ ⟨out, .done (some value)⟩ ∧
      runFuel n ⟨mem, .start (.write value) address⟩ = ⟨out, .done (some value)⟩ ∧
      out.lookup address = value ∧
      ∀ query, query ≠ address → out.lookup query = mem.lookup query := by
  refine ⟨fuel address, Nat.le_refl _, mem.write address value,
    execution_trace mem (.write value) address,
    execution_runFuel mem (.write value) address, ?_, ?_⟩
  · simp [Memory.lookup_write]
  · intro query hq
    simp [Memory.lookup_write, hq]

/-- An empty raw wire bus is rejected and reset without accessing memory. -/
theorem empty_wire_rejected (mem : Memory) (op : Operation) :
    Trace 2 ⟨mem, .access op []⟩ ⟨mem, .done none⟩ := by
  cases op <;> exact Trace.cons rfl (Trace.cons rfl (Trace.nil _))

/-- A raw wire word starting with zero is rejected; it cannot alias a canonical address. -/
theorem zero_wire_rejected (mem : Memory) (op : Operation) (bits : List Bool) :
    Trace (bits.length + 3) ⟨mem, .access op (false :: bits)⟩ ⟨mem, .done none⟩ := by
  cases op <;>
    simpa [Nat.add_assoc] using Trace.cons (by rfl) (reset_trace mem none (false :: bits))

end Computation.AddressedBits
