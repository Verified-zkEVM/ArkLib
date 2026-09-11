/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AddressedBitsSemantics

/-!
# Address-controller execution canary

Actual writes at two distinct addresses followed by an overwrite and reads distinguish aliasing,
wrong wire order, failure to update, and failure to preserve other cells. The empty path is a valid
root address. Raw malformed wire words are rejected. One transition before the public bound the
bus is empty but the controller has not yet returned. All checks use kernel reduction.
-/

@[expose] public section

namespace Computation.AddressedBits

private def store (mem : Memory) (address : Address) (value : Bool) : Configuration :=
  runFuel (fuel address) ⟨mem, .start (.write value) address⟩

private def fetch (mem : Memory) (address : Address) : Configuration :=
  runFuel (fuel address) ⟨mem, .start .read address⟩

/-- Full controller calls preserve the other address across an overwrite, including a root write. -/
example :
    let first := store .empty [false, true] true
    let second := store first.memory [true, false] true
    let third := store second.memory [false, true] false
    let fourth := store third.memory [] true
    first.control = .done (some true) ∧ second.control = .done (some true) ∧
    third.control = .done (some false) ∧ fourth.control = .done (some true) ∧
    (fetch fourth.memory [false, true]).control = .done (some false) ∧
    (fetch fourth.memory [true, false]).control = .done (some true) ∧
    (fetch fourth.memory []).control = .done (some true) ∧
    (fetch fourth.memory [false]).control = .done (some false) ∧
    fourth.memory.lookup [false, true] = false ∧
    fourth.memory.lookup [true, false] = true := by
  decide +kernel

/-- Full reset is necessary; malformed raw addresses cannot alias the valid root address. -/
theorem malformed_addresses_do_not_alias_root :
    let store := fun (mem : Memory) (address : Address) (value : Bool) ↦
      runFuel (fuel address) ⟨mem, .start (.write value) address⟩
    let mem := (store .empty [] true).memory
    runFuel 7 ⟨mem, .start .read []⟩ = ⟨mem, .reset (some true) []⟩ ∧
    runFuel 8 ⟨mem, .start .read []⟩ = ⟨mem, .done (some true)⟩ ∧
    runFuel 2 ⟨mem, .access .read []⟩ = ⟨mem, .done none⟩ ∧
    runFuel 3 ⟨mem, .access (.write false) [false]⟩ = ⟨mem, .done none⟩ := by
  decide +kernel

end Computation.AddressedBits
