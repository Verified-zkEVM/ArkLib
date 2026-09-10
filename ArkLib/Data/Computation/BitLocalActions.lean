/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AddressedBits
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.SplitIfs

/-!
# Shared local bit-tape interface

One finite-control bit-RAM transition can keep, pop one bit from, or push one bit onto each of
four local stacks. Its finite Boolean control can inspect their heads. This is a local storage
interface, not permission to execute arbitrary transformations of words in one step. Clients
supply fixed literal controllers and prove every successor has this shape.

The address controller inhabits exactly this interface: restoration reads the former bus tape
and writes the former input tape. No phase change copies or exchanges a whole list. The separate
architectural random-access operation remains precisely the one documented by `AddressedBits`.
-/

@[expose] public section

namespace Computation.BitLocalActions

/-- The three possible actions on one local bit stack. -/
inductive CellStep : List Bool → List Bool → Prop where
  | keep (bits) : CellStep bits bits
  | pop (bit bits) : CellStep (bit :: bits) bits
  | push (bit bits) : CellStep bits (bit :: bits)

/-- Four physical local tapes; names do not change on a controller phase change. -/
structure Tapes where
  left : List Bool := []
  right : List Bool := []
  saved : List Bool := []
  output : List Bool := []
  deriving DecidableEq, Repr

/-- At most one cell operation per tape, in one simultaneous finite-control transition. -/
def Step (before after : Tapes) : Prop :=
  CellStep before.left after.left ∧ CellStep before.right after.right ∧
    CellStep before.saved after.saved ∧ CellStep before.output after.output

/-- Pointwise local actions on any fixed finite tape bank. Its index size is program-fixed. -/
def BankStep {ι : Type*} [Fintype ι] (before after : ι → List Bool) : Prop :=
  ∀ i, CellStep (before i) (after i)

/-- Embed the four physical tapes in a larger fixed bank with blank extra tapes. -/
def Tapes.pad (tapes : Tapes) (extra : ℕ) : Fin (4 + extra) → List Bool := fun i ↦
  if i.val < 4 then
    if i.val = 0 then tapes.left else if i.val = 1 then tapes.right
    else if i.val = 2 then tapes.saved else tapes.output
  else []

/-- Enlarging the fixed bank preserves the local transition and leaves extra tapes blank. -/
theorem Step.pad {before after : Tapes} (h : Step before after) (extra : ℕ) :
    BankStep (before.pad extra) (after.pad extra) := by
  intro i
  unfold Tapes.pad
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2
  · exact .keep []

/-- Frame arbitrary retained extra tapes around the four arithmetic tapes. -/
def Tapes.frame {extra : ℕ} (tapes : Tapes) (rest : Fin extra → List Bool) :
    Fin (4 + extra) → List Bool := fun i ↦
  if h : i.val < 4 then tapes.pad extra i
  else rest ⟨i.val - 4, by omega⟩

/-- A local instruction preserves arbitrary extra tape contents, not only blank scratch tapes. -/
theorem Step.frame {before after : Tapes} (h : Step before after) {extra : ℕ}
    (rest : Fin extra → List Bool) : BankStep (before.frame rest) (after.frame rest) := by
  intro i
  unfold Tapes.frame
  split_ifs
  · exact h.pad extra i
  · exact .keep _

/-- Existing address phases projected onto fixed physical tapes. -/
def addressTapes : AddressedBits.Control → Tapes
  | .start _ address => { left := address }
  | .transfer _ remaining bus => { left := remaining, right := bus }
  | .restore _ remaining bus => { left := bus, right := remaining }
  | .access _ bus => { left := bus }
  | .reset _ bus => { left := bus }
  | .done _ => {}

/-- Every actual address successor obeys the common local bit-storage interface. -/
theorem address_step {s t : AddressedBits.Configuration} (h : AddressedBits.step s = some t) :
    Step (addressTapes s.control) (addressTapes t.control) := by
  rcases s with ⟨mem, state⟩
  cases state with
  | start op address => cases h; exact ⟨.push _ _, .keep _, .keep _, .keep _⟩
  | transfer op remaining bus =>
    cases remaining with
    | nil => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons b bs => cases h; exact ⟨.pop _ _, .push _ _, .keep _, .keep _⟩
  | restore op remaining bus =>
    cases remaining with
    | nil => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons b bs => cases h; exact ⟨.push _ _, .pop _ _, .keep _, .keep _⟩
  | access op bus =>
    cases op <;> cases bus with
    | nil => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons b bs => cases b <;> cases h <;> exact ⟨.keep _, .keep _, .keep _, .keep _⟩
  | reset result bus =>
    cases bus with
    | nil => cases h; exact ⟨.keep _, .keep _, .keep _, .keep _⟩
    | cons b bs => cases h; exact ⟨.pop _ _, .keep _, .keep _, .keep _⟩
  | done result => cases h

end Computation.BitLocalActions
