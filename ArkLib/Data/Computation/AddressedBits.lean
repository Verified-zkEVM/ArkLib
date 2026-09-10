/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Data.List.Basic

/-!
# Address transfer in a bit RAM

Addresses are binary paths with an implicit leading one. The empty path denotes address one;
zero is reserved and has no address value. Thus every path has one canonical wire encoding,
`true :: path`, including paths starting with false. Distinct paths name distinct memory cells.

The literal controller transfers each input bit, restores wire order one bit at a time, performs
one addressed bit access, then erases every bus bit before returning. Every successor counts as
one **bit-RAM transition**. The terminal read/write is an openly stipulated random-access RAM
primitive. `Memory.lookup` and `Memory.write` give its executable finite-trie semantics; their host
evaluation time is not the transition count. In particular this is no tape simulation, native-time
bound, or compiler-correctness claim. No instruction accepts an arbitrary callback.

Input paths are already materialized on the local input tape. Starting writes the implicit leading
one. List head/tail operations model single local tape-cell operations, not random heap-list
operations. Shared heap representations and scalar arithmetic are separate future refinements.
-/

@[expose] public section

namespace Computation.AddressedBits

/-- A canonical positive binary address, with its leading one omitted. -/
abbrev Address := List Bool

/-- Finite bit memory; missing nodes denote zero bits. Redundant zero nodes are permitted. -/
inductive Memory where
  | empty
  | node (value : Bool) (zero one : Memory)
  deriving DecidableEq, Repr

namespace Memory

/-- Semantic random lookup, not a claimed constant-time host implementation. -/
def lookup : Memory → Address → Bool
  | .empty, _ => false
  | .node v _ _, [] => v
  | .node _ l r, b :: bs => lookup (if b then r else l) bs

/-- Semantic update of one RAM bit; unaddressed branches remain shared. -/
def write : Memory → Address → Bool → Memory
  | .empty, [], v => .node v .empty .empty
  | .node _ l r, [], v => .node v l r
  | .empty, b :: bs, v =>
      if b then .node false .empty (write .empty bs v)
      else .node false (write .empty bs v) .empty
  | .node w l r, b :: bs, v =>
      if b then .node w l (write r bs v) else .node w (write l bs v) r

/-- The write semantics changes exactly the named address, including previously absent cells. -/
theorem lookup_write (mem : Memory) (address query : Address) (value : Bool) :
    (mem.write address value).lookup query =
      if query = address then value else mem.lookup query := by
  induction address generalizing mem query with
  | nil => cases mem <;> cases query <;> simp [write, lookup]
  | cons b bs ih =>
    cases mem <;> cases query with
    | nil => cases b <;> simp [write, lookup]
    | cons c cs => cases b <;> cases c <;> simp [write, lookup, ih]

/-- Memory is observed by its bits, not by redundant trie structure. -/
def Equivalent (left right : Memory) : Prop := ∀ address, left.lookup address = right.lookup address

/-- Equal observations remain equal after the same write. -/
theorem Equivalent.write {left right : Memory} (h : Equivalent left right)
    (address : Address) (value : Bool) : Equivalent (left.write address value)
      (right.write address value) := by
  intro query
  simp only [lookup_write, h query]

end Memory

/-- Literal access operations; write returns the bit that was written. -/
inductive Operation where
  | read
  | write (value : Bool)
  deriving DecidableEq, Repr

/-- The finite instruction vocabulary of this fixed controller. -/
inductive Instruction where
  | start | transfer | restore | access | reset | halt
  deriving DecidableEq, Repr

/-- Local bit tapes and finite control. A malformed wire address returns `none`. -/
inductive Control where
  | start (op : Operation) (address : Address)
  | transfer (op : Operation) (remaining bus : List Bool)
  | restore (op : Operation) (remaining bus : List Bool)
  | access (op : Operation) (bus : List Bool)
  | reset (result : Option Bool) (bus : List Bool)
  | done (result : Option Bool)
  deriving DecidableEq, Repr

/-- Instruction selection depends only on the finite control tag. -/
def Control.instruction : Control → Instruction
  | .start _ _ => .start
  | .transfer _ _ _ => .transfer
  | .restore _ _ _ => .restore
  | .access _ _ => .access
  | .reset _ _ => .reset
  | .done _ => .halt

/-- The state retains the actual memory through every phase of the same run. -/
structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- Literal one-bit transitions. Only the access clause invokes architectural random memory. -/
def step : Configuration → Option Configuration
  | ⟨mem, .start op address⟩ => some ⟨mem, .transfer op (true :: address) []⟩
  | ⟨mem, .transfer op (b :: bs) bus⟩ => some ⟨mem, .transfer op bs (b :: bus)⟩
  | ⟨mem, .transfer op [] bus⟩ => some ⟨mem, .restore op bus []⟩
  | ⟨mem, .restore op (b :: bs) bus⟩ => some ⟨mem, .restore op bs (b :: bus)⟩
  | ⟨mem, .restore op [] bus⟩ => some ⟨mem, .access op bus⟩
  | ⟨mem, .access .read (true :: address)⟩ =>
      some ⟨mem, .reset (some (mem.lookup address)) (true :: address)⟩
  | ⟨mem, .access (.write value) (true :: address)⟩ =>
      some ⟨mem.write address value, .reset (some value) (true :: address)⟩
  | ⟨mem, .access _ bus⟩ => some ⟨mem, .reset none bus⟩
  | ⟨mem, .reset result (_ :: bs)⟩ => some ⟨mem, .reset result bs⟩
  | ⟨mem, .reset result []⟩ => some ⟨mem, .done result⟩
  | ⟨_, .done _⟩ => none

/-- An actual run with its exact number of bit-RAM successors. -/
inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- Fuel is an observer bounding successor calls, not an uncharged instruction inside the RAM. -/
def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

/-- Concatenation counts every transition of both literal runs. -/
theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Exact fuel observes precisely the same final state as the trace. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) :
    runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- A halted controller performs no additional transitions. -/
theorem runFuel_done (n : ℕ) (mem : Memory) (result : Option Bool) :
    runFuel n ⟨mem, .done result⟩ = ⟨mem, .done result⟩ := by
  cases n <;> rfl

end Computation.AddressedBits
