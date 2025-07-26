/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gemini
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic

/-!
  # Memory checking relations: read-only and read-write

  This file defines a generic framework for memory checking relations. The goal is to provide a
  flexible API that can be instantiated with various memory models and operation containers.

  ## Main Concepts

  - **`MemoryRead`**, **`MemoryWrite`**: Represent a single read or write operation, containing
    the memory index and the value.

  - **`MemoryOp`**: An inductive type that wraps `MemoryRead` and `MemoryWrite` to represent a
    trace of operations.

  - **`Memory` typeclass**: Abstracts over the memory representation. It provides `read` and
    `write` operations. Instances for dependent functions (`(i : ι) → α i`) and `Vector` are
    provided.

  - **`ReadOnly.relation`**: A relation that holds if a given sequence of read operations is
    consistent with a given memory state.

  - **`ReadWrite.relation`**: A relation that holds if executing a sequence of memory operations
    on a starting memory state results in a given final memory state. Read operations are
    checked for consistency along the way.
-/

universe u v w

/-- A record of a memory read operation, containing the index and the value read. -/
@[reducible]
def MemoryRead (ι : Type u) (α : ι → Type v) := (index : ι) × (α index)

namespace MemoryRead

variable {ι : Type u} {α : ι → Type v}

@[reducible]
def index (op : MemoryRead ι α) := op.1

@[reducible]
def value (op : MemoryRead ι α) := op.2

end MemoryRead

/-- A record of a memory write operation, containing the index and the value written. -/
@[reducible]
def MemoryWrite (ι : Type u) (α : ι → Type v) := (index : ι) × (α index)

namespace MemoryWrite

variable {ι : Type u} {α : ι → Type v}

@[reducible]
def index (op : MemoryWrite ι α) := op.1

@[reducible]
def value (op : MemoryWrite ι α) := op.2

end MemoryWrite

/-- A record of a memory operation. A `Read` includes the `value` that was read, and a `Write`
  includes the `value` to be written. This is used to represent a trace of operations. -/
inductive MemoryOp (ι : Type u) (α : ι → Type v) where
  | read (op : MemoryRead ι α)
  | write (op : MemoryWrite ι α)

namespace MemoryOp

variable {ι : Type u} {α : ι → Type v}

/-- Checks if a `MemoryOp` is a read operation. -/
def isRead : MemoryOp ι α → Prop
  | read _ => True
  | _ => False

/-- Checks if a `MemoryOp` is a write operation. -/
def isWrite : MemoryOp ι α → Prop
  | write _ => True
  | _ => False

end MemoryOp

namespace MemoryChecking

variable {ι : Type u} {α : ι → Type v}

/-- A typeclass for memory structures, abstracting over the concrete representation of memory.
  This allows the memory checking relations to be generic. -/
class Memory (ι : Type u) (α : ι → Type v) (M : Type w) where
  /-- Reads a value from the memory at a given index. -/
  read (m : M) (i : ι) : α i
  /-- Writes a value to the memory at a given index, returning the new memory state. -/
  write (m : M) (i : ι) (v : α i) : M

/-- Provide an instance for the dependent function type `(i : ι) → α i` as a simple memory model. -/
instance [DecidableEq ι] : Memory ι α (∀ i, α i) where
  read m i := m i
  write m i v := Function.update m i v

/-- Provide an instance for the vector type `Vector α n` as a simple memory model. -/
instance {n : ℕ} {α : Type v} : Memory (Fin n) (fun _ => α) (Vector α n) where
  read m i := m[i]
  write m i v := m.set i v

-- TODO: provide instances for other container types? `(D)Finsupp`?
-- TODO: what if read/write can fail? Need for `Nat`-indexed memory represented with `List`

namespace ReadOnly

variable {ι : Type u} {α : ι → Type v} {M : Type w} [Memory ι α M] [∀ i, DecidableEq (α i)]

/--
The read-only memory checking relation.

It takes a memory `mem` and a list of read operations `ops`.
The relation holds if for each operation `op` in `ops`, `op.value` is consistent with the value
at `op.index` in `mem` (i.e., `Memory.read mem op.index = op.value`).
-/
def relation : Set (M × List (MemoryRead ι α)) :=
  { ⟨mem, ops⟩ | ∀ op ∈ ops, Memory.read mem op.index = op.value }

end ReadOnly

namespace ReadWrite

variable {ι : Type u} {α : ι → Type v} {M : Type w} [Memory ι α M] [∀ i, DecidableEq (α i)]

/--
Processes a list of memory operations `ops` on a starting memory state `startMem`, producing a
final state.

This function folds over `ops`, updating the memory state at each step:
- For a `read` operation, it checks if the value in the operation is consistent with the
  current memory state. If not, it fails (returns `none`).
- For a `write` operation, it updates the memory with the value from the operation.

Returns `some` of the final memory state on success, or `none` on a failed consistency check.
-/
def processMemoryOps (ops : List (MemoryOp ι α)) (startMem : M) : Option M :=
  ops.foldlM (fun m op =>
    match op with
    | .read ⟨i, v⟩ => if Memory.read m i = v then some m else none
    | .write ⟨i, v⟩ => some (Memory.write m i v)
  ) startMem

/--
The read-write memory checking relation.

It takes an initial memory `startMem`, a final memory `finalMem`, and a list of operations `ops`.
The relation holds if executing `ops` on `startMem` is consistent and results in `finalMem`.
-/
def relation : Set (M × M × List (MemoryOp ι α)) :=
  { ⟨startMem, finalMem, ops⟩ | processMemoryOps ops startMem = some finalMem }

end ReadWrite

end MemoryChecking
