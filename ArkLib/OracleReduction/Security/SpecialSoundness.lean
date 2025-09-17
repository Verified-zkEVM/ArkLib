/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.ProtocolSpec.Basic

/-!
  # Special Soundness

  Define arity-indexed trees (skeleton and data) to later express
  special soundness over transcript trees.
-/

-- Define a tree skeleton of given depth `n` and arities `ar : Fin n → ℕ`


namespace ArityTree

/-- A tree skeleton of depth `n` with arities `ar : Fin n → ℕ`.
At depth `0`, only a leaf is allowed. At depth `n+1`, a node has
`ar 0` children, each a skeleton of depth `n` with arities reindexed
by `Fin.succ`.
-/
inductive Skeleton :
    (n : ℕ) → (ar : Fin n → ℕ) → Type where
  | leaf {ar0 : Fin 0 → ℕ} : Skeleton 0 ar0
  | node {n : ℕ} {ar : Fin (n+1) → ℕ}
      (children : Fin (ar 0) →
        Skeleton n (fun i => ar i.succ)) :
      Skeleton (n+1) ar

/-- A tree with the given skeleton, storing values of type `α` at
every node (root and internal nodes as well as leaves).
This is the arity-generalized analogue of `BinaryTree.FullData` from
`ToMathlib/Data/IndexedBinaryTree`.
-/
inductive Data (α : Type) :
    {n : ℕ} → {ar : Fin n → ℕ} → Skeleton n ar → Type where
  | leaf {ar0 : Fin 0 → ℕ} (value : α) :
      Data α (Skeleton.leaf (ar0 := ar0))
  | node {n : ℕ} {ar : Fin (n+1) → ℕ}
      {children : Fin (ar 0) →
        Skeleton n (fun i => ar i.succ)}
      (value : α)
      (childrenData : (i : Fin (ar 0)) →
        Data α (children i)) :
      Data α (Skeleton.node children)

end ArityTree

section Examples

open ArityTree

/-- Depth-0 skeleton (single leaf). -/
def exSkel0 : ArityTree.Skeleton 0 (fun i => nomatch i) :=
  ArityTree.Skeleton.leaf

/-- Depth-0 data example. -/
def exData0 {α} (a : α) : ArityTree.Data α exSkel0 :=
  ArityTree.Data.leaf a

/-- Arity function for depth-1 trees with `k` children at the root. -/
def ar1 (k : ℕ) : Fin 1 → ℕ := fun _ => k

/-- Depth-1 "star" skeleton with `k` leaves under the root. -/
def starSkel (k : ℕ) : ArityTree.Skeleton 1 (ar1 k) :=
  ArityTree.Skeleton.node (fun _ => ArityTree.Skeleton.leaf)

/-- Depth-1 data example: root value and `k` leaf values. -/
def starData {α} (k : ℕ) (root : α) (leaves : Fin k → α) :
    ArityTree.Data α (starSkel k) := by
  change
    ArityTree.Data α
      (ArityTree.Skeleton.node (fun _ => ArityTree.Skeleton.leaf))
  exact
    ArityTree.Data.node root (fun i => ArityTree.Data.leaf (leaves i))

/-- Arity function for depth-2 trees with `k0` children at root and
`k1` children at every depth-1 node. -/
def ar2 (k0 k1 : ℕ) : Fin 2 → ℕ
  | ⟨0, _⟩ => k0
  | ⟨1, _⟩ => k1

/-- Depth-2 uniform skeleton. -/
def twoLevelSkel (k0 k1 : ℕ) :
    ArityTree.Skeleton 2 (ar2 k0 k1) :=
  ArityTree.Skeleton.node (fun _ =>
    ArityTree.Skeleton.node (fun _ => ArityTree.Skeleton.leaf))

/-- Depth-2 data example with values at root, level-1, and leaves. -/
def twoLevelData {α} (k0 k1 : ℕ)
    (root : α)
    (lvl1 : Fin k0 → α)
    (lvl2 : (i : Fin k0) → Fin k1 → α) :
    ArityTree.Data α (twoLevelSkel k0 k1) := by
  change
    ArityTree.Data α
      (ArityTree.Skeleton.node (fun _ =>
        ArityTree.Skeleton.node (fun _ => ArityTree.Skeleton.leaf)))
  refine ArityTree.Data.node root (fun i => ?_)
  change
    ArityTree.Data α
      (ArityTree.Skeleton.node (fun _ => ArityTree.Skeleton.leaf)
      )
  refine ArityTree.Data.node (lvl1 i) (fun j => ?_)
  exact ArityTree.Data.leaf (lvl2 i j)

end Examples

/-!
## Transcript trees for a given ProtocolSpec

We refine `ArityTree` to a transcript tree whose node value at level `i`
is the message/challenge dictated by a protocol specification `pSpec`.
The branching arity across levels is given by a vector `ar : Fin n → ℕ`.
-/

namespace TranscriptTree

open ProtocolSpec

variable {n : ℕ}

/-- The dependent transcript data over a skeleton for `pSpec`.

At the root of a nonempty protocol `(n+1)`, we store either a message
or a challenge of round `0` (depending on `pSpec.dir 0`). The children
are transcript data for the tail protocol `pSpec.drop 1` and the tail
arities `fun i => ar i.succ`.

At depth `0` (empty protocol), there is no data (we use `PUnit`).
-/
inductive Data :
    {n : ℕ} → (pSpec : ProtocolSpec n) →
    {ar : Fin n → ℕ} → ArityTree.Skeleton n ar → Type 1 where
  | leaf {pSpec : ProtocolSpec 0} {ar0 : Fin 0 → ℕ} :
      Data pSpec (ArityTree.Skeleton.leaf (ar0 := ar0))
  | msgNode {n : ℕ}
      {pSpec : ProtocolSpec (n + 1)} {ar : Fin (n + 1) → ℕ}
      (h : pSpec.dir 0 = Direction.P_to_V)
      (val : pSpec.Message' 0 h)
      {children : Fin (ar 0) →
        ArityTree.Skeleton n (fun i => ar i.succ)}
      (childrenData : (i : Fin (ar 0)) →
        Data (pSpec := pSpec.drop 1 (Nat.succ_le_succ (Nat.zero_le n))) (children i)) :
      Data pSpec (ArityTree.Skeleton.node children)
  | chalNode {n : ℕ}
      {pSpec : ProtocolSpec (n + 1)} {ar : Fin (n + 1) → ℕ}
      (h : pSpec.dir 0 = Direction.V_to_P)
      (val : pSpec.Challenge' 0 h)
      {children : Fin (ar 0) →
        ArityTree.Skeleton n (fun i => ar i.succ)}
      (childrenData : (i : Fin (ar 0)) →
        Data (pSpec := pSpec.drop 1 (Nat.succ_le_succ (Nat.zero_le n))) (children i)) :
      Data pSpec (ArityTree.Skeleton.node children)

/-! ### Small constructors/examples for length-1 protocols -/

-- /-- For a length-1 protocol with a message at round 0, build a star transcript. -/
-- def starMsg {pSpec : ProtocolSpec 1}
--     (h : pSpec.dir 0 = Direction.P_to_V)
--     (k : ℕ)
--     (msg : pSpec.Message' 0 h) :
--     Data pSpec (ar := !v[1])
--       (ArityTree.Skeleton.node (children :=
--         (fun _ : Fin k => by dsimp))) :=
--   Data.msgNode h msg (children := fun _ : Fin k => ArityTree.Skeleton.leaf)
--     (fun _ => Data.leaf)

-- /-- For a length-1 protocol with a challenge at round 0, build a star transcript. -/
-- def starChal {pSpec : ProtocolSpec 1}
--     (h : pSpec.dir 0 = Direction.V_to_P)
--     (k : ℕ)
--     (chal : pSpec.Challenge' 0 h) :
--     Data pSpec
--       (ArityTree.Skeleton.node (children :=
--         (fun _ : Fin k => ArityTree.Skeleton.leaf))) :=
--   Data.chalNode h chal (children := fun _ : Fin k => ArityTree.Skeleton.leaf)
--     (fun _ => Data.leaf)

end TranscriptTree
