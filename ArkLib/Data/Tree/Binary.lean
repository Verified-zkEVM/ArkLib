/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Tree.Basic

/-!
  # Binary Trees

  This file defines binary tree data structures with different value storage patterns.

  We provide two main variants:
  - `BinaryTree`: Trees where both leaf and internal nodes can hold values
  - `BinaryLeafTree`: Trees where only leaf nodes hold values, internal nodes are structural

  These complement Mathlib's `Tree` type (which stores values only in internal nodes)
  and are particularly useful for Merkle tree implementations and other cryptographic
  applications where different node types serve different purposes.

  ## Comparison with Mathlib's Tree

  - **Mathlib's `Tree α`**: Values only in internal nodes (traditional binary tree)
  - **`BinaryTree α`**: Values in both leaf and internal nodes (maximum flexibility)
  - **`BinaryLeafTree α`**: Values only in leaf nodes (common in Merkle trees)
-/

/-- A binary tree with (possibly null) values stored at both leaf and internal nodes.

    This provides maximum flexibility where both leaf and internal nodes can carry data.
    Useful for complex tree structures where different types of nodes serve different purposes. -/
inductive BinaryTree (α : Type*) where
  | leaf : α → BinaryTree α
  | node : α → BinaryTree α → BinaryTree α → BinaryTree α
  | nil : BinaryTree α
  deriving Inhabited, Repr

/-- A binary tree where only leaf nodes can have values.
    Internal nodes are purely structural and do not store values.

    This is commonly used as input to Merkle tree construction where
    only the leaf data matters for the cryptographic commitments. -/
inductive BinaryLeafTree (α : Type*) where
  | leaf : α → BinaryLeafTree α
  | node : BinaryLeafTree α → BinaryLeafTree α → BinaryLeafTree α
  | nil : BinaryLeafTree α
  deriving Inhabited, Repr

namespace BinaryTree

variable {α : Type*}

/-- Get the root value of a binary tree, if it exists. -/
def getRoot : BinaryTree α → Option α
  | BinaryTree.nil => none
  | BinaryTree.leaf a => some a
  | BinaryTree.node a _ _ => some a

/-- Check if the tree is a leaf. -/
def isLeaf : BinaryTree α → Bool
  | BinaryTree.leaf _ => true
  | _ => false

/-- Check if the tree is empty. -/
def isEmpty : BinaryTree α → Bool
  | BinaryTree.nil => true
  | _ => false

/-- Get the left child of the tree. -/
def left : BinaryTree α → BinaryTree α
  | BinaryTree.nil => BinaryTree.nil
  | BinaryTree.leaf _ => BinaryTree.nil
  | BinaryTree.node _ l _ => l

/-- Get the right child of the tree. -/
def right : BinaryTree α → BinaryTree α
  | BinaryTree.nil => BinaryTree.nil
  | BinaryTree.leaf _ => BinaryTree.nil
  | BinaryTree.node _ _ r => r

/-- Find the path from root to a leaf with the given value.
    Returns a list of boolean directions (false = left, true = right). -/
def findPath [DecidableEq α] (a : α) : BinaryTree α → Option (List Bool)
  | BinaryTree.nil => none
  | BinaryTree.leaf b => if a = b then some [] else none
  | BinaryTree.node _ left right =>
    match findPath a left with
    | some path => some (false :: path)
    | none =>
      match findPath a right with
      | some path => some (true :: path)
      | none => none



end BinaryTree

namespace BinaryLeafTree

variable {α : Type*}

/-- Check if the tree is a leaf. -/
def isLeaf : BinaryLeafTree α → Bool
  | BinaryLeafTree.leaf _ => true
  | _ => false

/-- Check if the tree is empty. -/
def isEmpty : BinaryLeafTree α → Bool
  | BinaryLeafTree.nil => true
  | _ => false

/-- Get the left child of the tree. -/
def left : BinaryLeafTree α → BinaryLeafTree α
  | BinaryLeafTree.nil => BinaryLeafTree.nil
  | BinaryLeafTree.leaf _ => BinaryLeafTree.nil
  | BinaryLeafTree.node l _ => l

/-- Get the right child of the tree. -/
def right : BinaryLeafTree α → BinaryLeafTree α
  | BinaryLeafTree.nil => BinaryLeafTree.nil
  | BinaryLeafTree.leaf _ => BinaryLeafTree.nil
  | BinaryLeafTree.node _ r => r

/-- Find the path from root to a leaf with the given value.
    Returns a list of boolean directions (false = left, true = right). -/
def findPath [DecidableEq α] (a : α) : BinaryLeafTree α → Option (List Bool)
  | BinaryLeafTree.nil => none
  | BinaryLeafTree.leaf b => if a = b then some [] else none
  | BinaryLeafTree.node left right =>
    match findPath a left with
    | some path => some (false :: path)
    | none =>
      match findPath a right with
      | some path => some (true :: path)
      | none => none

end BinaryLeafTree

-- Example usage:
section Examples

-- Example:
--        1
--       / \
--      2   3
--     / \   \
--    4   5   6
--       /
--      7
-- A tree with values at both leaf and internal nodes
def BinaryTree.example : BinaryTree (Fin 10) :=
  .node 1
    (.node 2
      (.leaf 4)
      (.node 5 (.leaf 7) .nil))
    (.node 3
      .nil
      (.leaf 6))

-- A leaf tree where only leaves hold values
def BinaryLeafTree.example : BinaryLeafTree (Fin 10) :=
  .node
    (.node (.leaf 1) (.leaf 2))
    (.node (.leaf 3) .nil)

end Examples
