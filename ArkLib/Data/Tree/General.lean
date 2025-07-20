/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Tree.Basic

/-!
  # General Trees with Arbitrary Arities

  This file defines general tree data structures where nodes can have an arbitrary number
  of children (represented as lists).

  We provide two main variants:
  - `GeneralTree`: Trees where every node (including internal nodes) holds a value
  - `GeneralLeafTree`: Trees where only leaf nodes hold values, internal nodes are structural

  Both support arbitrary arities and include helper functions for common operations like
  finding paths, checking properties, and accessing structure information.
-/

/-- A general tree with arbitrary arity where every node (including internal nodes) holds a value.
    The children are represented as a list, allowing for any number of child nodes. -/
inductive GeneralTree (α : Type*) where
  | leaf : α → GeneralTree α
  | node : α → List (GeneralTree α) → GeneralTree α
  | nil : GeneralTree α
  deriving Inhabited, Repr

/-- A general tree with arbitrary arity where only leaf nodes hold values.
    Internal nodes are purely structural and do not store values.
    Used as input to general Merkle tree construction. -/
inductive GeneralLeafTree (α : Type*) where
  | leaf : α → GeneralLeafTree α
  | node : List (GeneralLeafTree α) → GeneralLeafTree α
  | nil : GeneralLeafTree α
  deriving Inhabited, Repr

namespace GeneralTree

variable {α : Type*}

/-- Get the root value of a general tree, if it exists. -/
def getRoot : GeneralTree α → Option α
  | GeneralTree.nil => none
  | GeneralTree.leaf a => some a
  | GeneralTree.node a _ => some a

/-- Get the number of children of a node. -/
def arity : GeneralTree α → Nat
  | GeneralTree.nil => 0
  | GeneralTree.leaf _ => 0
  | GeneralTree.node _ children => children.length

/-- Get the children of a node. -/
def children : GeneralTree α → List (GeneralTree α)
  | GeneralTree.nil => []
  | GeneralTree.leaf _ => []
  | GeneralTree.node _ children => children

/-- Check if the tree is a leaf. -/
def isLeaf : GeneralTree α → Bool
  | GeneralTree.leaf _ => true
  | _ => false

/-- Check if the tree is empty. -/
def isEmpty : GeneralTree α → Bool
  | GeneralTree.nil => true
  | _ => false

/-- Find the path from root to a leaf with the given value.
    The path is represented as a list of child indices. -/
def findPath [DecidableEq α] (a : α) : GeneralTree α → Option (List Nat)
  | GeneralTree.nil => none
  | GeneralTree.leaf b => if a = b then some [] else none
  | GeneralTree.node _ children => findPathInChildren a children 0
where
  findPathInChildren (a : α) (children : List (GeneralTree α)) (idx : Nat) : Option (List Nat) :=
    match children with
    | [] => none
    | child :: rest =>
      match findPath a child with
      | some path => some (idx :: path)
      | none => findPathInChildren a rest (idx + 1)

end GeneralTree

namespace GeneralLeafTree

variable {α : Type*}

/-- Get the number of children of a node. -/
def arity : GeneralLeafTree α → Nat
  | GeneralLeafTree.nil => 0
  | GeneralLeafTree.leaf _ => 0
  | GeneralLeafTree.node children => children.length

/-- Get the children of a node. -/
def children : GeneralLeafTree α → List (GeneralLeafTree α)
  | GeneralLeafTree.nil => []
  | GeneralLeafTree.leaf _ => []
  | GeneralLeafTree.node children => children

/-- Check if the tree is a leaf. -/
def isLeaf : GeneralLeafTree α → Bool
  | GeneralLeafTree.leaf _ => true
  | _ => false

/-- Check if the tree is empty. -/
def isEmpty : GeneralLeafTree α → Bool
  | GeneralLeafTree.nil => true
  | _ => false

/-- Find the path from root to a leaf with the given value.
    The path is represented as a list of child indices. -/
def findPath [DecidableEq α] (a : α) : GeneralLeafTree α → Option (List Nat)
  | GeneralLeafTree.nil => none
  | GeneralLeafTree.leaf b => if a = b then some [] else none
  | GeneralLeafTree.node children => findPathInChildren a children 0
where
  findPathInChildren (a : α) (children : List (GeneralLeafTree α)) (idx : Nat) :
      Option (List Nat) :=
    match children with
    | [] => none
    | child :: rest =>
      match findPath a child with
      | some path => some (idx :: path)
      | none => findPathInChildren a rest (idx + 1)

end GeneralLeafTree

-- Example usage:
section Examples

-- A general tree where every node holds a value
def GeneralTree.example : GeneralTree (Fin 10) :=
  .node 1 [
    .leaf 2,
    .node 3 [.leaf 4, .leaf 5, .leaf 6],
    .leaf 7,
    .node 8 [.leaf 9, .nil]
  ]

-- A general leaf tree where only leaves hold values
def GeneralLeafTree.example : GeneralLeafTree (Fin 10) :=
  .node [
    .leaf 1,
    .node [.leaf 2, .leaf 3, .leaf 4],
    .leaf 5,
    .node [.leaf 6, .nil]
  ]

end Examples
