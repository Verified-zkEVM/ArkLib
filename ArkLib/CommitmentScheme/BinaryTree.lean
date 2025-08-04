/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ArkLib.Data.Math.Basic
import ArkLib.CommitmentScheme.Basic
import Mathlib.Data.Vector.Snoc
import ArkLib.CommitmentScheme.QueryCacheToSet

/-!
# Inductive Indexed Binary Trees

## Notes & TODOs

### Binary Tree API

- More API about equivlances between
  - `SkeletonNodeIndex` ≃ `SkeletonInternalIndex` ⊕ `SkeletonLeafIndex`
  - analogously
  - `FullDataTree α ≃ InternalDataTree α × LeafDataTree α`
- Data trees should have `CoeFun` instances
- Functions for navigating tree
  - [ ] Go to parent if it exists
  - [ ] Go to left child if it exists
  - [ ] Go to right child if it exists
  - [ ] Go to sibling if it exists
  - [ ] Return Sym2 of left and right children
  - Function for relationships between all these tree navigations
    - [ ] How do these navigations affect depth?
    - [ ] Which navigation sequences are equivalent to each other?
- API for functorial mapping over data carried by the tree
- API for getting the left and right subtrees of a tree.
- API for flatttening a tree to a list
- Define `Lattice` structure on trees
  - a susbset relation on trees, mappings of indices to indices of supertrees
- Define a datatype for indices of trees agnostic of the skeleton,
  - This type has an equivalence to lists of bools,
  - and maps from the the other indexing types.

#### Changes?

- Replace `List`s with `FreeSubgroup` for ancestors?
- Rename so that "tree" does not appear twice in names. E.g. BinaryTree.FullData instead of
  BinaryTree.FullDataTree


-/

namespace BinaryTree

/-!
# Binary Trees

This section contains datatypes for working with binary trees.

There

-/

/--
Inductive data type for a binary tree skeleton.
A skeleton is a binary tree without values, used to represent the structure of the tree.
-/
inductive Skeleton where
  | leaf : Skeleton -- TODO rename to `nil`?
  | internal : Skeleton → Skeleton → Skeleton

/-- Type of indices of leaves of a skeleton -/
inductive SkeletonLeafIndex : Skeleton → Type
  | ofLeaf : SkeletonLeafIndex Skeleton.leaf
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonLeafIndex left) :
      SkeletonLeafIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonLeafIndex right) :
      SkeletonLeafIndex (Skeleton.internal left right)

/-- Type of indices of internal nodes of a skeleton -/
inductive SkeletonInternalIndex : Skeleton → Type
  | ofInternal {left right} : SkeletonInternalIndex (Skeleton.internal left right)
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonLeafIndex left) :
      SkeletonInternalIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonLeafIndex right) :
      SkeletonInternalIndex (Skeleton.internal left right)

/-- Type of indices of any node of a skeleton -/
inductive SkeletonNodeIndex : Skeleton → Type
  | ofLeaf : SkeletonNodeIndex Skeleton.leaf
  | ofInternal {left right} :
      SkeletonNodeIndex (Skeleton.internal left right)
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonNodeIndex left) :
      SkeletonNodeIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonNodeIndex right) :
      SkeletonNodeIndex (Skeleton.internal left right)

/-- Construct a `SkeletonLeafIndex` from a `SkeletonNodeIndex` -/
def SkeletonLeafIndex.toNodeIndex {s : Skeleton} (idx : SkeletonLeafIndex s) :
    SkeletonNodeIndex s :=
  match idx with
  | SkeletonLeafIndex.ofLeaf => SkeletonNodeIndex.ofLeaf
  | SkeletonLeafIndex.ofLeft idxLeft =>
    SkeletonNodeIndex.ofLeft (SkeletonLeafIndex.toNodeIndex idxLeft)
  | SkeletonLeafIndex.ofRight idxRight =>
    SkeletonNodeIndex.ofRight (SkeletonLeafIndex.toNodeIndex idxRight)

/-- Depth of a SkeletonNodeIndex -/
def SkeletonNodeIndex.depth {s : Skeleton} : SkeletonNodeIndex s → Nat
  | SkeletonNodeIndex.ofLeaf => 0
  | SkeletonNodeIndex.ofInternal => 0
  | SkeletonNodeIndex.ofLeft idxLeft => idxLeft.depth + 1
  | SkeletonNodeIndex.ofRight idxRight => idxRight.depth + 1

def SkeletonNodeIndex.parent {s : Skeleton} (idx : SkeletonNodeIndex s) :
    Option (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => none
  | SkeletonNodeIndex.ofInternal => none
  | SkeletonNodeIndex.ofLeft (.ofLeaf) => some .ofInternal
  | SkeletonNodeIndex.ofLeft (.ofInternal) => some .ofInternal
  | SkeletonNodeIndex.ofLeft idxLeft =>
    idxLeft.parent.map (SkeletonNodeIndex.ofLeft)
  | SkeletonNodeIndex.ofRight (.ofLeaf) => some .ofInternal
  | SkeletonNodeIndex.ofRight (.ofInternal) => some .ofInternal
  | SkeletonNodeIndex.ofRight idxRight =>
    idxRight.parent.map (SkeletonNodeIndex.ofRight)

/-- Get the root value of a InternalDataTree. -/
def getRootIndex (s : Skeleton) : SkeletonNodeIndex s := match s with
  | Skeleton.leaf => SkeletonNodeIndex.ofLeaf
  | Skeleton.internal _ _ =>
    SkeletonNodeIndex.ofInternal

-- Analogous to `Cache`
/--
A binary tree with values stored in internal nodes.
-/
inductive InternalDataTree (α : Type) : Skeleton → Type
  | leaf : InternalDataTree α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : InternalDataTree α left)
      (rightData : InternalDataTree α right) : InternalDataTree α (Skeleton.internal left right)
  deriving Repr

/--
A binary tree with values stored at leaves.
-/
inductive LeafDataTree (α : Type) : Skeleton → Type
  | leaf (value : α) : LeafDataTree α Skeleton.leaf
  | internal {left right} (leftData : LeafDataTree α left) (rightData : LeafDataTree α right) :
      LeafDataTree α (Skeleton.internal left right)
  deriving Repr

def LeafDataTree.getLeftSubtree {α : Type} {s_left s_right : Skeleton}
    (tree : LeafDataTree α (Skeleton.internal s_left s_right)) :
    LeafDataTree α s_left :=
  match tree with
  | LeafDataTree.internal left _right =>
    left

def LeafDataTree.getRightSubtree {α : Type} {s_left s_right : Skeleton}
    (tree : LeafDataTree α (Skeleton.internal s_left s_right)) :
    LeafDataTree α s_right :=
  match tree with
  | LeafDataTree.internal _left right =>
    right

/-- Get the root value of a InternalDataTree. -/
def LeafDataTree.getValueAtIndex {s} {α : Type}
    (tree : LeafDataTree α s) (idx : SkeletonLeafIndex s) : α :=
  match tree, idx with
  | LeafDataTree.leaf value, SkeletonLeafIndex.ofLeaf => value
  | LeafDataTree.internal left _, SkeletonLeafIndex.ofLeft idxLeft =>
    LeafDataTree.getValueAtIndex left idxLeft
  | LeafDataTree.internal _ right, SkeletonLeafIndex.ofRight idxRight =>
    LeafDataTree.getValueAtIndex right idxRight

lemma LeafDataTree.getValueAtIndex_ofLeft {s_left s_right : Skeleton} {α : Type}
    (tree : LeafDataTree α (Skeleton.internal s_left s_right))
    (idxLeft : SkeletonLeafIndex s_left) :
    tree.getValueAtIndex (SkeletonLeafIndex.ofLeft idxLeft) =
      tree.getLeftSubtree.getValueAtIndex idxLeft := by
  match tree with
  | LeafDataTree.internal left _ =>
    rfl

lemma LeafDataTree.getValueAtIndex_ofRight {s_left s_right : Skeleton} {α : Type}
    (tree : LeafDataTree α (Skeleton.internal s_left s_right))
    (idxRight : SkeletonLeafIndex s_right) :
    tree.getValueAtIndex (SkeletonLeafIndex.ofRight idxRight) =
      tree.getRightSubtree.getValueAtIndex idxRight := by
  match tree with
  | LeafDataTree.internal _ right =>
    rfl

/--
A binary tree with values stored at both leaves and internal nodes.
-/
inductive FullDataTree (α : Type) : Skeleton → Type
  | leaf (value : α) : FullDataTree α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : FullDataTree α left)
      (rightData : FullDataTree α right) :
      FullDataTree α (Skeleton.internal left right)

lemma FullDataTree.leaf_eq {α} (tree : FullDataTree α Skeleton.leaf) :
    ∃ a, tree = FullDataTree.leaf a := by
  cases tree with
  | leaf value =>
    use value

lemma FullDataTree.internal_eq {α} {s_left s_right : Skeleton}
    (tree : FullDataTree α (Skeleton.internal s_left s_right)) :
    ∃ value left right, tree = FullDataTree.internal value left right := by
  cases tree with
  | internal value left right =>
    use value, left, right

def FullDataTree.getLeftSubtree {α : Type} {s_left s_right : Skeleton}
    (tree : FullDataTree α (Skeleton.internal s_left s_right)) :
    FullDataTree α s_left :=
  match tree with
  | FullDataTree.internal _ left _right =>
    left

def FullDataTree.getRightSubtree {α : Type} {s_left s_right : Skeleton}
    (tree : FullDataTree α (Skeleton.internal s_left s_right)) :
    FullDataTree α s_right :=
  match tree with
  | FullDataTree.internal _ _left right =>
    right

/-- Convert a `FullDataTree` to a `LeafDataTree` by dropping the internal node values. -/
def FullDataTree.toLeafDataTree {α : Type} {s : Skeleton}
    (tree : FullDataTree α s) : LeafDataTree α s :=
  match tree with
  | FullDataTree.leaf value => LeafDataTree.leaf value
  | FullDataTree.internal _ left right =>
    LeafDataTree.internal (left.toLeafDataTree) (right.toLeafDataTree)

@[simp]
lemma FullDataTree.toLeafDataTree_leaf {α} (a : α) :
    (FullDataTree.leaf a).toLeafDataTree = LeafDataTree.leaf a := by
  rfl

lemma FullDataTree.toLeafDataTree_getLeftSubtree {α} {s_left s_right : Skeleton}
    (tree : FullDataTree α (Skeleton.internal s_left s_right)) :
    tree.toLeafDataTree.getLeftSubtree =
      tree.getLeftSubtree.toLeafDataTree := by
  match tree with
  | FullDataTree.internal _ left _right =>
    rfl

lemma FullDataTree.toLeafDataTree_getRightSubtree {α} {s_left s_right : Skeleton}
    (tree : FullDataTree α (Skeleton.internal s_left s_right)) :
    tree.toLeafDataTree.getRightSubtree =
      tree.getRightSubtree.toLeafDataTree := by
  match tree with
  | FullDataTree.internal _ _left right =>
    rfl

lemma FullDataTree.toLeafDataTree_eq_leaf {α} (a : α) (tree)
    (h : LeafDataTree.leaf a = tree.toLeafDataTree) :
    tree = FullDataTree.leaf a := by
  cases tree with
  | leaf value =>
    simp only [FullDataTree.toLeafDataTree] at h
    cases h
    rfl

@[simp]
lemma FullDataTree.toLeafDataTree_internal {α} {s_left s_right : Skeleton}
    (value : α) (left : FullDataTree α s_left) (right : FullDataTree α s_right) :
    (FullDataTree.internal value left right).toLeafDataTree =
      LeafDataTree.internal (left.toLeafDataTree) (right.toLeafDataTree) := by
  rfl

/-- Get the root value of a InternalDataTree. -/
def FullDataTree.getValueAtIndex {s} {α : Type}
    (tree : FullDataTree α s) (idx : SkeletonNodeIndex s) : α :=
  match tree, idx with
  | FullDataTree.leaf value, SkeletonNodeIndex.ofLeaf => value
  | FullDataTree.internal value _ _, SkeletonNodeIndex.ofInternal => value
  | FullDataTree.internal _ left _, SkeletonNodeIndex.ofLeft idxLeft =>
    FullDataTree.getValueAtIndex left idxLeft
  | FullDataTree.internal _ _ right, SkeletonNodeIndex.ofRight idxRight =>
    FullDataTree.getValueAtIndex right idxRight

lemma FullDataTree.toLeafDataTree_getValueAtIndex {s} {α : Type}
    (tree : FullDataTree α s) (idx : SkeletonLeafIndex s) :
    tree.toLeafDataTree.getValueAtIndex idx =
      tree.getValueAtIndex idx.toNodeIndex := by
  -- This is supposed to be the kind of thing `Canonical` is good at,
  -- but I can't get it to work on my machine
  sorry

/-- Get the root value of a InternalDataTree. -/
def FullDataTree.getRootValue {s} {α : Type} (tree : FullDataTree α s) :=
  tree.getValueAtIndex (getRootIndex s)

@[simp]
lemma FullDataTree.internal_getRootValue {s_left s_right : Skeleton} {α : Type}
    (value : α) (left : FullDataTree α s_left) (right : FullDataTree α s_right) :
    (FullDataTree.internal value left right).getRootValue =
      value := by
  rfl

@[simp] lemma FullDataTree.internal_getLeftSubtree {s_left s_right : Skeleton} {α : Type}
    (value : α) (left : FullDataTree α s_left) (right : FullDataTree α s_right) :
    (FullDataTree.internal value left right).getLeftSubtree = left := by
  rfl

@[simp] lemma FullDataTree.internal_getRightSubtree {s_left s_right : Skeleton} {α : Type}
    (value : α) (left : FullDataTree α s_left) (right : FullDataTree α s_right) :
    (FullDataTree.internal value left right).getRightSubtree = right := by
  rfl

lemma SkeletonNodeIndex.parent_of_depth_zero {s : Skeleton}
    (idx : SkeletonNodeIndex s) (h : idx.depth = 0) :
    parent idx = none := by
  cases idx with
  | ofLeaf => rfl
  | ofInternal => rfl
  | ofLeft idxLeft =>
    unfold depth at h
    simp_all
  | ofRight idxRight =>
    unfold depth at h
    simp_all


/--
Given a `Skeleton`, and a node index of the skeleton,
return a list of node indices which are the ancestors of the node,
starting with the root node,
working down to the node itself.
-/
def SkeletonNodeIndex.findAncestors {s : Skeleton} (idx : SkeletonNodeIndex s) :
    List (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => [SkeletonNodeIndex.ofLeaf]
  | SkeletonNodeIndex.ofInternal => [SkeletonNodeIndex.ofInternal]
  | SkeletonNodeIndex.ofLeft idxLeft =>
    .ofInternal :: ((idxLeft.findAncestors)).map (SkeletonNodeIndex.ofLeft)
  | SkeletonNodeIndex.ofRight idxRight =>
    .ofInternal :: ((idxRight.findAncestors)).map (SkeletonNodeIndex.ofRight)

/--
Given a `Skeleton`,
and a leaf index of the skeleton,
return a list of node indices which are the ancestors of the leaf.
-/
def findAncestors {s : Skeleton} (idx : SkeletonLeafIndex s) : List (SkeletonNodeIndex s) :=
  SkeletonNodeIndex.findAncestors idx.toNodeIndex

/--
Return the sibling node index of a given `SkeletonNodeIndex`. Or `none` if the node is the root
-/
def SkeletonNodeIndex.findSibling {s : Skeleton} (idx : SkeletonNodeIndex s) :
    Option (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => none
  | SkeletonNodeIndex.ofInternal => none
  | @SkeletonNodeIndex.ofLeft left right idxLeft =>
    match idxLeft with
    | SkeletonNodeIndex.ofLeaf => some (getRootIndex right).ofRight
    | SkeletonNodeIndex.ofInternal => some (getRootIndex right).ofRight
    | SkeletonNodeIndex.ofLeft idxLeftLeft =>
      idxLeftLeft.ofLeft.findSibling.map (SkeletonNodeIndex.ofLeft)
    | SkeletonNodeIndex.ofRight idxLeftRight =>
      idxLeftRight.ofRight.findSibling.map (SkeletonNodeIndex.ofLeft)
  | @SkeletonNodeIndex.ofRight left right idxRight =>
    match idxRight with
    | SkeletonNodeIndex.ofLeaf => some (getRootIndex left).ofLeft
    | SkeletonNodeIndex.ofInternal => some (getRootIndex left).ofLeft
    | SkeletonNodeIndex.ofLeft idxRightLeft =>
      idxRightLeft.ofLeft.findSibling.map (SkeletonNodeIndex.ofRight)
    | SkeletonNodeIndex.ofRight idxRightRight =>
      idxRightRight.ofRight.findSibling.map (SkeletonNodeIndex.ofRight)

/-- Find the siblings of the ancestors of a node -/
def SkeletonNodeIndex.findUncles {s : Skeleton} (idx : SkeletonNodeIndex s) :
    List (SkeletonNodeIndex s) := (idx.findAncestors.filterMap (fun idx => idx.findSibling))


/--
Returns, for a particular FullDataTree,
the set of all query-responses that have been made to the oracle to construct the tree.
Note that technically, this can have multiple responses for the same query,
even though that cannot happen in a genuine tree construction.
-/
def FullDataTree.toQueryCacheSet {s : BinaryTree.Skeleton} {α : Type} (tree : FullDataTree α s) :
    Set ((α × α) × α) :=
  match tree with
  | FullDataTree.leaf a => ∅
  | FullDataTree.internal value left right =>
    let leftCache := left.toQueryCacheSet
    let rightCache := right.toQueryCacheSet
    insert ((left.getRootValue, right.getRootValue), value) (leftCache ∪ rightCache)

/--
A `FullDataTree` is self-consistent if for any locations in the tree,
if the childrenof the locations have the same values,
then the locations themselves must have the same value.
-/
def FullDataTree.isSelfConsistent {s : BinaryTree.Skeleton} {α : Type}
    (tree : FullDataTree α s) : Prop :=
  ∀ d r1 r2,
    ((d, r1) ∈ tree.toQueryCacheSet
    ∧ (d, r2) ∈ tree.toQueryCacheSet)
    → r1 = r2

@[simp]
lemma FullDataTree.leaf_toQueryCacheSet {α} (a : α) :
    (FullDataTree.leaf a).toQueryCacheSet = ∅ := by
  rfl

@[simp]
lemma FullDataTree.leaf_toQueryCacheSet' {a} (tree : FullDataTree a Skeleton.leaf) :
    tree.toQueryCacheSet = ∅ := by
  cases tree with
  | leaf a' =>
    simp

@[simp]
lemma FullDataTree.internal_toQueryCacheSet {α} {s1 s2 : BinaryTree.Skeleton}
    (value : α) (left : FullDataTree α s1) (right : FullDataTree α s2) :
    (FullDataTree.internal value left right).toQueryCacheSet =
      insert
        ((left.getRootValue, right.getRootValue), value)
        (left.toQueryCacheSet ∪ right.toQueryCacheSet) := by
  rfl

lemma FullDataTree.getLeftSubtree_toQueryCacheSet_subset {α} {s_left s_right : BinaryTree.Skeleton}
    (tree : FullDataTree α (BinaryTree.Skeleton.internal s_left s_right)) :
    tree.getLeftSubtree.toQueryCacheSet ⊆ tree.toQueryCacheSet := by
  sorry

lemma FullDataTree.getRightSubtree_toQueryCacheSet_subset {α} {s_left s_right : BinaryTree.Skeleton}
    (tree : FullDataTree α (BinaryTree.Skeleton.internal s_left s_right)) :
    tree.getRightSubtree.toQueryCacheSet ⊆ tree.toQueryCacheSet := by
  sorry

lemma FullDataTree.getRootValue_mem_toQueryCacheSet {α} {s_left s_right : BinaryTree.Skeleton}
    (left_tree : FullDataTree α s_left)
    (right_tree : FullDataTree α s_right)
    (a b)
     :
    ((left_tree.getRootValue, right_tree.getRootValue), a) ∈
      (FullDataTree.internal b left_tree right_tree).toQueryCacheSet ↔ a = b := by
  -- TODO needs self-consistency
  constructor
  · intro h_mem

    sorry
  · intro h_eq
    rw [h_eq]
    sorry

section Equivalences

/-!
## Equivalences

This section contains theorems about equivalences between different indexing types
and data structures, as mentioned in the TODOs.
-/

/-- Equivalence between node indices and the sum of internal and leaf indices -/
def skeletonNodeIndex_equiv_sum (s : Skeleton) :
    SkeletonNodeIndex s ≃ SkeletonInternalIndex s ⊕ SkeletonLeafIndex s := by
  sorry

/-- Equivalence between full data trees and the product of internal and leaf data trees -/
def fullDataTree_equiv_product {α : Type} (s : Skeleton) :
    FullDataTree α s ≃ InternalDataTree α s × LeafDataTree α s := by
  sorry

/-- Alternative formulation: FullDataTree as a function from the skeleton -/
def FullDataTreeAsFunction (α : Type) (s : Skeleton) : Type :=
  SkeletonNodeIndex s → α

/-- Equivalence between FullDataTree and function representation -/
def fullDataTree_equiv_function {α : Type} (s : Skeleton) :
    FullDataTree α s ≃ FullDataTreeAsFunction α s := by
  sorry

/-- InternalDataTree as a function from internal indices -/
def InternalDataTreeAsFunction (α : Type) (s : Skeleton) : Type :=
  SkeletonInternalIndex s → α

/-- Equivalence between InternalDataTree and function representation -/
def internalDataTree_equiv_function {α : Type} (s : Skeleton) :
    InternalDataTree α s ≃ InternalDataTreeAsFunction α s := by
  sorry

/-- LeafDataTree as a function from leaf indices -/
def LeafDataTreeAsFunction (α : Type) (s : Skeleton) : Type :=
  SkeletonLeafIndex s → α

/-- Equivalence between LeafDataTree and function representation -/
def leafDataTree_equiv_function {α : Type} (s : Skeleton) :
    LeafDataTree α s ≃ LeafDataTreeAsFunction α s := by
  sorry

/-- Using the function representations, the product equivalence follows algebraically -/
def fullDataTree_equiv_product_via_functions {α : Type} (s : Skeleton) :
    FullDataTreeAsFunction α s ≃ InternalDataTreeAsFunction α s × LeafDataTreeAsFunction α s := by
  sorry

end Equivalences

section map

def FullDataTree.map {α β : Type} (f : α → β) {s : Skeleton}
    (tree : FullDataTree α s) : FullDataTree β s :=
  match tree with
  | FullDataTree.leaf value => FullDataTree.leaf (f value)
  | FullDataTree.internal value left right =>
    FullDataTree.internal (f value) (left.map f) (right.map f)

lemma FullDataTree.map_leaf {α β} (f : α → β) (a : α) :
    (FullDataTree.leaf a).map f = FullDataTree.leaf (f a) := by
  rfl

lemma FullDataTree.map_internal {α β} {s_left s_right : Skeleton}
    (f : α → β) (value : α) (left : FullDataTree α s_left) (right : FullDataTree α s_right) :
    (FullDataTree.internal value left right).map f =
      FullDataTree.internal (f value) (left.map f) (right.map f) := by
  rfl

def LeafDataTree.map {α β : Type} (f : α → β) {s : Skeleton}
    (tree : LeafDataTree α s) : LeafDataTree β s :=
  match tree with
  | LeafDataTree.leaf value => LeafDataTree.leaf (f value)
  | LeafDataTree.internal left right =>
    LeafDataTree.internal (left.map f) (right.map f)

lemma LeafDataTree.map_leaf {α β} (f : α → β) (a : α) :
    (LeafDataTree.leaf a).map f = LeafDataTree.leaf (f a) := by
  rfl

lemma LeafDataTree.map_internal {α β} {s_left s_right : Skeleton}
    (f : α → β) (left : LeafDataTree α s_left) (right : LeafDataTree α s_right) :
    (LeafDataTree.internal left right).map f =
      LeafDataTree.internal (left.map f) (right.map f) := by
  rfl

def FullDataTree.map_getRootValue {α β : Type} {s : Skeleton}
    (f : α → β) (tree : FullDataTree α s) :
    (tree.map f).getRootValue = f (tree.getRootValue) := by
  match tree with
  | FullDataTree.leaf value => rfl
  | FullDataTree.internal value left right =>
    rfl

end map

section ComposeBuild

/-!
## Build

This section contains theorems about building full trees from leaf trees.
-/

def LeafDataTree.composeBuild {α : Type} {s : Skeleton} (leaf_data_tree : LeafDataTree α s)
    (compose : α → α → α) :
    FullDataTree α s :=
  match s, leaf_data_tree with
  | Skeleton.leaf, LeafDataTree.leaf value =>
    FullDataTree.leaf value
  | Skeleton.internal s_left s_right, LeafDataTree.internal left right =>
    let left_tree := LeafDataTree.composeBuild left compose
    let right_tree := LeafDataTree.composeBuild right compose
    FullDataTree.internal
      (compose left_tree.getRootValue right_tree.getRootValue)
      left_tree
      right_tree

lemma LeafDataTree.composeBuild_leaf {α} (a : α)
    (compose : α → α → α) :
    (LeafDataTree.leaf a).composeBuild compose = FullDataTree.leaf a := by
  rfl

lemma LeafDataTree.composeBuild_internal {α} {s_left s_right : Skeleton}
    (left : LeafDataTree α s_left) (right : LeafDataTree α s_right)
    (compose : α → α → α) :
    (LeafDataTree.internal left right).composeBuild compose =
      FullDataTree.internal
        (compose (left.composeBuild compose).getRootValue (right.composeBuild compose).getRootValue)
        (left.composeBuild compose)
        (right.composeBuild compose) := by
  rfl

lemma LeafDataTree.composeBuild_getRootValue {α} {s_left s_right : Skeleton}
    (left : LeafDataTree α s_left) (right : LeafDataTree α s_right)
    (compose : α → α → α) :
    ((LeafDataTree.internal left right).composeBuild compose).getRootValue =
      compose (left.composeBuild compose).getRootValue (right.composeBuild compose).getRootValue := by
  rfl

def Option.doubleBind {α β γ : Type} (f : α → β → Option γ)
    (x : Option α) (y : Option β) : Option γ :=
  match x, y with
  | none, _ => none
  | _, none => none
  | some a, some b => f a b

def Option.doubleBind_v2 {α β γ : Type} (f : α → β → Option γ)
    (x : Option α) (y : Option β) : Option γ := do
  let a ← x
  let b ← y
  f a b

def Option.doubleBind_v3 {α β γ : Type} (f : α → β → Option γ)
    (x : Option α) (y : Option β) : Option γ := do f (← x) (← y)

def LeafDataTree.optionComposeBuild {α : Type} {s : Skeleton} (leaf_data_tree : LeafDataTree α s)
    (compose : α → α → Option α) :
    FullDataTree (Option α) s :=
  (leaf_data_tree.map (.some)).composeBuild (Option.doubleBind compose)

def Option.some_eq_doubleBind {α β γ : Type} (f : α → β → Option γ) (a) (b) (out : γ) :
    some out = Option.doubleBind f a b ↔
    ∃ a' b', a = some a' ∧ b = some b' ∧ f a' b' = some out := by
  sorry


end ComposeBuild

end BinaryTree
