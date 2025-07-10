/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ArkLib.Data.Math.Basic
import ArkLib.CommitmentScheme.Basic
import Mathlib.Data.Vector.Snoc

/-!
# Inductive Merkle Trees

This file implements Merkle Trees. In contrast to the other Merkle tree implementation in
`ArkLib.CommitmentScheme.MerkleTree`, this one is defined inductively.

## Notes & TODOs

### Binary Tree API

- Split this BinaryTree API to a new file
- More API about equivlances between
  - `SkeletonNodeIndex` ≃ `SkeletonInternalIndex` ⊕ `SkeletonLeafIndex`
  - analogously
  - `FullDataTree α ≃ InternalDataTree α × LeafDataTree α`
  - OR EVEN BETTER:
    - Redefine `FullDataTree`, `InternalDataTree`, `LeafDataTree`
      in terms of functions from `Skeleton`,
      so that this equivalence follows immediately from the above by algebraic data types.
- Replace `List`s with `FreeSubgroup` for ancestors?
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
- Define `Lattice` strutcure of trees
  - a susbset relation on trees, mappings of indices to indices of supertrees
- Define a datatype for indices of trees agnostic of the skeleton,
  - This type has an equivalence to lists of bools,
  - and maps from the the other indexing types.

### More Things needed for basic Merkle Trees

- Collision Lemma (See SNARGs book 18.3)
  - (this is really not a lemma about oracles, so it could go with the binary tree API)

### More Complicated Merkle Trees

We want this treatment to be as comprehensive as possible. In particular, our formalization
should (eventually) include all complexities such as the following:

- Multi-instance extraction & simulation
- Dealing with arbitrary trees (may have arity > 2, or is not complete)
- Path pruning optimization for multi-leaf proofs



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

/-- Get the root value of a InternalDataTree. -/
def LeafDataTree.getValueAtIndex {s} {α : Type}
    (tree : LeafDataTree α s) (idx : SkeletonLeafIndex s) : α :=
  match tree, idx with
  | LeafDataTree.leaf value, SkeletonLeafIndex.ofLeaf => value
  | LeafDataTree.internal left _, SkeletonLeafIndex.ofLeft idxLeft =>
    LeafDataTree.getValueAtIndex left idxLeft
  | LeafDataTree.internal _ right, SkeletonLeafIndex.ofRight idxRight =>
    LeafDataTree.getValueAtIndex right idxRight

/--
A binary tree with values stored at both leaves and internal nodes.
-/
inductive FullDataTree (α : Type) : Skeleton → Type
  | leaf (value : α) : FullDataTree α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : FullDataTree α left)
      (rightData : FullDataTree α right) :
      FullDataTree α (Skeleton.internal left right)

def FullDataTree.getLeftSubtree {α : Type} {s_left s_right : Skeleton}
    (tree : FullDataTree α (Skeleton.internal s_left s_right)) :
    FullDataTree α s_left :=
  match tree with
  | FullDataTree.internal _ left right =>
    left

def FullDataTree.getRightSubtree {α : Type} {s_left s_right : Skeleton}
    (tree : FullDataTree α (Skeleton.internal s_left s_right)) :
    FullDataTree α s_right :=
  match tree with
  | FullDataTree.internal _ left right =>
    right

def FullDataTree.toLeafDataTree {α : Type} {s : Skeleton}
    (tree : FullDataTree α s) : LeafDataTree α s :=
  match tree with
  | FullDataTree.leaf value => LeafDataTree.leaf value
  | FullDataTree.internal _ left right =>
    LeafDataTree.internal (left.toLeafDataTree) (right.toLeafDataTree)

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
    leftCache ∪ rightCache ∪ Set.singleton ((left.getRootValue, right.getRootValue), value)

@[simp]
lemma FullDataTree.leaf_toQueryCacheSet {α} (a : α) :
    (FullDataTree.leaf a).toQueryCacheSet = ∅ := by
  rfl

lemma FullDataTree.internal_toQueryCacheSet {α} {s1 s2 : BinaryTree.Skeleton}
    (value : α) (left : FullDataTree α s1) (right : FullDataTree α s2) :
    (FullDataTree.internal value left right).toQueryCacheSet =
      left.toQueryCacheSet ∪ right.toQueryCacheSet ∪
      {((left.getRootValue, right.getRootValue), value)} := by
  rfl

end BinaryTree

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable (α : Type)

/-- Define the domain & range of the (single) oracle needed for constructing a Merkle tree with
    elements from some type `α`.

  We may instantiate `α` with `BitVec n` or `Fin (2 ^ n)` to construct a Merkle tree for boolean
  vectors of length `n`. -/
@[reducible]
def spec : OracleSpec Unit := fun _ => (α × α, α)

@[simp]
lemma domain_def : (spec α).domain () = (α × α) := rfl

@[simp]
lemma range_def : (spec α).range () = α := rfl

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Example: a single hash computation -/
def singleHash (left : α) (right : α) : OracleComp (spec α) α := do
  let out ← query (spec := spec α) () ⟨left, right⟩
  return out

variable {α : Type}


-- /-- Find the path from root to a leaf with the given value. -/
-- def findPath [DecidableEq α] (a : α) : BinaryTree α → Option (List Bool)
--   | BinaryTree.nil => none
--   | BinaryTree.node _ left right =>
--     match findPath a left with
--     | some path => some (false :: path)
--     | none =>
--       match findPath a right with
--       | some path => some (true :: path)
--       | none => none

-- /-- Helper function to get the proof for a value at a given path. -/
-- def getProofHelper [DecidableEq α] : List Bool → BinaryTree α → List α
--   | _, BinaryTree.nil => []
--   | _, BinaryTree.leaf _ => []
--   | [], BinaryTree.node _ _ _ => []
--   | false :: rest, BinaryTree.node _ l r =>
--     match getRoot r with
--     | none => getProofHelper rest l
--     | some v => v :: getProofHelper rest l
--   | true :: rest, BinaryTree.node _ l r =>
--     match getRoot l with
--     | none => getProofHelper rest r
--     | some v => v :: getProofHelper rest r

def buildMerkleTree_with_hash {s} (leaf_tree : LeafDataTree α s) (hashFn : α → α → α) :
    (FullDataTree α s) :=
  match leaf_tree with
  | LeafDataTree.leaf a => FullDataTree.leaf a
  | LeafDataTree.internal left right =>
    let leftTree := buildMerkleTree_with_hash left hashFn
    let rightTree := buildMerkleTree_with_hash right hashFn
    let rootHash := hashFn (leftTree.getRootValue) (rightTree.getRootValue)
    FullDataTree.internal rootHash leftTree rightTree

/-- Build the full Merkle tree, returning the cache -/
def buildMerkleTree {s} (leaf_tree : LeafDataTree α s) : OracleComp (spec α) (FullDataTree α s) :=
  match leaf_tree with
  | LeafDataTree.leaf a => do return (FullDataTree.leaf a)
  | LeafDataTree.internal left right => do
    let leftTree ← buildMerkleTree left
    let rightTree ← buildMerkleTree right
    let rootHash ← singleHash α leftTree.getRootValue rightTree.getRootValue
    return FullDataTree.internal rootHash leftTree rightTree

/-- Generate a Merkle proof for a leaf at a given idx
    The proof consists of the sibling hashes needed to recompute the root.

-/
def generateProof {s} (cache_tree : FullDataTree α s) (idx : BinaryTree.SkeletonLeafIndex s) :
    List α :=
  (idx.toNodeIndex.findUncles.map (fun siblingIdx =>
    cache_tree.getValueAtIndex siblingIdx))

@[simp]
theorem generateProof_ofLeaf {α : Type} (cache_tree : FullDataTree α Skeleton.leaf) :
    generateProof cache_tree SkeletonLeafIndex.ofLeaf = [] := by
  rfl

@[simp]
theorem generateProof_ofLeft {α : Type} {sleft sright : Skeleton}
    (cache_tree : FullDataTree α (Skeleton.internal sleft sright))
    (idxLeft : SkeletonLeafIndex sleft) :
    generateProof cache_tree (BinaryTree.SkeletonLeafIndex.ofLeft idxLeft) =
      (cache_tree.getRightSubtree).getRootValue ::
        (generateProof cache_tree.getLeftSubtree idxLeft) := by
  sorry

@[simp]
theorem generateProof_ofRight {α : Type} {sleft sright : Skeleton}
    (cache_tree : FullDataTree α (Skeleton.internal sleft sright))
    (idxRight : SkeletonLeafIndex sright) :
    generateProof cache_tree (BinaryTree.SkeletonLeafIndex.ofRight idxRight) =
      (cache_tree.getLeftSubtree).getRootValue ::
        (generateProof cache_tree.getRightSubtree idxRight) := by
  sorry

/--
Given a leaf index, a leaf value at that index, and putative proof,
returns the hash that would be the root of the tree if the proof was valid.
i.e. the hash obtained by combining the leaf in sequence with each member of the proof,
according to its index.
-- TODO should this, instead of a List, take a Vector of length idx.depth?
-/
def getPutativeRoot {s} (idx : BinaryTree.SkeletonLeafIndex s) (leafValue : α)
    (proof : List α) : OracleComp (spec α) α :=
  match proof with
  | [] => return leafValue -- If no proof, the root is just the leaf value
  | siblingBelowRootHash :: restProof => do
    match idx with
    | BinaryTree.SkeletonLeafIndex.ofLeaf =>
      -- This indicates that the proof is longer than the depth of the tree, which is invalid.
      -- A more well-typed version using `Vector` might prevent this.
      -- For now, we just return the leaf value.
      return leafValue
    | BinaryTree.SkeletonLeafIndex.ofLeft idxLeft =>
      -- Recursively get the hash of the ancestor of the leaf which is just below the root
      let ancestorBelowRootHash ← getPutativeRoot idxLeft leafValue restProof
      singleHash α ancestorBelowRootHash siblingBelowRootHash
    | BinaryTree.SkeletonLeafIndex.ofRight idxRight =>
      -- Recursively get the hash of the ancestor of the leaf which is just below the root
      let ancestorBelowRootHash ← getPutativeRoot idxRight leafValue restProof
      singleHash α siblingBelowRootHash ancestorBelowRootHash

/-- Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
  `root`.
  Works by computing the putative root based on the branch, and comparing that to the actual root.
  Outputs `failure` if the proof is invalid. -/
def verifyProof [DecidableEq α] {s}
    (idx : BinaryTree.SkeletonLeafIndex s) (leafValue : α) (rootValue : α)
    (proof : List α) : OracleComp (spec α) Unit := do
  let putative_root ← getPutativeRoot idx leafValue proof
  guard (putative_root = rootValue)

theorem singleHash_neverFails [DecidableEq α] [inst_1 : SelectableType α] (left right : α)
    (preexisting_cache : (spec α).QueryCache) :
    ((simulateQ randomOracle (singleHash α left right)).run preexisting_cache).neverFails := by
  unfold singleHash
  simp only [range_def, bind_pure, simulateQ_query,
    unifOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind]
  simp
  cases preexisting_cache () (left, right) with
  | none =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
      StateT.run_modifyGet, Functor.map_map, neverFails_map_iff, neverFails_uniformOfFintype]
  | some u =>
    simp only [StateT.run_pure, neverFails_pure]

theorem buildMerkleTree_neverFails {α : Type} [DecidableEq α] [SelectableType α] {s : Skeleton}
    (leaf_tree : LeafDataTree α s) (preexisting_cache : (spec α).QueryCache) :
    ((simulateQ randomOracle (buildMerkleTree leaf_tree)).run preexisting_cache).neverFails := by
  induction leaf_tree generalizing preexisting_cache with
  | leaf a =>
    unfold buildMerkleTree
    simp only [simulateQ_pure, StateT.run_pure, neverFails_pure]
  | internal left right left_ih right_ih =>
    unfold buildMerkleTree
    simp [simulateQ_bind, StateT.run_bind, neverFails_bind_iff, left_ih, right_ih]
    intro merkle_cache_left query_cache h_mem_support merkle_cache_right query_cache' h_mem_support'
    clear left_ih right_ih
    exact
      singleHash_neverFails merkle_cache_left.getRootValue merkle_cache_right.getRootValue
        query_cache'

theorem getPutativeRoot_neverFails {α : Type} [inst : DecidableEq α] [inst_1 : SelectableType α]
    {s : Skeleton} (idx : SkeletonLeafIndex s) (leafValue : α) (query_cache : (spec α).QueryCache)
    (proof : List α) :
    ((simulateQ randomOracle
            (getPutativeRoot idx leafValue proof)).run
        query_cache).neverFails := by
  induction proof generalizing s idx leafValue query_cache with
  | nil =>
    unfold getPutativeRoot
    simp only [simulateQ_pure, StateT.run_pure, neverFails_pure]
  | cons siblingBelowRootHash restProof ih =>
    unfold getPutativeRoot
    cases s with
    | leaf =>
      cases idx with
      | ofLeaf =>
        -- If the index is a leaf, then the proof is invalid, so we just return the leaf value.
        simp only [simulateQ_pure, StateT.run_pure, neverFails_pure]
    | internal left right =>
      cases idx with
      | ofLeft idxLeft =>
        simp only [simulateQ_bind, StateT.run_bind, neverFails_bind_iff]
        constructor
        · apply ih
        · intro x x_mem
          simp only [Function.comp_apply]
          exact singleHash_neverFails x.1 siblingBelowRootHash x.2
      | ofRight idxRight =>
        simp only [simulateQ_bind, StateT.run_bind, neverFails_bind_iff]
        constructor
        · apply ih
        · intro x x_mem
          simp only [Function.comp_apply]
          exact singleHash_neverFails siblingBelowRootHash x.1 x.2


-- To VCVio
/--
Returns, for a particular oracle's cache,
the set of all (query, response) pairs that have been made to the oracle.
-/
def QueryCache.toSet {ι : Type} {spec : OracleSpec ι} (i : ι) (cache : spec.QueryCache) :
    Set (spec.domain i × spec.range i) :=
  { (q, r) : spec.domain i × spec.range i | cache i q = some r }

@[simp]
lemma QueryCache.toSet_cacheQuery_eq_insert_of_none {ι : Type} {spec : OracleSpec ι}
    [spec.DecidableEq] [DecidableEq ι]
    (i : ι) (cache : spec.QueryCache) (q : spec.domain i) (r : spec.range i)
    (h : cache i q = none) :
    QueryCache.toSet i (cache.cacheQuery i q r) =
      QueryCache.toSet i cache ∪ {(q, r)} := by
  simp only [QueryCache.toSet, OracleSpec.QueryCache.cacheQuery]
  simp
  ext ⟨q', r'⟩
  simp
  rw [Function.update_apply]
  split_ifs with h' <;> simp_all
  exact eq_comm

-- To Mathlib (the symmetric form of preexisting lemma)
@[simp]
theorem Set.eq_insert_self {α : Type} {s : Set α} (a : α) :
    s = insert a s ↔ a ∈ s := by
  rw [← Set.insert_eq_self]
  exact eq_comm

theorem of_mem_singleHash_support {α : Type} [DecidableEq α] [SelectableType α]
    (left right out : α) (preexisting_cache resulting_cache : (spec α).QueryCache)
    (h :
      (out, resulting_cache) ∈
        ((simulateQ randomOracle (singleHash α left right)).run
            preexisting_cache).support
    ) :
    QueryCache.toSet () resulting_cache
    = QueryCache.toSet () preexisting_cache ∪ {((left, right), out)} := by
  unfold singleHash at h
  simp at h
  set pre_out := preexisting_cache () (left, right) with h_mem_pre_out
  clear_value pre_out

  cases pre_out with
  | none =>
    simp_all only []
    simp at h
    subst h
    rw [QueryCache.toSet_cacheQuery_eq_insert_of_none _ _ _ _ h_mem_pre_out.symm]
  | some u =>
    simp_all only []
    simp at h
    rcases h with ⟨rfl, rfl⟩
    simp only [domain_def, range_def, Set.union_singleton]
    symm
    simp
    simp [QueryCache.toSet, h_mem_pre_out]


/--
A theorem that characterizes the support of the `buildMerkleTree` computation.
This is used to prove completeness of the Merkle tree construction.

-- TODO backwards direction
(requires also stating that the merkle_tree_cache is consistent with the
  leaf_data_tree, i.e. that the corresponding leaf values are the same)
-/
theorem of_mem_buildMerkleTree_support {α : Type} [DecidableEq α] [SelectableType α] {s : Skeleton}
    (leaf_data_tree : LeafDataTree α s)
    (merkle_tree_cache) (preexisting_cache resulting_cache : (spec α).QueryCache)
    (h :
     ((merkle_tree_cache, resulting_cache)
        ∈ ((simulateQ randomOracle (buildMerkleTree leaf_data_tree)).run preexisting_cache).support)
    )
    :
    (
      QueryCache.toSet () resulting_cache
      = QueryCache.toSet () preexisting_cache ∪ merkle_tree_cache.toQueryCacheSet
    ) := by
  induction s generalizing preexisting_cache resulting_cache with
  | leaf =>
    cases leaf_data_tree with
    | leaf a =>
      unfold buildMerkleTree at h
      rcases h
      simp [QueryCache.toSet]
  | internal left_skeleton right_skeleton left_ih right_ih =>
    cases leaf_data_tree with
    | internal leftData rightData =>
      unfold buildMerkleTree at h
      simp at h
      rcases h with ⟨merkle_tree_cache_left, query_cache_left, h_left,
        merkle_tree_cache_right, query_cache_right, h_right,
        merkle_tree_cache_final, h_final, h_eq⟩
      rw [← h_eq]
      rw [FullDataTree.internal_toQueryCacheSet]
      specialize left_ih _ _ _ _ h_left
      specialize right_ih _ _ _ _ h_right
      have final_of_mem_singleHash_support := of_mem_singleHash_support _ _ _ _ _ h_final
      simp_rw [←Set.union_assoc]
      rw [<-left_ih, <-right_ih, <- final_of_mem_singleHash_support]


/--
When generateProof runs on a cache that contains all the queries in the merkle tree,
the putative root obtained from the resulting proof is equal to the root value of the cache.
-/
theorem putative_root_eq_merkle_tree_cache_root_of_generate_proof {α : Type}
    [DecidableEq α] [SelectableType α]
    {s : Skeleton} (leaf_data_tree : LeafDataTree α s) (idx : SkeletonLeafIndex s)
    (merkle_tree_cache : FullDataTree α s)
    (preexisting_cache resulting_cache : (spec α).QueryCache)
    (putative_root : α)
    (cache_subset :
      merkle_tree_cache.toQueryCacheSet ⊆ QueryCache.toSet () preexisting_cache)
    -- TODO refactor away this assumption
    (leaf_data_tree_merkle_tree_cache_consistent : leaf_data_tree = merkle_tree_cache.toLeafDataTree
      )
    (mem_support' :
      (putative_root, resulting_cache) ∈
      ((simulateQ randomOracle
        (getPutativeRoot idx
          (leaf_data_tree.getValueAtIndex idx)
          (generateProof merkle_tree_cache idx))).run
        preexisting_cache).support) :
    putative_root = merkle_tree_cache.getRootValue := by
  subst leaf_data_tree_merkle_tree_cache_consistent
  induction s generalizing preexisting_cache resulting_cache with
  | leaf =>
    cases idx with
    | ofLeaf =>
      simp only [generateProof_ofLeaf] at mem_support'
      rcases mem_support' with ⟨rfl, rfl⟩
      unfold FullDataTree.getRootValue getRootIndex
      rw [FullDataTree.toLeafDataTree_getValueAtIndex]
      rfl
  | internal left_skeleton right_skeleton left_ih right_ih =>
    cases idx with
    | ofLeft idxLeft =>
      simp only [generateProof_ofLeft] at mem_support'
      unfold getPutativeRoot at mem_support'
      simp [] at mem_support'
      rcases mem_support' with ⟨putative_root_left, cache_after_left, h_mem_left, h_mem_singleHash⟩

      -- replace mem_support := of_mem_buildMerkleTree_support _ _ _ _ mem_support
      replace h_mem_singleHash := of_mem_singleHash_support _ _ _ _ _ h_mem_singleHash

      sorry
    | ofRight idxRight => sorry

theorem completeness [DecidableEq α] [SelectableType α] {s}
    (leaf_data_tree : LeafDataTree α s) (idx : BinaryTree.SkeletonLeafIndex s)
    (preexisting_cache : (spec α).QueryCache) :
    (((do
      let cache ← buildMerkleTree leaf_data_tree
      let proof := generateProof cache idx
      let _ ← verifyProof idx (leaf_data_tree.getValueAtIndex idx) (cache.getRootValue) proof
      ).simulateQ (randomOracle)).run preexisting_cache).neverFails := by
  simp [neverFails_bind_iff]
  constructor
  · -- buildMerkleTree never fails
    exact buildMerkleTree_neverFails leaf_data_tree preexisting_cache
  · -- verifyProof never fails on the output of generateProof after buildMerkleTree
    intros merkle_tree_cache query_cache h_mem_support
    simp [verifyProof, neverFails_bind_iff]
    constructor
    · -- getPutativeRoot never fails
      exact
        getPutativeRoot_neverFails idx (leaf_data_tree.getValueAtIndex idx) query_cache
          (generateProof merkle_tree_cache idx)
    · -- guard never fails
      intro putative_root query_cache' h_mem_support'
      split_ifs with h
      · -- If the putative root is equal to the root value, then we are done.
        simp
      -- Otherwise, we must derive a contradiction
      simp only [StateT.run_failure, not_neverFails_failure]
      contrapose! h
      have h_cache_subset := of_mem_buildMerkleTree_support leaf_data_tree
        merkle_tree_cache preexisting_cache query_cache h_mem_support
      have cache_subset : merkle_tree_cache.toQueryCacheSet ⊆ QueryCache.toSet () query_cache := by
        rw [h_cache_subset]
        exact Set.subset_union_right
      have consistent_cache_leaves : leaf_data_tree = merkle_tree_cache.toLeafDataTree := by
        -- follows from h_mem_support
        -- factor as a lemma similar to of_mem_buildMerkleTree_support
        sorry
      exact?

end

end InductiveMerkleTree
