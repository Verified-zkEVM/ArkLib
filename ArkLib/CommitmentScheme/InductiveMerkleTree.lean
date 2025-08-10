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
import ArkLib.CommitmentScheme.BinaryTree
import ArkLib.ToVCVio.Oracle

/-!
# Inductive Merkle Trees

This file implements Merkle Trees. In contrast to the other Merkle tree implementation in
`ArkLib.CommitmentScheme.MerkleTree`, this one is defined inductively.

## Notes & TODOs

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


/-- Build the full Merkle tree, returning the tree populated with data on all its nodes -/
def buildMerkleTree {s} (leaf_tree : LeafDataTree α s) : OracleComp (spec α) (FullDataTree α s) :=
  match leaf_tree with
  | LeafDataTree.leaf a => do return (FullDataTree.leaf a)
  | LeafDataTree.internal left right => do
    let leftTree ← buildMerkleTree left
    let rightTree ← buildMerkleTree right
    let rootHash ← singleHash α leftTree.getRootValue rightTree.getRootValue
    return FullDataTree.internal rootHash leftTree rightTree

/--
A functional form of merkle tree construction, that doesn't depend on the monad.
This receives an explicit hash function
-/
def buildMerkleTree_with_hash {s} (leaf_tree : LeafDataTree α s) (hashFn : α → α → α) :
    (FullDataTree α s) :=
  match leaf_tree with
  | LeafDataTree.leaf a => FullDataTree.leaf a
  | LeafDataTree.internal left right =>
    let leftTree := buildMerkleTree_with_hash left hashFn
    let rightTree := buildMerkleTree_with_hash right hashFn
    let rootHash := hashFn (leftTree.getRootValue) (rightTree.getRootValue)
    FullDataTree.internal rootHash leftTree rightTree

/--
Running the monadic version of `buildMerkleTree` with an oracle function `f`
is equivalent to running the functional version of `buildMerkleTree_with_hash`
with the same oracle function.
-/
lemma runWithOracle_buildMerkleTree {s} (leaf_data_tree : LeafDataTree α s) (f) :
    (runWithOracle f (buildMerkleTree leaf_data_tree))
    = buildMerkleTree_with_hash leaf_data_tree fun (left right : α) =>
      (f () ⟨left, right⟩) := by
  induction s with
  | leaf =>
    match leaf_data_tree with
    | LeafDataTree.leaf a =>
      unfold buildMerkleTree
      simp only [runWithOracle_pure, buildMerkleTree_with_hash]
  | internal s_left s_right left_ih right_ih =>
    match leaf_data_tree with
    | LeafDataTree.internal left right =>
      unfold buildMerkleTree
      simp [left_ih, right_ih, runWithOracle_bind]
      rfl

/--
Generate a Merkle proof for a leaf at a given idx
The proof consists of the sibling hashes needed to recompute the root.
-/
def generateProof {s} (cache_tree : FullDataTree α s) :
    BinaryTree.SkeletonLeafIndex s → List α
  | .ofLeaf => []
  | .ofLeft idxLeft =>
    (cache_tree.getRightSubtree).getRootValue ::
      (generateProof cache_tree.getLeftSubtree idxLeft)
  | .ofRight idxRight =>
    (cache_tree.getLeftSubtree).getRootValue ::
      (generateProof cache_tree.getRightSubtree idxRight)

@[simp]
theorem generateProof_ofLeaf {α : Type} (cache_tree : FullDataTree α Skeleton.leaf) :
    generateProof cache_tree SkeletonLeafIndex.ofLeaf = [] := by
  rfl

@[simp]
theorem generateProof_leaf {α : Type} (a : α) (idx) :
    generateProof (FullDataTree.leaf a) idx = [] := by
  cases idx with
  | ofLeaf => rfl

@[simp]
theorem generateProof_ofLeft {α : Type} {sleft sright : Skeleton}
    (cache_tree : FullDataTree α (Skeleton.internal sleft sright))
    (idxLeft : SkeletonLeafIndex sleft) :
    generateProof cache_tree (BinaryTree.SkeletonLeafIndex.ofLeft idxLeft) =
      (cache_tree.getRightSubtree).getRootValue ::
        (generateProof cache_tree.getLeftSubtree idxLeft) := by
  rfl

@[simp]
theorem generateProof_ofRight {α : Type} {sleft sright : Skeleton}
    (cache_tree : FullDataTree α (Skeleton.internal sleft sright))
    (idxRight : SkeletonLeafIndex sright) :
    generateProof cache_tree (BinaryTree.SkeletonLeafIndex.ofRight idxRight) =
      (cache_tree.getLeftSubtree).getRootValue ::
        (generateProof cache_tree.getRightSubtree idxRight) := by
  rfl

/--
Given a leaf index, a leaf value at that index, and putative proof,
returns the hash that would be the root of the tree if the proof was valid.
i.e. the hash obtained by combining the leaf in sequence with each member of the proof,
according to its index.
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

/--
A functional version of `getPutativeRoot` that does not depend on the monad.
It receives an explicit hash function `hashFn` that combines two hashes into one.
And recursively calls itself down the tree.
-/
def getPutativeRoot_with_hash {s} (idx : BinaryTree.SkeletonLeafIndex s)
    (leafValue : α) (proof : List α) (hashFn : α → α → α) : α :=
  match proof with
  | [] => leafValue -- If no proof, the root is just the leaf value
  | siblingBelowRootHash :: restProof =>
    match idx with
    | BinaryTree.SkeletonLeafIndex.ofLeaf =>
      -- This indicates that the proof is longer than the depth of the tree, which is invalid.
      -- A more well-typed version using `Vector` might prevent this.
      -- For now, we just return the leaf value.
      leafValue
    | BinaryTree.SkeletonLeafIndex.ofLeft idxLeft =>
      -- Recursively get the hash of the ancestor of the leaf which is just below the root
      hashFn (getPutativeRoot_with_hash idxLeft leafValue restProof hashFn) siblingBelowRootHash
    | BinaryTree.SkeletonLeafIndex.ofRight idxRight =>
      -- Recursively get the hash of the ancestor of the leaf which is just below the root
      hashFn siblingBelowRootHash (getPutativeRoot_with_hash idxRight leafValue restProof hashFn)

/--
Running the monadic version of `getPutativeRoot` with an oracle function `f`,
it is equivalent to running the functional version of `getPutativeRoot_with_hash`
-/
lemma runWithOracle_getPutativeRoot {s} (idx : BinaryTree.SkeletonLeafIndex s)
    (leafValue : α) (proof : List α) (f) :
    (runWithOracle f (getPutativeRoot idx leafValue proof))
    = getPutativeRoot_with_hash idx leafValue proof fun (left right : α) =>
      (f () ⟨left, right⟩) := by
  induction proof generalizing s with
  | nil =>
    unfold getPutativeRoot
    simp only [runWithOracle_pure, getPutativeRoot_with_hash]
  | cons siblingBelowRootHash restProof ih =>
    unfold getPutativeRoot
    cases s with
    | leaf =>
      cases idx with
      | ofLeaf =>
        rfl
    | internal s_left s_right =>
      cases idx with
      | ofLeft idxLeft =>
        simp [runWithOracle_bind, ih]
        rfl
      | ofRight idxRight =>
        simp only [runWithOracle_bind, ih]
        rfl

end

/--
Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
`root`.
Works by computing the putative root based on the branch, and comparing that to the actual root.
Outputs `failure` if the proof is invalid.
-/
def verifyProof {α} [DecidableEq α] {s}
    (idx : BinaryTree.SkeletonLeafIndex s) (leafValue : α) (rootValue : α)
    (proof : List α) : OracleComp (spec α) Unit := do
  let putative_root ← getPutativeRoot idx leafValue proof
  guard (putative_root = rootValue)

/--
A functional form of the completeness theorem for Merkle trees.
This references the functional versions of `getPutativeRoot` and `buildMerkleTree_with_hash`
-/
theorem functional_completeness (α : Type) {s : Skeleton}
  (idx : SkeletonLeafIndex s)
  (leaf_data_tree : LeafDataTree α s)
  (hash : α → α → α) :
  (getPutativeRoot_with_hash
    idx
    (leaf_data_tree.getValueAtIndex idx)
    (generateProof
      (buildMerkleTree_with_hash leaf_data_tree hash) idx)
    (hash)) =
  (buildMerkleTree_with_hash leaf_data_tree hash).getRootValue := by
  induction s with
  | leaf =>
    match leaf_data_tree with
    | LeafDataTree.leaf a =>
      simp
      unfold buildMerkleTree_with_hash
      simp
      unfold getPutativeRoot_with_hash
      rfl
  | internal s_left s_right left_ih right_ih =>
    match leaf_data_tree with
    | LeafDataTree.internal left right =>
      unfold buildMerkleTree_with_hash
      cases idx with
      | ofLeft idxLeft =>
        unfold getPutativeRoot_with_hash
        simp [left_ih]
      | ofRight idxRight =>
        unfold getPutativeRoot_with_hash
        simp [right_ih]

/--
Completeness theorem for Merkle trees.

The proof proceeds by reducing to the functional completeness theorem by a theorem about
the OracleComp monad,
and then applying the functional version of the completeness theorem.
-/
theorem completeness [DecidableEq α] [SelectableType α] {s}
    (leaf_data_tree : LeafDataTree α s) (idx : BinaryTree.SkeletonLeafIndex s)
    (preexisting_cache : (spec α).QueryCache) :
    (((do
      let cache ← buildMerkleTree leaf_data_tree
      let proof := generateProof cache idx
      let _ ← verifyProof idx (leaf_data_tree.getValueAtIndex idx) (cache.getRootValue) proof
      ).simulateQ (randomOracle)).run preexisting_cache).neverFails := by
  -- An OracleComp is never failing on any preexisting cache
  -- if i never fails when run with any oracle function.
  revert preexisting_cache
  rw [randomOracle_neverFails_iff_runWithOracle_neverFails]
  -- Call this hash function `f`
  intro f
  -- Simplify
  simp_rw [verifyProof, guard_eq, bind_pure_comp, id_map', runWithOracle_bind,
    runWithOracle_buildMerkleTree, runWithOracle_getPutativeRoot]
  simp only [apply_ite, runWithOracle_pure, runWithOracle_failure, Option.bind_eq_bind,
    Option.bind_some, Option.isSome_some, Option.isSome_none, Bool.if_false_right, Bool.and_true,
    decide_eq_true_eq]
  exact functional_completeness α idx leaf_data_tree fun left right ↦ f () (left, right)

end InductiveMerkleTree
