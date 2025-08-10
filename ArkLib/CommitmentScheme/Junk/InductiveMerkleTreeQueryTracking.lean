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
  simp only [range_def, bind_pure, simulateQ_query]
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


-- To Mathlib (the symmetric form of preexisting lemma)
@[simp]
theorem Set.eq_insert_self {α : Type} {s : Set α} (a : α) :
    s = insert a s ↔ a ∈ s := by
  rw [← Set.insert_eq_self]
  exact eq_comm

@[ext]
theorem QueryCache.ext {ι : Type} {spec : OracleSpec ι} --[spec.DecidableEq] [DecidableEq ι]
    (cache1 cache2 : spec.QueryCache) (h : ∀ i, cache1 i = cache2 i) :
    cache1 = cache2 := by
  unfold QueryCache at *
  ext x x_1 a
  simp_all only

-- to mathlib
@[simp]
lemma Option.eq_of_forall_eq {α : Type} {o1 o2 : Option α} :
    (∀ a, o1 = some a ↔ o2 = some a) ↔ o1 = o2 := by
  exact Iff.symm Option.ext_iff


@[simp]
theorem mem_singleHash_support_iff {α : Type} [DecidableEq α] [SelectableType α]
    (left right out : α) (preexisting_cache resulting_cache : (spec α).QueryCache) :
    ((out, resulting_cache)
      ∈ ((simulateQ randomOracle (singleHash α left right)).run preexisting_cache).support)
    ↔
    resulting_cache () = Function.update (preexisting_cache ()) (left, right) out
    ∧
    (
      preexisting_cache () (left, right) = none
      ∨
      preexisting_cache () (left, right) = some out
    )
     := by
  unfold singleHash
  simp
  set pre_out := preexisting_cache () (left, right) with h_mem_pre_out
  clear_value pre_out
  cases pre_out with
  | none =>
    simp
    constructor
    · intro h
      rw [<- h]
      ext d r
      simp [Function.update_apply]
      revert r
      simp only [Option.eq_of_forall_eq]
      by_cases h_eq : d = (left, right)
      · simp [h_eq]
        unfold QueryCache.cacheQuery
        simp
      · simp [h_eq]
        unfold QueryCache.cacheQuery
        simp [h_eq]
    · intro h
      ext u d r
      unfold QueryCache.cacheQuery
      revert r
      simp only [Option.eq_of_forall_eq]
      simp
      have : u = () := by exact rfl
      subst this
      rw [h]
  | some u =>
    simp
    constructor
    · intro h
      rcases h with ⟨h_eq, h_mem⟩
      subst h_eq
      simp
      ext d r
      revert r
      simp only [Option.eq_of_forall_eq]
      subst h_mem
      simp [Function.update_apply]
      by_cases h_eq : d = (left, right)
      · simp [h_eq]
        rw [h_mem_pre_out]
      simp [h_eq]
    · intro h
      rcases h with ⟨h_eq, h_mem⟩
      subst h_mem
      simp
      ext u d r
      revert r
      simp only [Option.eq_of_forall_eq]
      simp
      have : u = () := by exact rfl
      subst this
      rw [h_eq]
      simp [Function.update_apply]
      by_cases h_eq : d = (left, right)
      · simp [h_eq]
        rw [h_mem_pre_out]
      simp [h_eq]




section toVCV

/--
If a cache results from a run of a randomOracle query, then it is a supercache of the initial cache
https://github.com/dtumad/VCV-io/pull/71
-/
theorem subcache_of_mem_support' {ι} [DecidableEq ι]
    (my_spec : OracleSpec ι)
    [my_spec.DecidableEq]
    [(i : ι) → SelectableType (my_spec.range i)]
    (i : ι) (t : (my_spec).domain i) (preexisting_cache : (my_spec).QueryCache)
    (a : my_spec.range i)
    (cache : (my_spec).QueryCache)
    (h1 : (a, cache) ∈
        ((randomOracle.impl (query i t)).run preexisting_cache).support)
    (x : my_spec.domain i) (r : my_spec.range i) (h : preexisting_cache i x = some r) :
    cache i x = some r := by
  simp_all only [QueryImpl.withCaching_apply, unifOracle.apply_eq, StateT.run_bind, StateT.run_get,
    pure_bind]
  set result := preexisting_cache i t with h'
  clear_value result
  cases result with
  | none =>
    simp_all only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
      StateT.run_modifyGet, Functor.map_map, support_map, support_uniformOfFintype, Set.image_univ,
      Set.mem_range, Prod.mk.injEq, exists_eq_left]
    subst h1
    simp [QueryCache.cacheQuery_eq_ite_ite]
    simp_all only [ite_eq_right_iff, Option.some.injEq]
    by_cases h_eq : x = t
    · simp [h_eq] at *
      exfalso
      grind only
    · grind
  | some val =>
    simp_all only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]

-- https://github.com/dtumad/VCV-io/pull/71
theorem subcache_of_mem_support.extracted_1_6 {α : Type} [DecidableEq α] [inst: SelectableType α]
    (t : (spec α).domain ()) (preexisting_cache : (spec α).QueryCache) (a : α)
    (cache :
      (spec α).QueryCache) (h1 : (a, cache) ∈
        ((randomOracle.impl (query () t)).run preexisting_cache).support)
    (x1 x2 r : α)
    (h : preexisting_cache () (x1, x2) = some r) : cache () (x1, x2) = some r := by

  exact subcache_of_mem_support' (spec α) () t preexisting_cache a cache h1 (x1, x2) r h

/--
If a final is an outcome of a run with some preexisting cache, then it is a supercache
https://github.com/dtumad/VCV-io/pull/71
-/
theorem subcache_of_mem_support {α β : Type} [DecidableEq α] [SelectableType α]
    (computation : OracleComp (spec α) β)
    (preexisting_cache resulting_cache : (spec α).QueryCache) (b : β)
    (h_mem :
      ((b, resulting_cache) ∈ ((simulateQ randomOracle computation).run preexisting_cache).support)
    ) :
    (∀ d r, preexisting_cache () d = some r → resulting_cache () d = some r) := by

  induction computation using OracleComp.inductionOn generalizing b preexisting_cache resulting_cache with
  | pure x =>
    simp_all only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, domain_def, range_def, implies_true]
  | query_bind i t oa ih =>
    simp_all only [range_def, domain_def, Prod.forall, simulateQ_bind, simulateQ_query,
      StateT.run_bind, Function.comp_apply, support_bind, Set.mem_iUnion, exists_prop, Prod.exists]
    rcases h_mem with
      ⟨a, cache, h1, h2⟩

    specialize ih a cache resulting_cache b h2
    have : ∀ (x1 x2 r : α),
        preexisting_cache () (x1, x2) = some r → cache () (x1, x2) = some r := by
      clear ih h2 b resulting_cache
      exact?

    intros x1 x2 y h
    apply ih
    apply this x1 x2 y h
  | failure =>
    simp_all only [simulateQ_failure, StateT.run_failure, support_failure, Set.mem_empty_iff_false]


/--
A relation that characterizes the cache-access behavior of a computation.

Takes a computation, an output and a cache,
and asserts that the output is the result of running the computation with that cache,
that nothing not in the cache is touched,
and that everything in the cache is touched.
-/
def touchedExactly {α β : Type} [DecidableEq α] [SelectableType α]
    (computation : OracleComp (spec α) β)
    (out : β)
    (cache : (spec α).QueryCache) : Prop :=
  -- I think we can simply phase this as:
  -- The cache is exactly what we can get starting from an empty cache
  ((out, cache) ∈ ((simulateQ randomOracle computation).run ∅).support)

/--
Characterize membership in oracle computation support.

A pair `(b, resulting_cache)` is in the support of running `computation` from `preexisting_cache`
if and only if:
The contents of `resulting_cache` are exactly the contents of `preexisting_cache`
plus the entries that were touched by the computation.

This captures the idea that the computation can produce this output/cache pair,
the cache grows monotonically, and all new entries are justified by the computation.
-/
theorem mem_oracle_support_iff {α β : Type} [DecidableEq α] [SelectableType α]
    [(spec α).DecidableEq]
    (computation : OracleComp (spec α) β)
    (preexisting_cache resulting_cache : (spec α).QueryCache)
    (b : β) :
    ((b, resulting_cache) ∈ ((simulateQ randomOracle computation).run preexisting_cache).support)
    ↔
    (
      -- 2. Running from resulting_cache gives deterministic result
      (∃ touched_cache,
        touchedExactly computation b touched_cache
        ∧
        -- 3. Every touched entry is either in preexisting_cache or newly justified
        ∀ d, ∃ r, resulting_cache () d = some r ↔
          (preexisting_cache () d = some r ∨ touched_cache () d = some r))
    ) := by
  sorry

end toVCV


-- set_option maxHeartbeats 0 in
/--
Characterize membership in buildMerkleTree support

A merkle_tree_cache, resulting_cache pair is in the support of the
  buildMerkleTree on leaf_data_tree simulation starting from preexisting_cache
  iff:

1. The merkle_tree_cache is the result of building a Merkle tree from the leaf_data_tree
using the map supplied by the resulting_cache (suitably lifted to Option types)
2. The resulting_cache is a superset of the preexisting_cache
3. The resulting_cache does not include any entries that are not in either the
preexisting_cache or the merkle_tree_cache.
  1. Equivalently, If an entry is not in the preexisting_cache or the merkle_tree_cache,
  then it is not in the resulting_cache.
  2. Contrapositively, if an entry is in the resulting_cache, then it is either in the
  preexisting_cache or the merkle_tree_cache.
-/
theorem mem_buildMerkleTree_support_iff_v3 {α : Type} [DecidableEq α] [SelectableType α]
    {s : Skeleton}
    (leaf_data_tree : LeafDataTree α s)
    (merkle_tree_cache : FullDataTree α s)
    (preexisting_cache resulting_cache : (spec α).QueryCache) :
    ((merkle_tree_cache, resulting_cache)
      ∈ ((simulateQ randomOracle (buildMerkleTree leaf_data_tree)).run preexisting_cache).support)
    ↔
    (
      (
      -- The merkle_tree_cache is the result of building a Merkle tree from the leaf_data_tree
      -- with the map supplied by the resulting_cache
      merkle_tree_cache.map (Option.some) = LeafDataTree.optionComposeBuild leaf_data_tree
        (fun a b => resulting_cache () (a, b))
      )
      ∧
      -- The resulting_cache is a superset of the preexisting_cache
      -- Note, this is needed for the rverse direction, but in the forward actuallly just a property of support membership of anything, refactor
      (∀ d r,
        preexisting_cache () d = some r → resulting_cache () d = some r)
      ∧
      -- The resulting_cache does not include any entries that are not in either the
      -- preexisting_cache or the merkle_tree_cache
      (∀ d r,
        resulting_cache () d = some r →
        (preexisting_cache () d = some r ∨ (d, r) ∈
          merkle_tree_cache.toQueryCacheSet))
    ) := by
  induction s generalizing preexisting_cache resulting_cache with
  | leaf =>
    cases leaf_data_tree with
    | leaf a =>
      unfold buildMerkleTree
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, domain_def, range_def, FullDataTree.leaf_toQueryCacheSet',
        Set.mem_empty_iff_false, or_false, Prod.forall]
      constructor
      · intro h
        rcases h with ⟨rfl, rfl⟩
        simp only [imp_self, implies_true, and_self, and_true]
        rfl
      · intro h
        rcases h with ⟨h1, h2, h3⟩
        constructor
        · apply FullDataTree.toLeafDataTree_eq_leaf
          simp [LeafDataTree.optionComposeBuild, LeafDataTree.map_leaf, LeafDataTree.composeBuild_leaf] at h1
          sorry -- confident
        · have : ∀ d r,
              resulting_cache () d = some r ↔
              preexisting_cache () d = some r := by
            intro d r
            constructor
            · exact fun a ↦ h3 d.1 d.2 r (h2 d.1 d.2 r (h3 d.1 d.2 r a))
            · exact fun a ↦ h2 d.1 d.2 r (h3 d.1 d.2 r (h2 d.1 d.2 r a))
          -- simp only [Option.eq_of_forall_eq] at this
          ext u d r
          revert r
          simp only [Option.eq_of_forall_eq] at this
          have : u = () := by exact rfl
          subst this
          rw [this]
          exact fun r ↦ Eq.congr_right rfl
  | internal left_skeleton right_skeleton left_ih right_ih =>
    cases leaf_data_tree with
    | internal left_leaf_data right_leaf_data =>
      unfold buildMerkleTree
      simp only [simulateQ_bind, StateT.run_bind]
      simp
      simp [left_ih, right_ih]
      clear left_ih right_ih
      constructor
      · -- Forward direction
        intro h
        rcases h with
          ⟨left_tree, left_cache,
            ⟨h_left_tree_eq_build, h_preexisting_cache_subcache_of_left_cache, h_left_cache'⟩,
          right_tree, right_cache,
            ⟨h_right_tree_eq_build, h_left_cache_subcache_of_right_cache, h_right_cache'⟩,
          final, ⟨h_final_cache, h_final_cache'⟩, h_eq⟩
        subst h_eq
        have h_right_cache_subcache_of_resulting_cache : ∀ a b r,
            right_cache () (a, b) = some r → resulting_cache () (a, b) = some r := by
          sorry


        refine ⟨?_, ?_, ?_⟩
        · simp only [LeafDataTree.optionComposeBuild] at *
          simp [FullDataTree.map_internal, h_left_tree_eq_build, h_right_tree_eq_build,
            LeafDataTree.composeBuild_internal, LeafDataTree.map_internal]
          have right_composing_cache_change :
              (LeafDataTree.map some right_leaf_data).composeBuild
                (Option.doubleBind fun a b ↦ right_cache () (a, b)) =
              (LeafDataTree.map some right_leaf_data).composeBuild
                (Option.doubleBind fun a b ↦ resulting_cache () (a, b)) := by
            -- use right_cache_subcache_of_resulting_cache
            sorry
          have left_composing_cache_change :
              (LeafDataTree.map some left_leaf_data).composeBuild
                (Option.doubleBind fun a b ↦ left_cache () (a, b)) =
              (LeafDataTree.map some left_leaf_data).composeBuild
                (Option.doubleBind fun a b ↦ resulting_cache () (a, b)) := by
            sorry
          refine ⟨?_, ?_, ?_⟩
          · rw [Option.some_eq_doubleBind]
            use left_tree.getRootValue
            use right_tree.getRootValue
            rw [<- right_composing_cache_change, <- left_composing_cache_change]
            rw [<-h_left_tree_eq_build, <- h_right_tree_eq_build]
            refine ⟨?_, ?_, ?_⟩
            · rw [FullDataTree.map_getRootValue]
            · rw [FullDataTree.map_getRootValue]
            · rw [h_final_cache]
              simp
          · exact?
          · exact?

        · intro input_left input_right output h_mem_preexisting
          apply h_right_cache_subcache_of_resulting_cache
          apply h_left_cache_subcache_of_right_cache
          apply h_preexisting_cache_subcache_of_left_cache
          exact h_mem_preexisting
        · intro input_left input_right output h_mem_resulting
          simp only [FullDataTree.internal_toQueryCacheSet, Set.mem_insert_iff, Prod.mk.injEq,
            Set.mem_union]
          -- If we sufficiently specialize the hypotheses, we can grind or aesop it out
          -- Technically, I think we don't need to specialize the hypotheses, but aesop times out
          -- if we don't.
          specialize h_left_cache' input_left input_right output
          specialize h_right_cache' input_left input_right output
          specialize h_preexisting_cache_subcache_of_left_cache input_left input_right output
          specialize h_left_cache_subcache_of_right_cache input_left input_right output
          specialize h_right_cache_subcache_of_resulting_cache input_left input_right output
          replace h_final_cache := congrFun h_final_cache (input_left, input_right)
          simp only [Function.update_apply] at h_final_cache
          aesop -- Sick!
      · -- Backward direction
        classical
        intro h
        have := FullDataTree.internal_eq merkle_tree_cache
        rcases this with
          ⟨merkle_tree_root, left_subtree, right_subtree, h_eq⟩
        subst h_eq
        rcases h with ⟨h1, h2, h3⟩
        -- Construct the function for what the cache will be
        -- after the left side of the tree is computed
        let left_cache : (spec α).QueryCache := fun () input =>
          if ∃ pair ∈ left_subtree.toQueryCacheSet, pair.1 = input
          then
            resulting_cache () input
          else
            preexisting_cache () input
        use left_subtree, left_cache
        constructor
        · --

          simp at h1


          sorry
        -- Construct the function for what the cache will be
        -- after the right side of the tree is computed
        let right_cache : (spec α).QueryCache := fun () input =>
          if ∃ pair ∈ right_subtree.toQueryCacheSet, pair.1 = input
          then
            resulting_cache () input
          else
            left_cache () input
        use right_subtree, right_cache
        constructor
        · sorry
        use merkle_tree_root

        sorry



/--
When generateProof runs on a cache that contains all the queries in the merkle tree,
the putative root obtained from the resulting proof is equal to the root value of the cache.
-/
theorem putative_root_eq_merkle_tree_cache_root_of_generate_proof {α : Type}
    [DecidableEq α] [SelectableType α]
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (merkle_tree_cache : FullDataTree α s)
    (preexisting_cache resulting_cache : (spec α).QueryCache)
    (putative_root : α)
    (cache_subset :
      ∀ (a b c),
        ((a, b), c) ∈ merkle_tree_cache.toQueryCacheSet →
        preexisting_cache () (a, b) = some c)
    (mem_support' :
      (putative_root, resulting_cache) ∈
      ((simulateQ randomOracle
        (getPutativeRoot idx
          ((merkle_tree_cache.toLeafDataTree).getValueAtIndex idx)
          (generateProof merkle_tree_cache idx))).run
        preexisting_cache).support) :
    putative_root = merkle_tree_cache.getRootValue
   := by
  -- TODO refactor to avoid `QueryCache.toSet`
  replace cache_subset :
      merkle_tree_cache.toQueryCacheSet ⊆ QueryCache.toSet () preexisting_cache := by
    clear mem_support'
    simp only [Set.subset_def, QueryCache.toSet, Set.mem_setOf_eq]
    intro x x_mem
    apply cache_subset
    exact x_mem
  induction s generalizing putative_root preexisting_cache resulting_cache with
  | leaf =>
    cases idx with
    | ofLeaf =>
      simp only [generateProof_ofLeaf] at mem_support'
      rcases mem_support' with ⟨rfl, rfl⟩
      unfold FullDataTree.getRootValue getRootIndex
      rw [FullDataTree.toLeafDataTree_getValueAtIndex]
      simp
      rfl
  | internal left_skeleton right_skeleton left_ih right_ih =>
    -- Decompose the merkle tree cache into its left and right subtrees
    have := merkle_tree_cache.internal_eq
    rcases this with
      ⟨merkle_tree_root, left_subtree, right_subtree, h_eq⟩
    subst h_eq
    cases idx with
    | ofLeft idxLeft =>
      simp only [generateProof_ofLeft] at mem_support'
      unfold getPutativeRoot at mem_support'
      simp only [simulateQ_bind, StateT.run_bind, Function.comp_apply, support_bind, Set.mem_iUnion,
        exists_prop, Prod.exists] at mem_support'
      simp [] at mem_support'
      rcases mem_support' with
        ⟨putative_root_left, cache_after_left, h_mem_left,
        h_mem_getPutativeRoot, h_cache_after_left⟩
      simp only [LeafDataTree.getValueAtIndex_ofLeft] at h_mem_left
      simp at *

      simp only [Set.insert_subset_iff, Set.union_subset_iff] at cache_subset
      rcases cache_subset with
        ⟨h_mem_root_compose, h_mem_left_cache_subset, h_mem_right_cache_subset⟩
      specialize left_ih
        idxLeft left_subtree _ cache_after_left
        putative_root_left h_mem_left h_mem_left_cache_subset
      have := subcache_of_mem_support (α := α) _ _ _ _
        h_mem_left (left_subtree.getRootValue, right_subtree.getRootValue)
      clear h_mem_left h_mem_left_cache_subset h_mem_right_cache_subset
      subst left_ih
      -- rcases left_ih with
      --   ⟨putative_root_left_eq, h_preexisting_cache_subcache_of_left_cache⟩
      -- subst putative_root_left_eq
      simp [QueryCache.toSet] at h_mem_root_compose
      have cache_after_left_root_compose :
          cache_after_left () (left_subtree.getRootValue, right_subtree.getRootValue)
          = some merkle_tree_root := by
        aesop
      aesop
    | ofRight idxRight =>
      simp only [generateProof_ofRight] at mem_support'
      unfold getPutativeRoot at mem_support'
      simp only [simulateQ_bind, StateT.run_bind, Function.comp_apply, support_bind, Set.mem_iUnion,
        exists_prop, Prod.exists] at mem_support'
      simp [] at mem_support'
      rcases mem_support' with
        ⟨putative_root_right, cache_after_right, h_mem_right,
        h_mem_getPutativeRoot, h_cache_after_right⟩
      simp only [LeafDataTree.getValueAtIndex_ofRight] at h_mem_right
      simp at *
      simp only [Set.insert_subset_iff, Set.union_subset_iff] at cache_subset
      rcases cache_subset with
        ⟨h_mem_root_compose, h_mem_left_cache_subset, h_mem_right_cache_subset⟩
      specialize right_ih
        idxRight right_subtree _ cache_after_right
        putative_root_right h_mem_right h_mem_right_cache_subset
      have := subcache_of_mem_support (α := α) _ _ _ _
        h_mem_right (left_subtree.getRootValue, right_subtree.getRootValue)
      clear h_mem_right h_mem_left_cache_subset h_mem_right_cache_subset
      subst right_ih
      -- rcases right_ih with
      --   ⟨putative_root_right_eq, h_preexisting_cache_subcache_of_right_cache⟩
      -- subst putative_root_right_eq
      simp [QueryCache.toSet] at h_mem_root_compose
      have cache_after_right_root_compose :
          cache_after_right () (left_subtree.getRootValue, right_subtree.getRootValue)
          = some merkle_tree_root := by
        aesop
      aesop

theorem completeness [DecidableEq α] [SelectableType α] {s}
    (leaf_data_tree : LeafDataTree α s) (idx : BinaryTree.SkeletonLeafIndex s)
    (preexisting_cache : (spec α).QueryCache) :
    (((do
      let cache ← buildMerkleTree leaf_data_tree
      let proof := generateProof cache idx
      let _ ← verifyProof idx (leaf_data_tree.getValueAtIndex idx) (cache.getRootValue) proof
      ).simulateQ (randomOracle)).run preexisting_cache).neverFails := by
  -- TODO there should be a lemma that says that a computation never fails for all preexisting_cache if and only if it never fails for any complete cache / if it never fails when run in a context where the cache system is replaced with a vanilla function.
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
      rw [mem_buildMerkleTree_support_iff_v3] at h_mem_support
      rcases h_mem_support with
        ⟨h_mem_root_compose, h_preexisting_cache_subcache_of_left_cache,
        h_resulting_cache_subset⟩
      have : leaf_data_tree = merkle_tree_cache.toLeafDataTree := by
        -- follows from h_mem_root_compose
        symm
        exact
          LeafDataTree.eq_full_of_map_some_eq_optionComposeBuild merkle_tree_cache leaf_data_tree
            (fun a b ↦ query_cache () (a, b)) h_mem_root_compose
      rw [this] at h_mem_support'
      apply putative_root_eq_merkle_tree_cache_root_of_generate_proof
        idx merkle_tree_cache query_cache query_cache' _ _ h_mem_support'
      clear h_mem_support'

      -- follows from h_mem_root_compose
      intro input_left input_right output h_mem
      have := LeafDataTree.eq_full_of_map_some_eq_optionComposeBuild'
                merkle_tree_cache leaf_data_tree
                (fun a b ↦ query_cache () (a, b)) h_mem_root_compose
                input_left input_right output h_mem
      simp at this
      exact this

end

end InductiveMerkleTree
