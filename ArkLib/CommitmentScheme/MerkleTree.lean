/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Tree.Binary
import Mathlib.Data.Vector.Snoc
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
  # Merkle Trees as a vector commitment

  ## Notes & TODOs

  We want this treatment to be as comprehensive as possible. In particular, our formalization
  should (eventually) include all complexities such as the following:

  - Multi-instance extraction & simulation
  - Dealing with arbitrary trees (may have arity > 2, or is not complete)
  - Path pruning optimization
-/

namespace MerkleTree

open List OracleSpec OracleComp

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

/-- Cache for Merkle tree. Indexed by `j : Fin (n + 1)`, i.e. `j = 0, 1, ..., n`. -/
def Cache (n : ℕ) := (layer : Fin (n + 1)) → List.Vector α (2 ^ layer.val)

/-- Add a base layer to the cache -/
def Cache.cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache α (n + 1) :=
  Fin.snoc cache leaves

/-- Removes the leaves layer to the cache, returning only the layers of the tree above this -/
def Cache.upper (n : ℕ) (cache : Cache α (n + 1)) :
    Cache α n :=
  Fin.init cache

/-- Returns the leaves of the cache -/
def Cache.leaves (n : ℕ) (cache : Cache α (n + 1)) :
    List.Vector α (2 ^ (n + 1)) := cache (Fin.last _)

omit [DecidableEq α] [Inhabited α] [Fintype α] in
@[simp]
lemma Cache.upper_cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache.upper α n (Cache.cons α n leaves cache) = cache := by
  simp [Cache.upper, Cache.cons]

omit [DecidableEq α] [Inhabited α] [Fintype α] in
@[simp]
lemma Cache.leaves_cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache.leaves α n (Cache.cons α n leaves cache) = leaves := by
  simp [Cache.leaves, Cache.cons]

/-- Compute the next layer of the Merkle tree -/
def buildLayer (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) :
    OracleComp (spec α) (List.Vector α (2 ^ n)) := do
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  -- Pair up the leaves to form pairs
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by omega⟩, leaves.get ⟨2 * i + 1, by omega⟩))
  -- Hash each pair to get the next layer
  let hashes : List.Vector α (2 ^ n) ←
    List.Vector.mmap (fun ⟨left, right⟩ => query (spec := spec α) () ⟨left, right⟩) pairs
  return hashes

/-- Build the full Merkle tree, returning the cache -/
def buildMerkleTree (α) (n : ℕ) (leaves : List.Vector α (2 ^ n)) :
    OracleComp (spec α) (Cache α n) := do
  match n with
  | 0 => do
    return fun j => (by
      rw [Fin.val_eq_zero j]
      exact leaves)
  | n + 1 => do
    let lastLayer ← buildLayer α n leaves
    let cache ← buildMerkleTree α n lastLayer
    return Cache.cons α n leaves cache

/-- Get the root of the Merkle tree -/
def getRoot {n : ℕ} (cache : Cache α n) : α :=
  (cache 0).get ⟨0, by simp⟩

/-- Figure out the indices of the Merkle tree nodes that are needed to
recompute the root from the given leaf -/
def findNeighbors {n : ℕ} (i : Fin (2 ^ n)) (layer : Fin n) :
    Fin (2 ^ (layer.val + 1)) :=
  -- `finFunctionFinEquiv.invFun` gives the little-endian order, e.g. `6 = 011 little`
  -- so we need to reverse it to get the big-endian order, e.g. `6 = 110 big`
  let bits := (Vector.ofFn (finFunctionFinEquiv.invFun i)).reverse
  -- `6 = 110 big`, `j = 1`, we get `neighbor = 10 big`
  let neighbor := (bits.set layer (bits.get layer + 1)).take (layer.val + 1)
  have : min (layer.val + 1) n = layer.val + 1 := by omega
  -- `10 big` => `01 little` => `2`
  finFunctionFinEquiv.toFun (this ▸ neighbor.reverse.get)

end

@[simp]
theorem getRoot_trivial (a : α) : getRoot α <$> (buildMerkleTree α 0 ⟨[a], rfl⟩) = pure a := by
  simp [getRoot, buildMerkleTree, List.Vector.head]

@[simp]
theorem getRoot_single (a b : α) :
    getRoot α <$> buildMerkleTree α 1 ⟨[a, b], rfl⟩ = (query (spec := spec α) () (a, b)) := by
  simp [buildMerkleTree, buildLayer, List.Vector.ofFn, List.Vector.get]
  unfold Cache.cons getRoot
  simp [Fin.snoc]

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Generate a Merkle proof that a given leaf at index `i` is in the Merkle tree. The proof consists
  of the Merkle tree nodes that are needed to recompute the root from the given leaf. -/
def generateProof {n : ℕ} (i : Fin (2 ^ n)) (cache : Cache α n) :
    List.Vector α n :=
  match n with
  | 0 => List.Vector.nil
  | n + 1 => List.Vector.snoc (generateProof ⟨i.val / 2, by omega⟩ (cache.upper))
                              ((cache.leaves).get (findNeighbors i (Fin.last _)))

/--
Given a leaf index, a leaf at that index, and putative proof,
returns the hash that would be the root of the tree if the proof was valid.
i.e. the hash obtained by combining the leaf in sequence with each member of the proof,
according to its index.
-/
def getPutativeRoot {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (proof : List.Vector α n) :
    OracleComp (spec α) α := do
  match h : n with
  | 0 => do
    -- When we have an empty proof, the root is just the leaf
    return leaf
  | n + 1 => do
    -- Get the sign bit of `i`
    let signBit := i.val % 2
    -- Show that `i / 2` is in `Fin (2 ^ (n - 1))`
    let i' : Fin (2 ^ n) := ⟨i.val / 2, by omega⟩
    if signBit = 0 then
      -- `i` is a left child
      let newLeaf ← query (spec := spec α) () ⟨leaf, proof.get (Fin.last n)⟩
      getPutativeRoot i' newLeaf (proof.drop 1)
    else
      -- `i` is a right child
      let newLeaf ← query (spec := spec α) () ⟨proof.get (Fin.last n), leaf⟩
      getPutativeRoot i' newLeaf (proof.drop 1)

/-- Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
  `root`.
  Works by computing the putative root based on the branch, and comparing that to the actual root.
  Outputs `failure` if the proof is invalid. -/
def verifyProof {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (root : α) (proof : List.Vector α n) :
    OracleComp (spec α) Unit := do
  let putative_root ← getPutativeRoot α i leaf proof
  guard (putative_root = root)


theorem buildLayer_neverFails (α : Type) [inst : DecidableEq α] [inst_1 : SelectableType α]
    (preexisting_cache : (spec α).QueryCache) (n : ℕ)
    (leaves : List.Vector α (2 ^ (n + 1))) :
    ((simulateQ randomOracle (buildLayer α n leaves)).run preexisting_cache).neverFails := by
  simp_rw [buildLayer]
  simp only [range_def, Prod.mk.eta, eq_mp_eq_cast, cast_eq, bind_pure]
  -- I now require a "neverFails_mmap_iff" lemma, but I don't see one in VCVio.
  -- Feels like evidence for avoiding Vector-based merkle trees in favor of inductive-based ones.
  sorry

/--
Building a Merkle tree never results in failure
(no matter what queries have already been made to the oracle before it runs).
-/
theorem buildMerkleTree_neverFails (α : Type) [DecidableEq α] [SelectableType α] {n : ℕ}
    (leaves : List.Vector α (2 ^ n)) (preexisting_cache : (spec α).QueryCache) :
    ((simulateQ randomOracle (buildMerkleTree α n leaves)).run preexisting_cache).neverFails := by
  -- It feels like there should be some kind of tactic that inspects the structure of the
  -- `buildMerkleTree` definition to see that it never even mentions failure,
  -- and therefore can't fail.
  induction n generalizing preexisting_cache with
  | zero =>
    simp [buildMerkleTree]
  | succ n ih =>
    simp [buildMerkleTree, neverFails_bind_iff]
    constructor
    · exact buildLayer_neverFails α preexisting_cache n leaves
    · intro next_leaves next_cache h_mem_support
      apply ih

/-- Completeness theorem for Merkle trees: for any full binary tree with `2 ^ n` leaves, and for any
  index `i`, the verifier accepts the opening proof at index `i` generated by the prover.
-/
theorem completeness [SelectableType α] {n : ℕ}
    (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n)) (hash : α × α -> α)
    (preexisting_cache : (spec α).QueryCache) :
    (((do
      let cache ← buildMerkleTree α n leaves
      let proof := generateProof α i cache
      let verif ← verifyProof α i leaves[i] (getRoot α cache) proof).simulateQ
      (randomOracle)).run preexisting_cache).neverFails := by
  simp [neverFails_bind_iff]
  constructor
  · -- buildMerkleTree never fails
    exact buildMerkleTree_neverFails α leaves preexisting_cache
  · -- verifyProof never fails on the output of generateProof after buildMerkleTree
    intros merkle_tree_cache query_cache h_mem_support
    -- Need a theorem to characterize
    -- `((simulateQ randomOracle (buildMerkleTree α n leaves)).run preexisting_cache).support`
    -- i.e.
    --  - All merkle_tree_cache parent-child relationships are in the query_cache
    --  - Everything in the preexisting_cache is in the query_cache
    --  - Nothing else is in the query_cache
    sorry






--   induction n with
--   | zero =>
--     simp [buildMerkleTree, getRoot, generateProof, verifyProof, getPutativeRoot]
--     have : i = 0 := by aesop
--     subst i
--     simp [Fin.instGetElemFinVal]
--   | succ n ih =>
--     -- simp_all [Fin.getElem_fin, Vector.getElem_eq_get, Fin.eta, getRoot, Fin.val_zero,
--     --   Nat.pow_zero, Fin.zero_eta, Vector.get_zero, bind_pure_comp,
-- id_map', probFailure_eq_zero_iff,
--     --   neverFails_bind_iff, buildMerkleTree, generateProof,
-- LawfulMonad.bind_assoc, bind_map_left,
--     --   Cache.upper_cons, Cache.leaves_cons]
--     -- refine ⟨?_, ?_⟩
--     -- ·
--     simp [buildLayer, simulateQ, simulateQ, implement_with_function]
--     sorry

--     -- · intro newLeaves h_newLeaves
--     --   let i' : Fin (2 ^ n) := i.val / 2
--     --   specialize ih newLeaves i'
--     --   rcases ih with ⟨ih', ih⟩
--     --   sorry
--       -- refine ⟨?_, ?_⟩
--       -- · exact ih'
--       -- · intro cache h_cache
--       --   specialize ih cache h_cache
--       --   unfold verifyProof
--       --   simp only [guard_eq, neverFails_bind_iff]
--       --   unfold verifyProof at ih
--       --   simp only [guard_eq, neverFails_bind_iff] at ih
--       --   rcases ih with ⟨ih_getroot, ih_cmp⟩
--       --   refine ⟨?_, ?_⟩
--       --   · -- I think this just needs a simple lemma about `getPutativeRoot`
--       --     sorry
--       --   · intro root h_root
--       --     specialize ih_cmp root
--       --     have : root ∈ (getPutativeRoot α i'
--       --                     (newLeaves.get i') (generateProof α i' cache)).support := by

--       --       sorry
--       --     specialize ih_cmp this
--       --     simp [apply_ite] at ih_cmp
--       --     rw [ih_cmp]
--       --     simp [apply_ite]
--       --     simp [Cache.cons]
--       --     sorry


-- theorem soundness (i : Fin (2 ^ n)) (leaf : α) (proof : Vector α n) :
--     verifyMerkleProof i leaf proof = pure true →
--     getMerkleRoot (buildMerkleTree n (leaf ::ᵥ proof)) = leaf := sorry

end

section Test

-- 6 = 110_big
-- Third neighbor (`j = 0`): 0 = 0 big
-- Second neighbor (`j = 1`): 2 = 10 big
-- First neighbor (`j = 2`): 7 = 111 big
#eval findNeighbors (6 : Fin (2 ^ 3)) 0
#eval findNeighbors (6 : Fin (2 ^ 3)) 1
#eval findNeighbors (6 : Fin (2 ^ 3)) 2


end Test

end MerkleTree

-- Alternative definition of Merkle tree using inductive type

variable {α : Type}

/-- Helper function to get the proof for a value at a given path. -/
def getProofHelper [DecidableEq α] : List Bool → BinaryTree α → List α
  | _, BinaryTree.nil => []
  | _, BinaryTree.leaf _ => []
  | [], BinaryTree.node _ _ _ => []
  | false :: rest, BinaryTree.node _ l r =>
    match BinaryTree.getRoot r with
    | none => getProofHelper rest l
    | some v => v :: getProofHelper rest l
  | true :: rest, BinaryTree.node _ l r =>
    match BinaryTree.getRoot l with
    | none => getProofHelper rest r
    | some v => v :: getProofHelper rest r

/-- Generate a Merkle proof for a leaf with value 'a'.
    The proof consists of the sibling hashes needed to recompute the root. -/
def generateProof [DecidableEq α] (a : α) (tree : BinaryTree α) : Option (List α) :=
  match BinaryTree.findPath a tree with
  | none => none
  | some path => some (getProofHelper path tree)

/-- Verify a Merkle proof that a value 'a' is in the tree with root 'root'.
    The 'proof' contains sibling hashes, and 'path' is the position (left/right) at each level. -/
def verifyProof [DecidableEq α] (hashFn : α → α → α) (a : α) (root : α)
    (proof : List α) (path : List Bool) : Bool :=
  let rec verify (current : α) (p : List α) (dirs : List Bool) : Bool :=
    match p, dirs with
    | [], [] => current = root
    | sibling :: restProof, dir :: restPath =>
      let nextHash := if dir then hashFn sibling current else hashFn current sibling
      verify nextHash restProof restPath
    | _, _ => false -- Proof and path lengths don't match
  verify a proof path

-- /-- Build a Merkle tree from a list of leaves using a hash function. -/
-- def buildMerkleTree [DecidableEq α] [Inhabited α]
--     (hashFn : α → α → α) (leaves : List α) : BinaryTree α :=
--   -- Find the smallest power of 2 that fits all leaves
--   -- We can estimate 2^n >= leaves.length by using n = ceiling(log2(leaves.length))
--   let n := Nat.ceil (Nat.log 2 (leaves.length + 1)) -- Ceiling of log base 2
--   LeafTree.toMerkleTree hashFn (LeafTree.fromList n leaves)
