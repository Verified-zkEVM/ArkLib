/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

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
def spec : OracleSpec (α × α) := (α × α) →ₒ α

@[simp, grind]
lemma domain_def : (spec α).Domain = (α × α) := rfl

@[simp]
lemma range_def {x} : (spec α).Range x = α := rfl

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Example: a single hash computation -/
@[simp, grind]
def singleHash (left : α) (right : α) : OracleComp (spec α) α := do
  let out ← query (spec := spec α) ⟨left, right⟩
  return out

/-- Cache for Merkle tree. Indexed by `j : Fin (n + 1)`, i.e. `j = 0, 1, ..., n`. -/
@[simp, grind]
def Cache (n : ℕ) := (layer : Fin (n + 1)) → List.Vector α (2 ^ layer.val)

/-- Add a base layer to the cache -/
@[simp, grind]
def Cache.cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache α (n + 1) :=
  Fin.snoc cache leaves

/-- Removes the leaves layer to the cache, returning only the layers of the tree above this -/
@[simp, grind]
def Cache.upper (n : ℕ) (cache : Cache α (n + 1)) :
    Cache α n :=
  Fin.init cache

/-- Returns the leaves of the cache -/
@[simp, grind]
def Cache.leaves (n : ℕ) (cache : Cache α (n + 1)) :
    List.Vector α (2 ^ (n + 1)) := cache (Fin.last _)

omit [DecidableEq α] [Inhabited α] [Fintype α] in
@[simp, grind]
lemma Cache.upper_cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache.upper α n (Cache.cons α n leaves cache) = cache := by
  simp [Cache.upper, Cache.cons]

omit [DecidableEq α] [Inhabited α] [Fintype α] in
@[simp, grind]
lemma Cache.leaves_cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache.leaves α n (Cache.cons α n leaves cache) = leaves := by
  simp [Cache.leaves, Cache.cons]

/-- Compute the next layer of the Merkle tree -/
@[simp, grind]
def buildLayer (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) :
    OracleComp (spec α) (List.Vector α (2 ^ n)) := do
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  -- Pair up the leaves to form pairs
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by omega⟩, leaves.get ⟨2 * i + 1, by omega⟩))
  -- Hash each pair to get the next layer
  let hashes : List.Vector α (2 ^ n) ←
    List.Vector.mmap (fun ⟨left, right⟩ => query (spec := spec α) ⟨left, right⟩) pairs
  return hashes

/-- Build the full Merkle tree, returning the cache -/
@[simp, grind]
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
@[simp, grind]
def getRoot {n : ℕ} (cache : Cache α n) : α :=
  (cache 0).get ⟨0, by simp⟩

/-- Figure out the indices of the Merkle tree nodes that are needed to
recompute the root from the given leaf -/
@[simp, grind]
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

@[simp, grind]
theorem getRoot_trivial (a : α) : getRoot α <$> (buildMerkleTree α 0 ⟨[a], rfl⟩) = pure a := by
  simp [getRoot, buildMerkleTree, List.Vector.head]

@[simp, grind]
theorem getRoot_single (a b : α) :
    getRoot α <$> buildMerkleTree α 1 ⟨[a, b], rfl⟩ = (query (spec := spec α) (a, b)) := by
  simp [buildMerkleTree, buildLayer, List.Vector.ofFn, List.Vector.get]

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Generate a Merkle proof that a given leaf at index `i` is in the Merkle tree. The proof consists
  of the Merkle tree nodes that are needed to recompute the root from the given leaf. -/
@[simp, grind]
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
@[simp, grind]
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
      let newLeaf ← query (spec := spec α) ⟨leaf, proof.get (Fin.last n)⟩
      getPutativeRoot i' newLeaf (proof.drop 1)
    else
      -- `i` is a right child
      let newLeaf ← query (spec := spec α) ⟨proof.get (Fin.last n), leaf⟩
      getPutativeRoot i' newLeaf (proof.drop 1)

/-- Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
  `root`.
  Works by computing the putative root based on the branch, and comparing that to the actual root.
  Outputs `failure` if the proof is invalid. -/
@[simp, grind]
def verifyProof {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (root : α) (proof : List.Vector α n) :
    OptionT (OracleComp (spec α)) Unit := do
  let putative_root ← getPutativeRoot α i leaf proof
  guard (putative_root = root)

@[simp, grind]
theorem buildLayer_neverFails (α : Type) [inst : DecidableEq α]
    [inst_1 : SampleableType α] [(spec α).DecidableEq]
    (preexisting_cache : (spec α).QueryCache) (n : ℕ)
    (leaves : List.Vector α (2 ^ (n + 1))) : NeverFail
      ((simulateQ (randomOracle (spec := spec α))
        (buildLayer α n leaves)).run preexisting_cache) := by
  grind

/--
Building a Merkle tree never results in failure
(no matter what queries have already been made to the oracle before it runs).
-/
@[simp, grind]
theorem buildMerkleTree_neverFails (α : Type) [DecidableEq α]
    [SampleableType α] {n : ℕ} [(spec α).DecidableEq]
    (leaves : List.Vector α (2 ^ n)) (preexisting_cache : (spec α).QueryCache) :
    NeverFail
      ((simulateQ (randomOracle (spec := spec α))
        (buildMerkleTree α n leaves)).run preexisting_cache) := by
  grind

/-- Completeness theorem for Merkle trees: for any full binary tree with `2 ^ n` leaves, and for any
  index `i`, the verifier accepts the opening proof at index `i` generated by the prover.
-/
@[simp]
theorem completeness [SampleableType α] {n : ℕ} [(spec α).DecidableEq]
    (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n)) (hash : α × α -> α)
    (preexisting_cache : (spec α).QueryCache) :
    NeverFail ((
      simulateQ (randomOracle (spec := spec α)) (do
        let cache ← buildMerkleTree α n leaves
        let proof := generateProof α i cache
        let verif ← verifyProof α i leaves[i] (getRoot α cache) proof)).run preexisting_cache :
      ProbComp (Unit × (spec α).QueryCache)) := by
  grind

-- theorem soundness (i : Fin (2 ^ n)) (leaf : α) (proof : Vector α n) :
--     verifyMerkleProof i leaf proof = pure true →
--     getMerkleRoot (buildMerkleTree n (leaf ::ᵥ proof)) = leaf := sorry

end

section Test

-- 6 = 110_big
-- Third neighbor (`j = 0`): 0 = 0 big
-- Second neighbor (`j = 1`): 2 = 10 big
-- First neighbor (`j = 2`): 7 = 111 big
-- #eval findNeighbors (6 : Fin (2 ^ 3)) 0
-- #eval findNeighbors (6 : Fin (2 ^ 3)) 1
-- #eval findNeighbors (6 : Fin (2 ^ 3)) 2


end Test

end MerkleTree
