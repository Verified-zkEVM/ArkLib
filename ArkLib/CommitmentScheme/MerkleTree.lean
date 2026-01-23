/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Vector.Snoc
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.DistSemantics.List
import ArkLib.ToVCVio.Oracle

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

/-- Sibling index in a perfect binary tree layer indexed by `Fin (2 ^ (n + 1))`. -/
def siblingIndex {n : ℕ} (i : Fin (2 ^ (n + 1))) : Fin (2 ^ (n + 1)) :=
  if h : i.val % 2 = 0 then
    ⟨i.val + 1, by
      have hi : i.val < 2 ^ (n + 1) := i.isLt
      have hEven : Even (2 ^ (n + 1)) := by
        exact (Nat.even_pow).2 ⟨by simpa using (even_two : Even (2 : ℕ)), Nat.succ_ne_zero n⟩
      have hmod : (2 ^ (n + 1)) % 2 = 0 := (Nat.even_iff).1 hEven
      have hle : i.val + 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt hi
      have hne : i.val + 1 ≠ 2 ^ (n + 1) := by
        intro hEq
        have hiVal : i.val = 2 ^ (n + 1) - 1 := by omega
        have hpos : 0 < 2 ^ (n + 1) := by
          exact pow_pos (by decide : 0 < (2 : ℕ)) _
        have hle1 : 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt hpos
        have hmodPred : (2 ^ (n + 1) - 1) % 2 = 1 := by
          have : (2 ^ (n + 1) - 1 + 1) % 2 = 0 := by
            simpa [Nat.sub_add_cancel hle1] using hmod
          exact (Nat.succ_mod_two_eq_zero_iff (m := 2 ^ (n + 1) - 1)).1 this
        have : i.val % 2 = 1 := by simpa [hiVal] using hmodPred
        omega
      exact lt_of_le_of_ne hle hne⟩
  else
    ⟨i.val - 1, by
      have hi : i.val < 2 ^ (n + 1) := i.isLt
      omega⟩

/-- Generate a Merkle proof that a given leaf at index `i` is in the Merkle tree. The proof consists
  of the Merkle tree nodes that are needed to recompute the root from the given leaf. -/
def generateProof {n : ℕ} (i : Fin (2 ^ n)) (cache : Cache α n) :
    List.Vector α n :=
  match n with
  | 0 => List.Vector.nil
  | n + 1 =>
      List.Vector.cons ((cache.leaves).get (siblingIndex i))
        (generateProof ⟨i.val / 2, by omega⟩ (cache.upper))

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
      let newLeaf ← query (spec := spec α) () ⟨leaf, proof.head⟩
      getPutativeRoot i' newLeaf proof.tail
    else
      -- `i` is a right child
      let newLeaf ← query (spec := spec α) () ⟨proof.head, leaf⟩
      getPutativeRoot i' newLeaf proof.tail

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
  -- Reduce to showing the computation succeeds for any deterministic oracle.
  have hAll :
      ∀ cache : (spec α).QueryCache,
        ((simulateQ randomOracle (buildLayer α n leaves)).run cache).neverFails := by
    -- An oracle computation never fails on all caches iff it succeeds under any oracle function.
    rw [randomOracle_neverFails_iff_runWithOracle_neverFails (oa := buildLayer α n leaves)]
    intro f
    -- `buildLayer` contains no failures, only queries and pure code.
    -- We show evaluation under `runWithOracle` always returns `some _`.
    have h_mmap :
        ∀ {m : ℕ} (xs : List.Vector (α × α) m),
          (runWithOracle f
              (List.Vector.mmap (fun x => liftM (query (spec := spec α) () x)) xs)).isSome = true :=
        by
      intro m xs
      induction xs using List.Vector.inductionOn with
      | nil =>
        simp [runWithOracle_pure]
      | @cons m x xs ih =>
        have h_query :
            runWithOracle f (liftM (query (spec := spec α) () x)) = some (f () x) := by
          unfold runWithOracle OracleComp.construct'
          simp
        simp [List.Vector.mmap_cons, runWithOracle_bind, h_query, map_eq_bind_pure_comp,
          runWithOracle_pure]
        cases hrest :
            runWithOracle f
              (List.Vector.mmap (fun x => liftM (query (spec := spec α) () x)) xs) with
        | none =>
          have : False := by
            simpa [hrest] using ih
          contradiction
        | some v =>
          simp [hrest]
    simp [buildLayer, h_mmap]
  exact hAll preexisting_cache

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

/-- A purely functional version of `buildLayer`, given an explicit hash function. -/
def buildLayer_with_hash (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (hashFn : α × α → α) :
    List.Vector α (2 ^ n) :=
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by omega⟩, leaves.get ⟨2 * i + 1, by omega⟩))
  pairs.map hashFn

/-- A purely functional version of `buildMerkleTree`, given an explicit hash function. -/
def buildMerkleTree_with_hash (n : ℕ) (leaves : List.Vector α (2 ^ n)) (hashFn : α × α → α) :
    Cache α n :=
  match n with
  | 0 =>
      fun j => by
        rw [Fin.val_eq_zero j]
        exact leaves
  | n + 1 =>
      let lastLayer := buildLayer_with_hash (α := α) n leaves hashFn
      let cache := buildMerkleTree_with_hash n lastLayer hashFn
      Cache.cons α n leaves cache

/--
A purely functional version of `getPutativeRoot`, given an explicit hash function.
-/
def getPutativeRoot_with_hash {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (proof : List.Vector α n)
    (hashFn : α × α → α) : α :=
  match n with
  | 0 => leaf
  | n + 1 =>
      let signBit := i.val % 2
      let i' : Fin (2 ^ n) := ⟨i.val / 2, by omega⟩
      if signBit = 0 then
        let newLeaf := hashFn (leaf, proof.head)
        getPutativeRoot_with_hash i' newLeaf proof.tail hashFn
      else
        let newLeaf := hashFn (proof.head, leaf)
        getPutativeRoot_with_hash i' newLeaf proof.tail hashFn

@[simp]
lemma runWithOracle_query (f : (spec α).FunctionType) (x : α × α) :
    runWithOracle f (liftM (query () x)) = some (f () x) := by
  unfold runWithOracle OracleComp.construct'
  simp

lemma runWithOracle_listVector_mmap_query (f : (spec α).FunctionType) {m : ℕ}
    (xs : List.Vector (α × α) m) :
    runWithOracle f
        (List.Vector.mmap (fun x => liftM (query () x)) xs) =
      some (xs.map (fun x => f () x)) := by
  induction xs using List.Vector.inductionOn with
  | nil => simp
  | @cons m x xs ih =>
    -- Reduce to the inductive hypothesis and the fact that a query always returns `some`.
    simp [List.Vector.mmap_cons, map_eq_bind_pure_comp, runWithOracle_bind, ih, runWithOracle_pure]
    rw [runWithOracle_query (α := α) (f := f) (x := x)]
    rfl

lemma runWithOracle_buildLayer (f : (spec α).FunctionType) (n : ℕ)
    (leaves : List.Vector α (2 ^ (n + 1))) :
    runWithOracle f (buildLayer α n leaves) =
      some (buildLayer_with_hash (α := α) n leaves (fun x => f () x)) := by
  -- `buildLayer` is just monadic `mmap` of `query` over `pairs`.
  simp [buildLayer, buildLayer_with_hash, runWithOracle_bind, runWithOracle_pure]
  simpa using
    (runWithOracle_listVector_mmap_query (α := α) (f := f)
      (xs :=
        List.Vector.ofFn fun i =>
          (leaves.get ⟨2 * i, by omega⟩, leaves.get ⟨2 * i + 1, by omega⟩)))

lemma runWithOracle_buildMerkleTree (f : (spec α).FunctionType) (n : ℕ)
    (leaves : List.Vector α (2 ^ n)) :
    runWithOracle f (buildMerkleTree α n leaves) =
      some (buildMerkleTree_with_hash (α := α) n leaves (fun x => f () x)) := by
  induction n with
  | zero =>
    simp [buildMerkleTree, buildMerkleTree_with_hash]
  | succ n ih =>
    simp [buildMerkleTree, buildMerkleTree_with_hash, map_eq_bind_pure_comp, runWithOracle_bind,
      runWithOracle_pure, runWithOracle_buildLayer, ih]

lemma runWithOracle_getPutativeRoot (f : (spec α).FunctionType) {n : ℕ} (i : Fin (2 ^ n))
    (leaf : α) (proof : List.Vector α n) :
    runWithOracle f (getPutativeRoot α i leaf proof) =
      some (getPutativeRoot_with_hash (α := α) i leaf proof (fun x => f () x)) := by
  induction n generalizing leaf with
  | zero =>
    simp [getPutativeRoot, getPutativeRoot_with_hash]
  | succ n ih =>
    by_cases hsign : i.val % 2 = 0
    · simp [getPutativeRoot, getPutativeRoot_with_hash, hsign, runWithOracle_bind, runWithOracle_pure,
        ih]
      rw [runWithOracle_query (α := α) (f := f) (x := (leaf, proof.head))]
      rfl
    · simp [getPutativeRoot, getPutativeRoot_with_hash, hsign, runWithOracle_bind, runWithOracle_pure,
        ih]
      rw [runWithOracle_query (α := α) (f := f) (x := (proof.head, leaf))]
      rfl

/-- A functional completeness theorem for Merkle proofs built from `buildMerkleTree_with_hash`. -/
theorem functional_completeness {n : ℕ} (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n))
    (hashFn : α × α → α) :
    getPutativeRoot_with_hash (α := α) i leaves[i]
        (generateProof α i (buildMerkleTree_with_hash (α := α) n leaves hashFn)) hashFn =
      getRoot α (buildMerkleTree_with_hash (α := α) n leaves hashFn) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    simp [buildMerkleTree_with_hash, generateProof, getPutativeRoot_with_hash, getRoot]
    change leaves.get 0 = leaves.head
    simp
  | succ n ih =>
    -- Abbreviate the upper layer and the upper tree.
    let lastLayer := buildLayer_with_hash (α := α) n leaves hashFn
    let upperCache := buildMerkleTree_with_hash (α := α) n lastLayer hashFn
    -- Split on whether `i` is a left or right child at the bottom layer.
    by_cases hsign : i.val % 2 = 0
    · -- Left child: sibling is `i + 1`.
      have hdiv : 2 * (i.val / 2) = i.val := by
        have h := Nat.mod_add_div i.val 2
        -- `i % 2 = 0` implies `2 * (i / 2) = i`.
        simpa [hsign] using h
      have hright : 2 * (i.val / 2) + 1 = i.val + 1 := by omega
      have hnew :
          hashFn (leaves.get i, leaves.get (siblingIndex i)) =
            lastLayer.get ⟨i.val / 2, by omega⟩ := by
        simp [lastLayer, buildLayer_with_hash, siblingIndex, hsign, hdiv, hright]
      -- Unfold and apply the induction hypothesis on the upper tree.
      -- `generateProof` and `getRoot` reduce via `Cache.upper_cons` and `Cache.leaves_cons`.
      simp [buildMerkleTree_with_hash, lastLayer, upperCache, generateProof, getPutativeRoot_with_hash,
        getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer, upperCache] using
        (ih (leaves := lastLayer) (i := ⟨i.val / 2, by omega⟩))
    · -- Right child: sibling is `i - 1`.
      have hmod1 : i.val % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one i.val with h0 | h1
        · exact (hsign h0).elim
        · exact h1
      have hdiv : 2 * (i.val / 2) = i.val - 1 := by
        have h := Nat.mod_add_div i.val 2
        -- `i % 2 = 1` implies `1 + 2 * (i / 2) = i`.
        have : 1 + 2 * (i.val / 2) = i.val := by simpa [hmod1] using h
        omega
      have hright : 2 * (i.val / 2) + 1 = i.val := by omega
      have hnew :
          hashFn (leaves.get (siblingIndex i), leaves.get i) =
            lastLayer.get ⟨i.val / 2, by omega⟩ := by
        have hiPos : 1 ≤ i.val := by
          have hne : i.val ≠ 0 := by
            intro h0
            simpa [h0] using hmod1
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
        have hi' :
            (⟨i.val - 1 + 1, by simpa [Nat.sub_add_cancel hiPos] using i.isLt⟩ :
                Fin (2 ^ (n + 1))) =
              i := by
          ext
          simpa [Nat.sub_add_cancel hiPos]
        simp [lastLayer, buildLayer_with_hash, siblingIndex, hsign, hmod1, hdiv, hright, hi']
      simp [buildMerkleTree_with_hash, lastLayer, upperCache, generateProof, getPutativeRoot_with_hash,
        getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer, upperCache] using
        (ih (leaves := lastLayer) (i := ⟨i.val / 2, by omega⟩))

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
  -- Reduce to showing success under any deterministic oracle function.
  revert preexisting_cache
  rw [randomOracle_neverFails_iff_runWithOracle_neverFails]
  intro f
  -- Simplify the computation under `runWithOracle`.
  simp_rw [verifyProof, guard_eq, bind_pure_comp, id_map', runWithOracle_bind,
    runWithOracle_buildMerkleTree, runWithOracle_getPutativeRoot]
  simp only [apply_ite, runWithOracle_pure, runWithOracle_failure, Option.bind_eq_bind,
    Option.bind_some, Option.isSome_some, Option.isSome_none, Bool.if_false_right, Bool.and_true,
    decide_eq_true_eq]
  -- Apply the purely functional completeness lemma.
  simpa using functional_completeness (α := α) (leaves := leaves) (i := i) (hashFn := fun x => f () x)

end

section Test

-- 6 = 110_big
-- Third neighbor (`j = 0`): 0 = 0 big
-- Second neighbor (`j = 1`): 2 = 10 big
-- First neighbor (`j = 2`): 7 = 111 big
#eval findNeighbors (6 : Fin (2 ^ 3)) 0
#eval findNeighbors (6 : Fin (2 ^ 3)) 1
#eval findNeighbors (6 : Fin (2 ^ 3)) 2

example : findNeighbors (n := 3) (6 : Fin (2 ^ 3)) (0 : Fin 3) = (0 : Fin 2) := by native_decide
example : findNeighbors (n := 3) (6 : Fin (2 ^ 3)) (1 : Fin 3) = (2 : Fin 4) := by native_decide
example : findNeighbors (n := 3) (6 : Fin (2 ^ 3)) (2 : Fin 3) = (7 : Fin 8) := by native_decide

example : siblingIndex (n := 0) (0 : Fin 2) = (1 : Fin 2) := by decide
example : siblingIndex (n := 0) (1 : Fin 2) = (0 : Fin 2) := by decide
example : siblingIndex (n := 1) (0 : Fin 4) = (1 : Fin 4) := by decide
example : siblingIndex (n := 1) (1 : Fin 4) = (0 : Fin 4) := by decide
example : siblingIndex (n := 1) (2 : Fin 4) = (3 : Fin 4) := by decide
example : siblingIndex (n := 1) (3 : Fin 4) = (2 : Fin 4) := by decide

def testHash (p : Nat × Nat) : Nat := p.1 * 100 + p.2

def testOracle : (spec Nat).FunctionType := fun _ p => testHash p

def testLeaves : List.Vector Nat (2 ^ 2) := ⟨[1, 2, 3, 4], by decide⟩

def testCache : Cache Nat 2 := buildMerkleTree_with_hash (α := Nat) 2 testLeaves testHash

def testRoot : Nat := getRoot Nat testCache

def testProofIdx2 : List.Vector Nat 2 := generateProof Nat (2 : Fin 4) testCache

def testProofIdx1 : List.Vector Nat 2 := generateProof Nat (1 : Fin 4) testCache

example : testProofIdx2 = (⟨[4, 102], by decide⟩ : List.Vector Nat 2) := by native_decide
example : testProofIdx1 = (⟨[1, 304], by decide⟩ : List.Vector Nat 2) := by native_decide

example :
    runWithOracle testOracle
        (verifyProof Nat (2 : Fin 4) testLeaves[(2 : Fin 4)] testRoot testProofIdx2) =
      some () := by
  native_decide

example :
    runWithOracle testOracle
        (verifyProof Nat (2 : Fin 4) (testLeaves[(2 : Fin 4)] + 1) testRoot testProofIdx2) =
      none := by
  native_decide

example :
    runWithOracle testOracle (getPutativeRoot Nat (1 : Fin 4) testLeaves[(1 : Fin 4)] testProofIdx1) =
      some testRoot := by
  native_decide

example :
    getPutativeRoot_with_hash Nat (1 : Fin 4) testLeaves[(1 : Fin 4)] testProofIdx1 testHash = testRoot := by
  native_decide

example : runWithOracle testOracle (getRoot Nat <$> buildMerkleTree Nat 2 testLeaves) = some testRoot := by
  native_decide


end Test

end MerkleTree
