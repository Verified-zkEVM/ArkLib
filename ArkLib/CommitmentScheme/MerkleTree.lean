/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Fawad Haider
-/

import VCVio.OracleComp.QueryTracking.RandomOracle
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
def spec : OracleSpec (α × α) := (α × α) →ₒ α

@[simp, grind =]
lemma domain_def : (spec α).Domain = (α × α) := rfl

@[simp]
lemma range_def {x} : (spec α).Range x = α := rfl

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Example: a single hash computation -/
def singleHash (left : α) (right : α) : OracleComp (spec α) α := do
  let out ← query (spec := spec α) ⟨left, right⟩
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
def buildLayer (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) :
    OracleComp (spec α) (List.Vector α (2 ^ n)) := do
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  -- Pair up the leaves to form pairs
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by grind only⟩, leaves.get ⟨2 * i + 1, by grind only⟩))
  -- Hash each pair to get the next layer
  let hashes : List.Vector α (2 ^ n) ←
    List.Vector.mmap (fun ⟨left, right⟩ => query (spec := spec α) ⟨left, right⟩) pairs
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
@[simp, grind]
def getRoot {n : ℕ} (cache : Cache α n) : α :=
  (cache 0).get ⟨0, by simp⟩

/-- Figure out the indices of the Merkle tree nodes that are needed to
recompute the root from the given leaf -/
def findNeighbors {n : ℕ} (i : Fin (2 ^ n)) (layer : Fin n) :
    Fin (2 ^ (layer.val + 1)) :=
  -- `finFunctionFinEquiv.invFun` gives the little-endian order, e.g. `6 = 011 little`
  -- so we need to reverse it to get the big-endian order, e.g. `6 = 110 big`
  let bits := (Vector.ofFn (finFunctionFinEquiv.invFun i)).reverse
  -- `6 = 110 big`, `layer = 1`, we get `neighbor = 10 big`
  let m := layer.val + 1
  have hm : m ≤ n := Nat.succ_le_of_lt layer.isLt
  let neighbor : _root_.Vector (Fin 2) m :=
    Vector.ofFn fun j : Fin m =>
      let j' : Fin n := ⟨j.val, lt_of_lt_of_le j.isLt hm⟩
      let bit := bits.get j'
      if j.val = layer.val then bit + 1 else bit
  -- `10 big` => `01 little` => `2`
  finFunctionFinEquiv.toFun neighbor.reverse.get

end

@[simp, grind =]
theorem getRoot_trivial (a : α) : getRoot α <$> (buildMerkleTree α 0 ⟨[a], rfl⟩) = pure a := by
  simp [getRoot, buildMerkleTree, List.Vector.head]

@[simp, grind =]
theorem getRoot_single (a b : α) :
    getRoot α <$> buildMerkleTree α 1 ⟨[a, b], rfl⟩ = (query (spec := spec α) (a, b)) := by
  simp [buildMerkleTree, buildLayer, List.Vector.ofFn, List.Vector.get]
  rfl

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Sibling index in a perfect binary tree layer indexed by `Fin (2 ^ (n + 1))`. -/
def siblingIndex {n : ℕ} (i : Fin (2 ^ (n + 1))) : Fin (2 ^ (n + 1)) :=
  if h : i.val % 2 = 0 then
    ⟨i.val + 1, by
      have hi : i.val < 2 ^ (n + 1) := i.isLt
      have hEven : Even (2 ^ (n + 1)) := by
        exact (Nat.even_pow).2 ⟨even_two, Nat.succ_ne_zero n⟩
      have hmod : (2 ^ (n + 1)) % 2 = 0 := (Nat.even_iff).1 hEven
      have hle : i.val + 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt hi
      have hne : i.val + 1 ≠ 2 ^ (n + 1) := by
        intro hEq
        have hiVal : i.val = 2 ^ (n + 1) - 1 := by grind only
        have hpos : 0 < 2 ^ (n + 1) := by
          exact pow_pos (by decide : 0 < (2 : ℕ)) _
        have hle1 : 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt hpos
        have hmodPred : (2 ^ (n + 1) - 1) % 2 = 1 := by
          have : (2 ^ (n + 1) - 1 + 1) % 2 = 0 := by
            simp [Nat.sub_add_cancel hle1, hmod]
          exact (Nat.succ_mod_two_eq_zero_iff (m := 2 ^ (n + 1) - 1)).1 this
        have : i.val % 2 = 1 := by simp [hiVal, hmodPred]
        grind only
      exact lt_of_le_of_ne hle hne⟩
  else
    ⟨i.val - 1, by
      have hi : i.val < 2 ^ (n + 1) := i.isLt
      grind only [= Lean.Grind.toInt_fin]⟩

/-- Generate a Merkle proof that a given leaf at index `i` is in the Merkle tree. The proof consists
  of the Merkle tree nodes that are needed to recompute the root from the given leaf. -/
def generateProof {n : ℕ} (i : Fin (2 ^ n)) (cache : Cache α n) :
    List.Vector α n :=
  match n with
  | 0 => List.Vector.nil
  | n + 1 =>
      List.Vector.cons ((cache.leaves).get (siblingIndex i))
        (generateProof ⟨i.val / 2, by grind only⟩ (cache.upper))

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
    let i' : Fin (2 ^ n) := ⟨i.val / 2, by grind only⟩
    if signBit = 0 then
      -- `i` is a left child
      let newLeaf ← query (spec := spec α) ⟨leaf, proof.head⟩
      getPutativeRoot i' newLeaf proof.tail
    else
      -- `i` is a right child
      let newLeaf ← query (spec := spec α) ⟨proof.head, leaf⟩
      getPutativeRoot i' newLeaf proof.tail

/-- Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
  `root`.
  Works by computing the putative root based on the branch, and comparing that to the actual root.
  Outputs `failure` if the proof is invalid. -/
def verifyProof {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (root : α) (proof : List.Vector α n) :
    OptionT (OracleComp (spec α)) Unit := do
  let putative_root ← getPutativeRoot α i leaf proof
  guard (putative_root = root)

@[grind]
theorem buildLayer_neverFails (α : Type) [inst : DecidableEq α]
    [inst_1 : SampleableType α] [(spec α).DecidableEq]
    (preexisting_cache : (spec α).QueryCache) (n : ℕ)
    (leaves : List.Vector α (2 ^ (n + 1))) : NeverFail
      ((simulateQ (randomOracle (spec := spec α))
        (buildLayer α n leaves)).run preexisting_cache) := by
  grind only [buildLayer, = HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

/--
Building a Merkle tree never results in failure
(no matter what queries have already been made to the oracle before it runs).
-/
@[grind]
theorem buildMerkleTree_neverFails (α : Type) [DecidableEq α]
    [SampleableType α] {n : ℕ} [(spec α).DecidableEq]
    (leaves : List.Vector α (2 ^ n)) (preexisting_cache : (spec α).QueryCache) :
    NeverFail
      ((simulateQ (randomOracle (spec := spec α))
        (buildMerkleTree α n leaves)).run preexisting_cache) := by
  grind only [= HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

/-- A purely functional version of `buildLayer`, given an explicit hash function. -/
def buildLayer_with_hash (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (hashFn : α × α → α) :
    List.Vector α (2 ^ n) :=
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by grind only⟩, leaves.get ⟨2 * i + 1, by grind only⟩))
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
      let i' : Fin (2 ^ n) := ⟨i.val / 2, by grind only⟩
      if signBit = 0 then
        let newLeaf := hashFn (leaf, proof.head)
        getPutativeRoot_with_hash i' newLeaf proof.tail hashFn
      else
        let newLeaf := hashFn (proof.head, leaf)
        getPutativeRoot_with_hash i' newLeaf proof.tail hashFn

@[simp, grind =]
lemma runWithOracle_query (f : (spec α).FunctionType) (x : α × α) :
    runWithOracle f (liftM (query x)) = f x := by
  unfold runWithOracle simulateQ
  simp_all only [range_def]
  obtain ⟨fst, snd⟩ := x
  rfl


@[simp, grind =]
lemma runWithOracle_listVector_mmap_query (f : (spec α).FunctionType) {m : ℕ}
    (xs : List.Vector (α × α) m) :
    runWithOracle f
        (List.Vector.mmap (fun x => liftM (query x)) xs) =
      xs.map f := by
  induction xs using List.Vector.inductionOn with
  | nil =>
    unfold runWithOracle simulateQ List.Vector.mmap
    simp_all only [vector_eq_nil, domain_def]
  | @cons m x xs ih =>
    unfold runWithOracle simulateQ at *
    simp_all only [domain_def, Nat.succ_eq_add_one, Vector.mmap_cons, bind_pure_comp,
      PFunctor.FreeM.mapM_bind', PFunctor.FreeM.mapM_map, Id.run_bind, Id.run_map, Vector.map_cons]
    obtain ⟨fst, snd⟩ := x
    rfl

@[simp, grind =]
lemma runWithOracle_buildLayer (f : (spec α).FunctionType) (n : ℕ)
    (leaves : List.Vector α (2 ^ (n + 1))) :
    runWithOracle f (buildLayer α n leaves) =
      buildLayer_with_hash (α := α) n leaves f := by
  unfold buildLayer
  simp_all only [range_def, eq_mp_eq_cast, cast_eq, bind_pure, runWithOracle_listVector_mmap_query,
    domain_def]
  rfl

@[simp, grind =]
lemma runWithOracle_buildMerkleTree (f : (spec α).FunctionType) (n : ℕ)
    (leaves : List.Vector α (2 ^ n)) :
    runWithOracle f (buildMerkleTree α n leaves) =
      buildMerkleTree_with_hash (α := α) n leaves f := by
  induction n with
  | zero =>
    simp_all only [Cache, Nat.reduceAdd, buildMerkleTree, Nat.pow_zero, eq_mpr_eq_cast]
    rfl
  | succ n ih =>
    -- Establish that `runWithOracle f` distributes over monadic bind.
    -- Proved by unfolding to `PFunctor.FreeM.mapM` and using `mapM_bind'`,
    -- exactly as in the other `runWithOracle_*` lemmas in this file.
    have rwb : ∀ {β γ : Type} (ma : OracleComp (spec α) β) (k : β → OracleComp (spec α) γ),
        runWithOracle f (ma >>= k) = runWithOracle f (k (runWithOracle f ma)) := by
      intros β γ ma k
      unfold runWithOracle simulateQ
      simp [PFunctor.FreeM.mapM_bind']
    -- Establish that `runWithOracle f (pure a) = a`.
    have rwp : ∀ {β : Type} (a : β),
        runWithOracle f (pure a : OracleComp (spec α) β) = a := by
      intros β a
      unfold runWithOracle simulateQ
      simp [PFunctor.FreeM.mapM_pure]
    -- Unfold one step of each side, then push `runWithOracle f` inside using
    -- `rwb` (twice, for the two binds), then close via `runWithOracle_buildLayer`,
    -- the induction hypothesis `ih`, and `rwp` for the final `pure`.
    simp only [buildMerkleTree, buildMerkleTree_with_hash]
    simp only [rwb, runWithOracle_buildLayer, ih, rwp]

@[simp, grind =]
lemma runWithOracle_getPutativeRoot (f : (spec α).FunctionType) {n : ℕ} (i : Fin (2 ^ n))
    (leaf : α) (proof : List.Vector α n) :
    runWithOracle f (getPutativeRoot α i leaf proof) =
      getPutativeRoot_with_hash (α := α) i leaf proof f := by
  induction n generalizing leaf with
  | zero =>
    simp_all only [getPutativeRoot, vector_eq_nil]
    rfl
  | succ n ih =>
    by_cases hsign : i.val % 2 = 0
    · simp [getPutativeRoot, getPutativeRoot_with_hash, hsign]
      apply ih
    · simp [getPutativeRoot, getPutativeRoot_with_hash, hsign]
      simp_all only [Nat.mod_two_not_eq_zero]
      apply ih

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
    simp only [buildMerkleTree_with_hash, Fin.isValue, Nat.pow_zero, getPutativeRoot_with_hash,
      getRoot, Fin.zero_eta, Vector.get_zero, List.Vector.head]
    simp_all only [Fin.isValue, Nat.reduceAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.pow_zero, eq_mpr_eq_cast,
      cast_eq, Nat.succ_eq_add_one, length_cons]
    split
    rename_i x a tail property
    simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
    rfl
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
      have hright : 2 * (i.val / 2) + 1 = i.val + 1 := by grind only
      have hnew :
          hashFn (leaves.get i, leaves.get (siblingIndex i)) =
            lastLayer.get ⟨i.val / 2, by grind only⟩ := by
        simp [lastLayer, buildLayer_with_hash, siblingIndex, hsign, hdiv]
      -- Unfold and apply the induction hypothesis on the upper tree.
      -- `generateProof` and `getRoot` reduce via `Cache.upper_cons` and `Cache.leaves_cons`.

      simp [buildMerkleTree_with_hash, lastLayer, generateProof,
        getPutativeRoot_with_hash, getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer, upperCache] using
        (ih (leaves := lastLayer) (i := ⟨i.val / 2, by grind only⟩))
    · -- Right child: sibling is `i - 1`.
      have hmod1 : i.val % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one i.val with h0 | h1
        · exact (hsign h0).elim
        · exact h1
      have hdiv : 2 * (i.val / 2) = i.val - 1 := by
        have h := Nat.mod_add_div i.val 2
        -- `i % 2 = 1` implies `1 + 2 * (i / 2) = i`.
        have : 1 + 2 * (i.val / 2) = i.val := by simpa [hmod1] using h
        grind only
      have hright : 2 * (i.val / 2) + 1 = i.val := by grind only
      have hnew :
          hashFn (leaves.get (siblingIndex i), leaves.get i) =
            lastLayer.get ⟨i.val / 2, by grind only⟩ := by
        have hiPos : 1 ≤ i.val := by grind only
        have hi' :
            (⟨i.val - 1 + 1, by simp [Nat.sub_add_cancel hiPos]⟩ :
                Fin (2 ^ (n + 1))) =
              i := by
          ext
          simp [Nat.sub_add_cancel hiPos]
        simp [lastLayer, buildLayer_with_hash, siblingIndex, hmod1, hdiv, hi']
      simp [buildMerkleTree_with_hash, lastLayer, generateProof,
        getPutativeRoot_with_hash, getRoot, hsign, hnew]
      simpa [getRoot, Cache.cons, lastLayer, upperCache] using
        (ih (leaves := lastLayer) (i := ⟨i.val / 2, by grind only⟩))

omit [Inhabited α] [Fintype α] in
/-- Completeness theorem for Merkle trees: for any full binary tree with `2 ^ n` leaves, and for any
  index `i`, the verifier accepts the opening proof at index `i` generated by the prover.
-/
theorem completeness [SampleableType α] {n : ℕ} [(spec α).DecidableEq]
    (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n))
    (preexisting_cache : (spec α).QueryCache) :
    NeverFail ((
      simulateQ (randomOracle (spec := spec α)) (do
        let cache ← buildMerkleTree α n leaves
        let proof := generateProof α i cache
        let _ ← verifyProof α i leaves[i] (getRoot α cache) proof)).run preexisting_cache :
      ProbComp (Unit × (spec α).QueryCache)) := by
  grind only [= HasEvalSPMF.neverFail_iff, = HasEvalPMF.probFailure_eq_zero]

-- theorem soundness (i : Fin (2 ^ n)) (leaf : α) (proof : Vector α n) :
--     verifyMerkleProof i leaf proof = pure true →
--     getMerkleRoot (buildMerkleTree n (leaf ::ᵥ proof)) = leaf := sorry

end

end MerkleTree
