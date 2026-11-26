/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.FunctionalCommitment.OneMessage
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Binding
public import VCVio.CryptoFoundations.MerkleTree.Inductive.Completeness
public import ToMathlib.Data.IndexedBinaryTree.Equiv

/-!
# Merkle trees as a functional commitment

This file presents VCVio's inductive Merkle tree (`InductiveMerkleTree`) as a functional
commitment in the random oracle model. The shared oracle is the hash `InductiveMerkleTree.spec α`,
which answers a pair `(l, r) : α × α` with a hash value in `α`.

For a fixed tree shape `s`, the data is a tree of leaf values `d : LeafData α s`, a query is a
leaf index `idx`, and the answer is the leaf value `d.get idx` (`Merkle.leafInterface`). Setup
returns `()`, the commitment is the root of the hash tree that `buildMerkleTree` computes, the
committer keeps that whole tree, and the opening proof at `idx` is the authentication path
`generateProof tree idx`. The verifier runs `verifyProof`, which queries the hash.

## Main statements

* `FunctionalCommitment.Merkle.correctness`: with the lazy random oracle as the ambient
  implementation, the scheme is correct with error `0` from every starting cache.
* `FunctionalCommitment.Merkle.exists_collision_of_accepts`: if every claim recomputes the same
  root under a hash function `h` and no tree of leaf values is consistent with the claims, then
  `h` has a collision. This is the deterministic core of function binding.
* `FunctionalCommitment.Merkle.exists_collision_of_check`: the same statement for the Merkle
  check run with a fixed hash table `f`.
* `FunctionalCommitment.Merkle.exists_collision_of_plainGame`: if the plain function-binding game
  can return `true` when the hash answers with the table `f`, then `f` has a collision.

A probability bound for function binding in the random oracle model, through a birthday bound
on the game's hash queries, is left for later work.

## References

* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat–Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

@[expose] public section

open OracleComp OracleSpec Interaction BinaryTree InductiveMerkleTree
open scoped ENNReal

namespace FunctionalCommitment.Merkle

variable (α : Type) (s : Skeleton)

/-- The leaf interface of a tree shape `s`: a query is a leaf index, and the answer is the leaf
value at that index. -/
@[reducible]
def leafInterface : OracleInterface (LeafData α s) where
  Query := SkeletonLeafIndex s
  spec := SkeletonLeafIndex s →ₒ α
  answer d idx := d.get idx

/-- With a fixed hash table `f`, a hash computation lifted into `unifSpec + spec α` returns its
value under `f`. -/
theorem simulateQ_unifFwdAnswerImpl_liftComp {β : Type}
    (f : QueryImpl (InductiveMerkleTree.spec α) Id)
    (oa : OracleComp (InductiveMerkleTree.spec α) β) :
    simulateQ (unifFwdAnswerImpl f) (liftComp oa (unifSpec + InductiveMerkleTree.spec α)) =
      pure (simulateQ f oa) := by
  unfold unifFwdAnswerImpl
  erw [QueryImpl.simulateQ_add_liftComp_right, simulateQ_liftTarget]
  rfl

variable [DecidableEq α]

/-- The Merkle check: recompute the root from the leaf value and the authentication path with
hash queries, and compare it with the commitment. -/
def check (_ : PUnit) (root : α) (idx : SkeletonLeafIndex s) (leaf : α)
    (proof : List.Vector α idx.depth) : OracleComp (InductiveMerkleTree.spec α) Bool :=
  verifyProof idx leaf root proof

/-- The Merkle tree as a functional commitment over the hash oracle. Commit builds the hash tree,
returns its root and keeps the tree; the opening proof at `idx` is the authentication path. -/
abbrev functionalCommitment :
    FunctionalCommitment (InductiveMerkleTree.spec α) (LeafData α s) (leafInterface α s) :=
  oneMessage (PP := PUnit) (Cm := α) (Aux := FullData α s)
    (Proof := fun idx => List.Vector α idx.depth)
    (pure ⟨⟩)
    (fun _ d => (fun tree => (tree.getRootValue, tree)) <$>
      liftComp (buildMerkleTree (m := OracleComp (InductiveMerkleTree.spec α)) d)
        (unifSpec + InductiveMerkleTree.spec α))
    (fun _ _ _ tree idx => pure (generateProof tree idx))
    (check α s)

/-- **Correctness.** With the lazy random oracle as the ambient implementation, the Merkle
functional commitment is correct with error `0` from every starting cache, for every challenge
sampler and every set of query choosers. -/
theorem correctness [SampleableType α] (cache : (InductiveMerkleTree.spec α).QueryCache)
    (chal : (functionalCommitment α s).ChallengeSampler)
    (Adv : Set (functionalCommitment α s).QueryChooser) :
    (functionalCommitment α s).Correctness (pure cache) (InductiveMerkleTree.spec α).randomOracle
      chal Adv 0 := by
  intro d chooser _
  rw [tsub_zero]
  refine le_of_eq (Eq.symm ?_)
  have key := (prEvent_eq_one_simulateQ_romImpl_run_iff
    ((functionalCommitment α s).correctnessGame chal d chooser) cache (fun b => b = true)).2 ?_
  · simp only [correctnessExperiment, runGame, LawfulMonad.pure_bind, StateT.run'_eq,
      Functor.map_map]
    exact key
  intro f _
  rw [prEvent_eq_one_iff]
  intro b hb
  rw [correctnessGame_oneMessage] at hb
  simp only [oneMessageCorrectnessGame, simulateQ_bind, simulateQ_pure, simulateQ_map,
    simulateQ_unifFwdAnswerImpl_liftComp, simulateQ_buildMerkleTree, check, verifyProof,
    simulateQ_getPutativeRoot, mem_support_bind_iff, support_pure, support_map,
    Set.mem_singleton_iff, Set.mem_image] at hb
  obtain ⟨-, -, _, ⟨_, rfl, rfl⟩, idx, -, _, rfl, rfl⟩ := hb
  change ((_ : α) == _) = true
  rw [beq_iff_eq]
  exact functional_completeness idx d fun left right => f (left, right)

/-! ### Function binding -/

omit [DecidableEq α] in
/-- **Binding, deterministic core.** Fix a hash function `h`. Suppose every claim
`(idxᵢ, xᵢ, πᵢ)` recomputes the root `root` under `h`, and no tree of leaf values is consistent
with the claimed leaf values. Then two claims share a leaf index and differ in value, and `h` has
a collision. -/
theorem exists_collision_of_accepts (h : α → α → α) {L : ℕ} (root : α)
    (claims : Fin L → (idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)
    (hacc : ∀ i, getPutativeRootWithHash (claims i).1 (claims i).2.1 (claims i).2.2 h = root)
    (hnc : ¬ ∃ d : LeafData α s, ∀ i, d.get (claims i).1 = (claims i).2.1) :
    ∃ l₁ r₁ l₂ r₂, Collision h l₁ r₁ l₂ r₂ := by
  classical
  by_contra hcol
  have hagree : ∀ i j, (claims i).1 = (claims j).1 → (claims i).2.1 = (claims j).2.1 := by
    intro i j hij
    by_contra hne
    have hi := hacc i
    have hj := hacc j
    rcases hci : claims i with ⟨qi, xi, πi⟩
    rcases hcj : claims j with ⟨qj, xj, πj⟩
    rw [hci] at hi hij hne
    rw [hcj] at hj hij hne
    subst hij
    obtain ⟨l₁, r₁, l₂, r₂, -, hc⟩ :=
      getPutativeRootWithHash_binding_collision h qi πi πj xi xj hne (hi.trans hj.symm)
    exact hcol ⟨l₁, r₁, l₂, r₂, hc⟩
  refine hnc ⟨LeafData.ofFun s fun idx =>
    if hex : ∃ i, (claims i).1 = idx then (claims hex.choose).2.1 else root, fun i => ?_⟩
  have hex : ∃ j, (claims j).1 = (claims i).1 := ⟨i, rfl⟩
  rw [LeafData.get_ofFun, dite_eq_left_of_eq_true (eq_true hex)]
  exact hagree _ _ hex.choose_spec

/-- **Binding through the plain game.** Fix the hash function to a table `f`. If the Merkle check
under `f` accepts every claim of a plain function-binding output and no data is consistent with
the claims, then `f` has a collision. -/
theorem exists_collision_of_check (f : QueryImpl (InductiveMerkleTree.spec α) Id) {L : ℕ}
    (root : α) (claims : Fin L → (idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)
    (hacc : ∀ i, simulateQ f (check α s ⟨⟩ root (claims i).1 (claims i).2.1 (claims i).2.2) = true)
    (hnc : noConsistentData (I := leafInterface α s)
      (fun i => ⟨(claims i).1, (claims i).2.1⟩) = true) :
    ∃ l₁ r₁ l₂ r₂, Collision (fun l r => f (l, r)) l₁ r₁ l₂ r₂ := by
  refine exists_collision_of_accepts α s _ root claims (fun i => ?_)
    ((noConsistentData_eq_true_iff _).1 hnc)
  have hi := hacc i
  simp only [check, verifyProof, simulateQ_bind, simulateQ_getPutativeRoot, simulateQ_pure] at hi
  exact beq_iff_eq.1 hi

/-- Simulating a sequence of computations runs the simulated computations in sequence. -/
theorem simulateQ_mOfFn {ι' : Type} {spec' : OracleSpec ι'} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec' m) {β : Type} :
    (L : ℕ) → (g : Fin L → OracleComp spec' β) →
    simulateQ impl (Fin.mOfFn L g) = Fin.mOfFn L fun i => simulateQ impl (g i)
  | 0, _ => by simp only [Fin.mOfFn_zero, simulateQ_pure]
  | L + 1, g => by
    simp only [Fin.mOfFn_succ, simulateQ_bind, simulateQ_pure, simulateQ_mOfFn impl L]

/-- **Binding in the plain game with a fixed hash table.** If the plain function-binding game of
the Merkle scheme can return `true` when the hash answers with the table `f`, then `f` has a
collision. -/
theorem exists_collision_of_plainGame
    (f : QueryImpl (InductiveMerkleTree.spec α) Id) {L : ℕ}
    (B : PlainAdversary (InductiveMerkleTree.spec α) PUnit α
      (I := leafInterface α s) (fun idx => List.Vector α idx.depth) L)
    (hwin : true ∈ support (simulateQ (unifFwdAnswerImpl f)
      (plainFunctionBindingGame (pure ⟨⟩) (check α s) L B))) :
    ∃ l₁ r₁ l₂ r₂, Collision (fun l r => f (l, r)) l₁ r₁ l₂ r₂ := by
  simp only [plainFunctionBindingGame, simulateQ_bind, simulateQ_pure, simulateQ_mOfFn,
    simulateQ_unifFwdAnswerImpl_liftComp, Fin.mOfFn_pure, LawfulMonad.pure_bind,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hwin
  obtain ⟨out, -, hout⟩ := hwin
  rw [eq_comm, Bool.and_eq_true, decide_eq_true_eq] at hout
  exact exists_collision_of_check α s f out.1 out.2 hout.1 hout.2

end FunctionalCommitment.Merkle
