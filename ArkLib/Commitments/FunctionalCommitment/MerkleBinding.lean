/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.FunctionalCommitment.Merkle
public import VCVio.CryptoFoundations.MerkleTree.Inductive.QueryBound
public import VCVio.EvalDist.IndepProduct
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.MapLens
public import VCVio.OracleComp.QueryTracking.Birthday
public import VCVio.OracleComp.QueryTracking.QueryBound.FinMOfFn
public import VCVio.OracleComp.QueryTracking.QueryBound.Hazard
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial

/-!
# Fixed-claim binding for Merkle trees

Two accepted openings that disagree at the same leaf reach the same root. Their paths
therefore contain distinct hash inputs with the same answer. The verifier queries both
inputs, so the random oracle records the collision in the cache of the winning run.
-/

@[expose] public section

open OracleComp OracleSpec BinaryTree InductiveMerkleTree
open scoped ENNReal BigOperators

namespace FunctionalCommitment.Merkle

variable {α : Type} {s : Skeleton}

/-- The cache records every hash step from the claimed leaf to the root along this path. -/
def ChainInCache (cache : (spec α).QueryCache) (leaf root : α)
    (idx : SkeletonLeafIndex s) (proof : List.Vector α idx.depth) : Prop :=
  simulateQ cache.toPartialImpl (getPutativeRoot (m := OracleComp (spec α)) idx leaf proof) =
    some root

private theorem simulateQ_partial_singleHash (cache : (spec α).QueryCache) (left right : α) :
    simulateQ cache.toPartialImpl (singleHash (m := OracleComp (spec α)) left right) =
      cache (left, right) := by
  change simulateQ cache.toPartialImpl (liftM ((spec α).query (left, right))) = _
  rw [simulateQ_spec_query, QueryCache.toPartialImpl_apply]

/-- Two paths from different values at the same leaf to the same root give two distinct
hash inputs for which the cache records the same answer. -/
theorem cacheHasCollision_of_conflictingPaths (idx : SkeletonLeafIndex s)
    {cache : (spec α).QueryCache} {root x y : α}
    {proof₁ proof₂ : List.Vector α idx.depth} (hne : x ≠ y)
    (h₁ : ChainInCache cache x root idx proof₁) (h₂ : ChainInCache cache y root idx proof₂) :
    CacheHasCollision cache := by
  by_contra hno
  induction idx generalizing root with
  | ofLeaf =>
    exact hne (Option.some.inj (h₁.trans h₂.symm))
  | ofLeft idx ih | ofRight idx ih =>
    simp only [ChainInCache, getPutativeRoot, simulateQ_bind, simulateQ_partial_singleHash] at h₁ h₂
    obtain ⟨child₁, hpath₁, hhash₁⟩ := Option.bind_eq_some_iff.mp h₁
    obtain ⟨child₂, hpath₂, hhash₂⟩ := Option.bind_eq_some_iff.mp h₂
    have hp := cache_lookup_eq_of_noCollision hno hhash₁ ⟨root, hhash₂, HEq.rfl⟩
    have heq : child₁ = child₂ := by
      first | exact congrArg Prod.fst hp | exact congrArg Prod.snd hp
    subst child₂
    exact ih hpath₁ hpath₂

private theorem cacheHasCollision_of_inconsistentClaims {L : ℕ}
    {cache : (spec α).QueryCache} {root : α}
    (claims : Fin L → (idx : SkeletonLeafIndex s) × α × List.Vector α idx.depth)
    (hacc : ∀ i, ChainInCache cache (claims i).2.1 root (claims i).1 (claims i).2.2)
    (hnc : ¬ ∃ d : LeafData α s, ∀ i, d.get (claims i).1 = (claims i).2.1) :
    CacheHasCollision cache := by
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
    exact hcol (cacheHasCollision_of_conflictingPaths _ hne hi hj)
  refine hnc ⟨LeafData.ofFun s fun idx =>
    if hex : ∃ i, (claims i).1 = idx then (claims hex.choose).2.1 else root, fun i => ?_⟩
  have hex : ∃ j, (claims j).1 = (claims i).1 := ⟨i, rfl⟩
  rw [LeafData.get_ofFun, dite_eq_left_of_eq_true (eq_true hex)]
  exact hagree _ _ hex.choose_spec

/-- Whenever the plain fixed-claim game wins, its final random-oracle cache contains
two distinct hash inputs with the same answer. -/
theorem cacheHasCollision_of_plainGame_win [DecidableEq α] [SampleableType α]
    (s : Skeleton) {L : ℕ}
    (B : PlainAdversary (spec α) PUnit α
      (I := leafInterface α s) (fun idx => List.Vector α idx.depth) L)
    {cache : (spec α).QueryCache}
    (hwin : (true, cache) ∈ support ((simulateQ (ambientImpl (spec α).randomOracle)
      (plainFixedClaimBindingGame (pure ⟨⟩) (check α s) L B)).run ∅)) :
    CacheHasCollision cache := by
  simp only [plainFixedClaimBindingGame, LawfulMonad.pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hwin
  obtain ⟨⟨⟨root, claims⟩, c⟩, -, ⟨verdicts, finalCache⟩, hchecks, hresult⟩ := hwin
  obtain ⟨hwin, hcache⟩ := Prod.mk.inj hresult
  change cache = finalCache at hcache
  subst finalCache
  rw [eq_comm, Bool.and_eq_true, decide_eq_true_eq] at hwin
  -- Replay the whole verification batch using the hash answers in the final cache.
  let checks (i : Fin L) := check α s ⟨⟩ root (claims i).1 (claims i).2.1 (claims i).2.2
  have heq : (simulateQ (spec α).randomOracle (Fin.mOfFn L checks)).run c =
      (simulateQ (ambientImpl (spec α).randomOracle)
        (Fin.mOfFn L fun i => liftComp (checks i) (unifSpec + spec α))).run c := by
    simp only [simulateQ_mOfFn, ambientImpl, QueryImpl.simulateQ_add_liftComp_right]
  change (verdicts, cache) ∈ support _ at hchecks
  rw [← heq] at hchecks
  have replay := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    _ (Fin.mOfFn L checks) hchecks
  rw [simulateQ_mOfFn] at replay
  refine cacheHasCollision_of_inconsistentClaims claims (root := root) (fun i => ?_)
    ((noConsistentData_eq_true_iff _).1 hwin.2)
  have hi := mem_support_mOfFn L (fun i => simulateQ cache.toPartialImpl (checks i)) verdicts
    (by rw [replay]; rfl) i
  have haccept := (Option.mem_def.mp hi).trans (congrArg some (hwin.1 i))
  simp only [checks, check, verifyProof, simulateQ_bind, simulateQ_pure] at haccept
  obtain ⟨r, hpath, hroot⟩ := Option.bind_eq_some_iff.mp haccept
  have heq : r = root := beq_iff_eq.mp (Option.some.inj hroot)
  exact heq ▸ hpath

private theorem plainGame_queryBound
    (α : Type) [DecidableEq α] (s : Skeleton) {L b : ℕ}
    (B : PlainAdversary (spec α) PUnit α
      (I := leafInterface α s) (fun idx => List.Vector α idx.depth) L)
    (h : IsQueryBoundP (B ⟨⟩) (fun t => t.isRight = true) b) :
    IsQueryBoundP (plainFixedClaimBindingGame (pure ⟨⟩) (check α s) L B)
      (fun t => t.isRight = true) (b + L * s.depth) := by
  simp only [plainFixedClaimBindingGame, pure_bind]
  refine isQueryBoundP_bind h fun out _ => ?_
  let checks : Fin L → OracleComp (unifSpec + spec α) Bool := fun i =>
    liftComp (check α s ⟨⟩ out.1 (out.2 i).1 (out.2 i).2.1 (out.2 i).2.2) _
  have htotal : IsTotalQueryBound (Fin.mOfFn L checks) (L * s.depth) := by
    refine isTotalQueryBound_fin_mOfFn checks fun i => ?_
    dsimp only [checks, check]
    rw [liftComp_add_right_eq_mapLens]
    exact (verifyProof_isTotalQueryBound_skeleton_depth _ _ _ _).mapLens _
  have hchecks : IsQueryBoundP (Fin.mOfFn L checks) (fun t => t.isRight = true)
      (L * s.depth) := htotal.isQueryBoundP
  simpa only [Nat.add_zero] using
    (isQueryBoundP_bind (m := 0) hchecks fun _ _ => isQueryBoundP_pure _ _ _)

private def populatedKeys [DecidableEq α] [Fintype α] (cache : (spec α).QueryCache) :
    Finset (α × α) :=
  Finset.univ.filter fun t => cache t ≠ none

private theorem populatedKeys_cacheQuery [DecidableEq α] [Fintype α]
    (cache : (spec α).QueryCache) (t : α × α) (u : α) :
    populatedKeys (cache.cacheQuery t u) = insert t (populatedKeys cache) := by
  ext t'
  by_cases h : t' = t
  · subst t'
    simp [populatedKeys]
  · simp [populatedKeys, h]

private theorem mixedBirthday {β : Type} [DecidableEq α] [Fintype α] [SampleableType α]
    (program : OracleComp (unifSpec + spec α) β) {q : ℕ}
    (hq : IsQueryBoundP program (fun t => t.isRight = true) q) :
    Pr{let z ← (simulateQ (ambientImpl (spec α).randomOracle) program).run ∅}[
      CacheHasCollision z.2] ≤
      (q.choose 2 : ℝ≥0∞) / Fintype.card α := by
  classical
  let C : ℝ≥0∞ := Fintype.card α
  let cnt (cache : (spec α).QueryCache) := (populatedKeys cache).card
  have hmono : Monotone (fun j : ℕ => (j : ℝ≥0∞) / C) :=
    fun _ _ h => ENNReal.div_le_div_right (Nat.cast_le.mpr h) _
  have hs : ¬ CacheHasCollision (∅ : (spec α).QueryCache) := by
    rintro ⟨t, _, _, _, _, ht, _, _⟩
    simp at ht
  have hcnt : cnt ∅ = 0 := by simp [cnt, populatedKeys]
  -- After j hash queries the cache has at most j entries. A fresh uniform answer
  -- can match at most that many previous answers.
  calc
    _ ≤ ∑ j ∈ Finset.range q, ((cnt ∅ + j : ℕ) : ℝ≥0∞) / C := by
      refine prEvent_simulateQ_run_le_sum_of_isQueryBoundP _ _ cnt (fun _ => True)
        CacheHasCollision _ hmono (QueryImpl.PreservesInv.trivial _) ?_ ?_ ?_
        program hq ∅ trivial hs
      · intro t cache ht _ hgood z hz
        cases t with
        | inl t =>
          rw [unifFwdImpl.snd_eq_of_mem_support_run t cache hz]
          exact ⟨rfl, hgood⟩
        | inr t => exact False.elim (ht rfl)
      · intro t cache ht _ _ z hz
        cases t with
        | inl t => cases ht
        | inr t =>
          have hcache := QueryImpl.withCaching_run_eq_cacheQuery (spec := spec α) _
            (t := t) (cache₀ := cache) (z := z) hz
          change (populatedKeys z.2).card ≤ (populatedKeys cache).card + 1
          rw [hcache, populatedKeys_cacheQuery]
          exact Finset.card_insert_le _ _
      · intro t cache ht _ hgood
        cases t with
        | inl t => cases ht
        | inr t =>
          rw [ambientImpl, QueryImpl.add_apply_inr, randomOracle.run_eq]
          cases hc : cache t with
          | some u =>
            rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => by
              rw [mem_support_pure_iff] at hz
              exact hz ▸ hgood]
            exact zero_le
          | none =>
            let step (u : α) := (u, cache.cacheQuery t u)
            change Pr{let z ← ($ᵗ α) >>= pure ∘ step}[CacheHasCollision z.2] ≤ _
            rw [← map_eq_bind_pure_comp ProbComp step, prEvent_map]
            apply (SampleableType.prEvent_uniformSample_le_div_iff _).mpr
            exact card_responses_creating_cacheCollision_le hgood
              (fun t ht => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
    _ = (q.choose 2 : ℝ≥0∞) / Fintype.card α := by
      simp only [hcnt, Nat.zero_add, div_eq_mul_inv, ← Finset.sum_mul, C]
      have hsum : ∑ j ∈ Finset.range q, j = q.choose 2 := by
        rw [Finset.sum_range_id, Nat.choose_two_right]
      rw [← hsum]
      congr 1
      exact (Nat.cast_sum _ _).symm

/-- An adversary that makes at most `b` hash queries, including queries from its proof producers,
wins the Merkle fixed-claim binding game with probability at most
`(b + L * s.depth).choose 2 / Fintype.card α`. The verifier makes at most `s.depth` additional
hash queries for each of the `L` claims. Private coins do not count toward either budget. -/
theorem fixedClaimBindingAdvantage_le_birthday
    (α : Type) [DecidableEq α] [Fintype α] [SampleableType α]
    (s : Skeleton) (L b : ℕ) (chal : (functionalCommitment α s).ChallengeSampler)
    (A : (functionalCommitment α s).FixedClaimAdversary L)
    (h : IsQueryBoundP (toPlainAdversary A ⟨⟩) (fun t => t.isRight = true) b) :
    (functionalCommitment α s).fixedClaimBindingAdvantage
        (pure ∅) (spec α).randomOracle chal L A ≤
      (((b + L * s.depth).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card α := by
  change (oneMessage _ _ _ (check α s)).fixedClaimBindingAdvantage
    (pure ∅) (spec α).randomOracle chal L A ≤ _
  rw [fixedClaimBindingAdvantage_oneMessage]
  simp only [plainFixedClaimBindingAdvantage, runGame, pure_bind, StateT.run'_eq, prEvent_map]
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (mixedBirthday _ (plainGame_queryBound α s (toPlainAdversary A) h))
  rintro ⟨won, cache⟩ hrun (rfl : won = true)
  exact cacheHasCollision_of_plainGame_win s (toPlainAdversary A) hrun

end FunctionalCommitment.Merkle
