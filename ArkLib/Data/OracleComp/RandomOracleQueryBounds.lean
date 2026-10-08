/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Structural query budgets for logged random-oracle execution

A bound on hash calls controls the actual ordered hash log under lazy sampling, with any initial
cache. Private uniform draws are unrestricted. Deduplication then bounds the distinct queried keys,
including on computations that return a failure value after making queries.
-/

@[expose] public section

open OracleSpec

namespace OracleComp

/-- A structural hash-call cap bounds every actual logged execution, including cache hits. -/
theorem randomOracleLoggedRun_log_length_le_queryBound {D α : Type} {R : D → Type}
    [DecidableEq D] [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α) (Q : ℕ)
    (hbound : oa.IsQueryBoundP (fun q => q.isRight) Q)
    (cache : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun oa cache)) :
    z.1.2.length ≤ Q := by
  induction oa using OracleComp.inductionOn generalizing Q cache z with
  | pure x =>
      simp [randomOracleLoggedRun] at hz
      subst z
      simp
  | query_bind t next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [randomOracleLoggedRun_bind, support_bind] at hz
      simp only [Set.mem_iUnion, support_map] at hz
      obtain ⟨p, hp, r, hr, rfl⟩ := hz
      cases t with
      | inl coin =>
          rw [randomOracleLoggedRun_uniformQuery, support_map] at hp
          obtain ⟨u, _, rfl⟩ := hp
          simpa using ih u Q (by simpa using hbound.2 u) cache r hr
      | inr key =>
          rw [randomOracleLoggedRun_hashQuery, support_map] at hp
          obtain ⟨u, _, rfl⟩ := hp
          have hn : 0 < Q := by simpa using hbound.1
          have ht := ih u.1 (Q - 1) (by simpa using hbound.2 u.1) u.2 r hr
          simp only [List.singleton_append, List.length_cons]
          omega
/-- The distinct-key count is bounded by the structural hash-call budget. -/
theorem randomOracleLoggedRun_distinctKeys_le_queryBound {D α : Type} {R : D → Type}
    [DecidableEq D] [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α) (Q : ℕ)
    (hbound : oa.IsQueryBoundP (fun q => q.isRight) Q)
    (cache : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun oa cache)) :
    (freshKeysOfLog z.1.2).card ≤ Q := by
  exact (List.toFinset_card_le _).trans (by
    simpa only [List.length_map] using
      randomOracleLoggedRun_log_length_le_queryBound oa Q hbound cache z hz)

/-- Adding a full private-coin/hash log preserves the structural hash-call budget. -/
theorem hashQueryBound_withQueryLog {D α : Type} {R : D → Type}
    (oa : OracleComp (unifSpec + ofFn R) α) (Q : ℕ)
    (hbound : oa.IsQueryBoundP (fun q => q.isRight) Q) :
    oa.withQueryLog.IsQueryBoundP (fun q => q.isRight) Q := by
  apply (isQueryBoundP_run_simulateQ_withLogging_iff _ _ _ _).mpr
  simpa using hbound
end OracleComp
