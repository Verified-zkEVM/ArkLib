/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyExecution

/-!
# Value projection of a cached fixed-table execution

The cached interpreter retains the ordered log and a cache. When its initial cache agrees with
the fixed table, forgetting those observations gives direct evaluation at that same table.
-/

@[expose] public section

open OracleComp OracleSpec

namespace Interaction.Oracle.Security.StateRestoration

variable {D A : Type} {R : D → Type}

def FixedTableCacheCompatible (table : ∀ key : D, R key)
    (cache : (OracleSpec.ofFn R).QueryCache) : Prop :=
  ∀ key, cache key = none ∨ cache key = some (table key)

theorem fixedTableCacheCompatible_empty
    (table : ∀ key : D, R key) :
    FixedTableCacheCompatible table ∅ := by
  intro key
  left
  rfl

theorem fixedTableCacheCompatible_insert [DecidableEq D]
    (table : ∀ key : D, R key)
    (cache : (OracleSpec.ofFn R).QueryCache)
    (hcache : FixedTableCacheCompatible table cache) (key : D) :
    FixedTableCacheCompatible table (cache.cacheQuery key (table key)) := by
  intro other
  by_cases h : other = key
  · subst other
    right
    simp
  · simpa [OracleSpec.QueryCache.cacheQuery, Function.update, h] using hcache other

/-- Erasing the cache and log of a compatible fixed-table execution preserves the value
distribution, including every independent private-uniform draw. -/
theorem fixedTableLoggedRun_value [DecidableEq D]
    (table : ∀ key : D, R key)
    (program : OracleComp (unifSpec + OracleSpec.ofFn R) A)
    (cache : (OracleSpec.ofFn R).QueryCache)
    (hcache : FixedTableCacheCompatible table cache) :
    (fun result => result.1.1) <$> fixedTableLoggedRun program table cache =
      simulateQ (unifSpec.passthrough + (QueryImpl.ofFn table).liftTarget ProbComp)
        program := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure a => simp [fixedTableLoggedRun]
  | query_bind query next ih =>
      cases query with
      | inl coin =>
          rw [fixedTableLoggedRun_bind, fixedTableLoggedRun_uniformQuery]
          simp only [map_bind, bind_map_left, Functor.map_map,
            simulateQ_bind, simulateQ_query]
          simp only [HasQuery.toQueryImpl_apply, HasQuery.instOfMonadLift_query,
            add_apply_inl, OracleQuery.input_query, QueryImpl.passthrough_add,
            PFunctor.Handler.liftTarget_self, QueryImpl.add_apply_inl,
            QueryImpl.id'_apply, OracleQuery.cont_query, id_eq]
          apply bind_congr
          intro answer
          simpa only [List.nil_append, Functor.map_map,
            QueryImpl.passthrough_add, QueryImpl.liftTarget_self]
            using ih answer cache hcache
      | inr key =>
          rw [fixedTableLoggedRun_bind, fixedTableLoggedRun_hashQuery]
          simp only [map_bind, bind_map_left, Functor.map_map,
            simulateQ_bind, simulateQ_query]
          have hlift : (@liftM Id ProbComp _ (R key) (table key)) =
              pure (table key) := by
            change (liftM (pure (table key) : Id (R key)) : ProbComp (R key)) = _
            exact liftM_pure _
          rcases hcache key with hnone | hsome
          · rw [QueryImpl.withCaching_run_none _ hnone]
            simp [OracleSpec.query, QueryImpl.add_apply_inr]
            have hnext := ih (table key) (cache.cacheQuery key (table key))
              (fixedTableCacheCompatible_insert table cache hcache key)
            simpa only [List.nil_append, Functor.map_map, hlift, pure_bind,
              QueryImpl.passthrough_add, QueryImpl.liftTarget_self] using hnext
          · rw [QueryImpl.withCaching_run_some _ hsome]
            simp [OracleSpec.query, QueryImpl.add_apply_inr]
            have hnext := ih (table key) cache hcache
            simpa only [List.nil_append, Functor.map_map, hlift, pure_bind,
              QueryImpl.passthrough_add, QueryImpl.liftTarget_self] using hnext

end Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security.StateRestoration

open Interaction.Oracle.FiatShamir

/-- Erase the native phase log, fixed-table cache, and interpreter log after the complete run.
This is the same full-table value program used by the operational legacy bridge. -/
theorem fixedTableLoggedRun_restored_value {Input W : Type}
    [DecidableEq Input] (rounds : List Round)
    (table : Table Input PUnit rounds)
    (adversary : RandomizedRestorationAdversary Input PUnit W rounds) :
    (fun joint => joint.1.1.1) <$>
      fixedTableLoggedRun
        (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅ =
      simulateQ (nativeFixedTableCoinImpl rounds table)
        (randomizedRestoredExecution rounds adversary) := by
  have hvalue := fixedTableLoggedRun_value table
    (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅
    (fixedTableCacheCompatible_empty table)
  have hprogram := randomizedRestoredExecutionWithAdversaryLog_erase rounds adversary
  calc
    _ = Prod.fst <$> simulateQ (nativeFixedTableCoinImpl rounds table)
          (randomizedRestoredExecutionWithAdversaryLog rounds adversary) := by
            simpa only [Functor.map_map, Function.comp_def,
              nativeFixedTableCoinImpl] using congrArg (Prod.fst <$> ·) hvalue
    _ = simulateQ (nativeFixedTableCoinImpl rounds table)
          (randomizedRestoredExecution rounds adversary) := by
            rw [← simulateQ_map, hprogram]

end Interaction.Oracle.Security.StateRestoration
