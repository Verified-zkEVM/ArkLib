/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationBudget
public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQueryInfinite

/-!
# Randomized native state restoration

An adversary may interleave independent private uniform samples with restoration-oracle calls.
It returns `none` when it fails to select a transcript. The failure is an ordinary returned value:
the random-oracle cache and query history accumulated before it remain part of the actual run.
When a transcript is selected, completion reads its challenge keys through the same cached oracle.
The native verifier replays precisely that path, and closes any virtual output under that path's
own accumulated handler.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec MeasureTheory
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

universe w

variable {Input Salt W : Type} {rounds : List Round}

/-- The adversary's interleaved private sampling and restoration-oracle effects. Repeated uniform
sampling queries are forwarded to `ProbComp`, so each operation draws a new private sample. -/
abbrev RandomizedRestorationAdversary (Input Salt W : Type) (rounds : List Round) :=
  OracleComp (unifSpec + oracleSpec Input Salt rounds)
    (Option (Input × Messages Salt rounds × W))

/-- Route completion's challenge queries into the cached side of the randomized signature. -/
def restorationQueries (Input Salt : Type) (rounds : List Round) :
    QueryImpl (oracleSpec Input Salt rounds)
      (OracleComp (unifSpec + oracleSpec Input Salt rounds)) :=
  fun key => liftM ((unifSpec + oracleSpec Input Salt rounds).query (.inr key))

/-- Only restoration-oracle calls count as adversarial challenge queries. Private uniform samples
use the other summand and are discarded by this projection. -/
def adversaryHashKeys [DecidableEq Input] [DecidableEq Salt]
    (log : QueryLog (unifSpec + oracleSpec Input Salt rounds)) :
    Finset (Key Input Salt rounds) :=
  (log.snd.map Sigma.fst).toFinset

/-- Completion has exactly one syntactic challenge key at each round, carrying that round's
error. This identity also applies when a key was already cached by the adversary. -/
theorem completionKeys_error_sum (rounds : List Round) (errors : RoundErrors rounds)
    (z : Input) (messages : Messages Salt rounds) :
    ((completionKeys rounds z messages).map (keyError errors)).sum = ∑ j, errors j := by
  induction rounds with
  | nil => cases messages; rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simpa only [completionKeys, List.map_cons, List.sum_cons, List.map_map,
        Function.comp_def, keyError, List.length_cons, Fin.sum_univ_succ]
        using congrArg (fun x : ENNReal => errors 0 + x)
          (ih (fun j => errors j.succ) messages)

/-- Deduplicating a finite nonnegative charge list cannot increase its sum. -/
theorem sum_toFinset_le_list_sum {A : Type} [DecidableEq A]
    (f : A → ENNReal) (items : List A) :
    (∑ a ∈ items.toFinset, f a) ≤ (items.map f).sum := by
  induction items with
  | nil => simp
  | cons a tail ih =>
      simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
      by_cases ha : a ∈ tail.toFinset
      · rw [Finset.insert_eq_of_mem ha]
        exact le_trans ih (le_add_left le_rfl)
      · rw [Finset.sum_insert ha]
        simpa only [add_comm] using add_le_add_left ih (f a)

/-- Distinct challenge-key charge on an ordered hash-query log. -/
noncomputable def roundFreshCharge [DecidableEq Input] [DecidableEq Salt]
    (errors : RoundErrors rounds) (log : QueryLog (oracleSpec Input Salt rounds)) : ENNReal :=
  ∑ key ∈ (log.map Sigma.fst).toFinset, keyError errors key

/-- The joint fresh charge is bounded pointwise by the distinct adversarial challenge keys plus
one completion key per round. No probability estimate or query bound enters this step. -/
theorem roundFreshCharge_append_le [DecidableEq Input] [DecidableEq Salt]
    (errors : RoundErrors rounds)
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (completionLog : QueryLog (oracleSpec Input Salt rounds))
    (z : Input) (messages : Messages Salt rounds)
    (hkeys : completionLog.map Sigma.fst = completionKeys rounds z messages) :
    roundFreshCharge errors (adversaryLog.snd ++ completionLog) ≤
      (adversaryHashKeys adversaryLog).card * Finset.univ.sup errors + ∑ j, errors j := by
  let A : Finset (Key Input Salt rounds) := (adversaryLog.snd.map Sigma.fst).toFinset
  let C : Finset (Key Input Salt rounds) := (completionLog.map Sigma.fst).toFinset
  have hA : (∑ key ∈ A, keyError errors key) ≤ A.card * Finset.univ.sup errors := by
    calc
      (∑ key ∈ A, keyError errors key) ≤ ∑ _key ∈ A, Finset.univ.sup errors :=
        Finset.sum_le_sum (fun key _ => keyError_le_max errors key)
      _ = A.card * Finset.univ.sup errors := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hC : (∑ key ∈ C, keyError errors key) ≤ ∑ j, errors j := by
    calc
      (∑ key ∈ C, keyError errors key) ≤
          ((completionLog.map Sigma.fst).map (keyError errors)).sum :=
        sum_toFinset_le_list_sum (keyError errors) (completionLog.map Sigma.fst)
      _ = ∑ j, errors j := by
        rw [hkeys, completionKeys_error_sum]
  have hUnion :
      (∑ key ∈ A ∪ C, keyError errors key) ≤
        (∑ key ∈ A, keyError errors key) + (∑ key ∈ C, keyError errors key) := by
    calc
      (∑ key ∈ A ∪ C, keyError errors key) ≤
          (∑ key ∈ A ∪ C, keyError errors key) +
            (∑ key ∈ A ∩ C, keyError errors key) := le_add_right le_rfl
      _ = (∑ key ∈ A, keyError errors key) +
          (∑ key ∈ C, keyError errors key) := Finset.sum_union_inter
  have hset : ((adversaryLog.snd ++ completionLog).map Sigma.fst).toFinset = A ∪ C := by
    simp [A, C]
  change (∑ key ∈ ((adversaryLog.snd ++ completionLog).map Sigma.fst).toFinset,
    keyError errors key) ≤ A.card * Finset.univ.sup errors + ∑ j, errors j
  rw [hset]
  exact hUnion.trans (add_le_add hA hC)

/-- A pathwise cap on the actual distinct adversary keys recovers the familiar worst-case
`Q * max + sum` charge without counting repeated cached calls. -/
theorem roundFreshCharge_append_le_queryBound [DecidableEq Input] [DecidableEq Salt]
    (errors : RoundErrors rounds)
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (completionLog : QueryLog (oracleSpec Input Salt rounds))
    (z : Input) (messages : Messages Salt rounds)
    (hkeys : completionLog.map Sigma.fst = completionKeys rounds z messages)
    (Q : ℕ) (hQ : (adversaryHashKeys adversaryLog).card ≤ Q) :
    roundFreshCharge errors (adversaryLog.snd ++ completionLog) ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  calc
    roundFreshCharge errors (adversaryLog.snd ++ completionLog) ≤
        (adversaryHashKeys adversaryLog).card * Finset.univ.sup errors + ∑ j, errors j :=
      roundFreshCharge_append_le errors adversaryLog completionLog z messages hkeys
    _ ≤ Q * Finset.univ.sup errors + ∑ j, errors j := by
      gcongr

/-- The shared extraction failure event. An adversary that returns `none` contributes no bad
extraction event, while its preceding oracle calls remain in the surrounding logged run. -/
def badExtractOnPath (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (result : Option (Input × (protocol rounds).tree.ExecutionPath × W)) : Prop :=
  match result with
  | none => False
  | some (z, path, witness) =>
      z ∈ Z ∧
      ((extractor z).terminalState path).holds (terminalWitness z path witness) ∧
      ¬ (state z).holds ((extractor z).extractWitness path
        (terminalWitness z path witness))

/-- If a completed path has a valid terminal witness but backward extraction fails, one of that
path's actual challenge keys is bad in the same answer table. -/
theorem badExtractOnPath_completion
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (z : Input) (messages : Messages Salt rounds) (witness : W)
    (table : Table Input Salt rounds)
    (bad : badExtractOnPath state extractor Z terminalWitness
      (some (z, completedPath rounds z messages table, witness))) :
    ∃ key ∈ completionKeys rounds z messages,
      badKey state extractor Z key table := by
  change z ∈ Z ∧
    ((extractor z).terminalState (completedPath rounds z messages table)).holds
      (terminalWitness z (completedPath rounds z messages table) witness) ∧
    ¬ (state z).holds ((extractor z).extractWitness
      (completedPath rounds z messages table)
      (terminalWitness z (completedPath rounds z messages table) witness)) at bad
  have hbad := RoundExtractor.extraction_failure_implies_bad_challenge (extractor z)
    (protocol rounds).roles (preserving z bad.1) _ _ bad.2.1 bad.2.2
  obtain ⟨key, hkey, hb⟩ := badChallengeOnPath_completion (extractor z) z messages table _ hbad
  have hz := completionKeys_input rounds z messages key hkey
  refine ⟨key, hkey, ?_⟩
  change key.input ∈ Z ∧ _
  rw [hz]
  exact ⟨bad.1, hb⟩

/-- Continue a logged adversary output through completion, preserving the source phase log. -/
def randomizedCompletionAfterAdversaryLog (rounds : List Round)
    (selectedAndLog : Option (Input × Messages Salt rounds × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) := do
  match selectedAndLog.1 with
  | none => pure (none, selectedAndLog.2)
  | some (z, messages, witness) =>
      let path ← simulateQ (restorationQueries Input Salt rounds) (complete rounds z messages)
      pure (some (z, path, witness), selectedAndLog.2)

/-- Log the adversary before completion to keep the phase boundary as ordinary returned data.
This observes source calls without introducing new uniform or restoration queries. -/
def randomizedRestoredExecutionWithAdversaryLog (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) :=
  adversary.withQueryLog >>= randomizedCompletionAfterAdversaryLog rounds

/-- Complete only a selected transcript. This remains a computation in the original randomized
oracle signature, so the adversary and completion share one stateful random-oracle run. -/
def randomizedRestoredExecution (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option (Input × (protocol rounds).tree.ExecutionPath × W)) := do
  match (← adversary) with
  | none => pure none
  | some (z, messages, witness) =>
      let path ← simulateQ (restorationQueries Input Salt rounds) (complete rounds z messages)
      pure (some (z, path, witness))

/-- Erasing the phase log recovers the ordinary joint adversary and completion program exactly. -/
theorem randomizedRestoredExecutionWithAdversaryLog_erase (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    Prod.fst <$> randomizedRestoredExecutionWithAdversaryLog rounds adversary =
      randomizedRestoredExecution rounds adversary := by
  have hstep (selected : Option (Input × Messages Salt rounds × W))
      (log : QueryLog (unifSpec + oracleSpec Input Salt rounds)) :
      Prod.fst <$> (match selected with
        | none => (pure (none, log) : OracleComp (unifSpec + oracleSpec Input Salt rounds) _)
        | some (z, messages, witness) => do
            let path ← simulateQ (restorationQueries Input Salt rounds)
              (complete rounds z messages)
            pure (some (z, path, witness), log)) =
        (match selected with
        | none => pure none
        | some (z, messages, witness) => do
            let path ← simulateQ (restorationQueries Input Salt rounds)
              (complete rounds z messages)
            pure (some (z, path, witness))) := by
    cases selected with
    | none => rfl
    | some data =>
        rcases data with ⟨z, messages, witness⟩
        simp only [map_bind, map_pure]
  simp only [randomizedRestoredExecutionWithAdversaryLog,
    randomizedCompletionAfterAdversaryLog, randomizedRestoredExecution,
    map_bind]
  simp_rw [hstep]
  let finish : Option (Input × Messages Salt rounds × W) →
      OracleComp (unifSpec + oracleSpec Input Salt rounds)
        (Option (Input × (protocol rounds).tree.ExecutionPath × W)) :=
    fun selected => match selected with
      | none => pure none
      | some (z, messages, witness) => do
          let path ← simulateQ (restorationQueries Input Salt rounds)
            (complete rounds z messages)
          pure (some (z, path, witness))
  change (adversary.withQueryLog >>= fun x => finish x.1) = adversary >>= finish
  exact loggingOracle.run_simulateQ_bind_fst adversary finish

/-- The actual cached interpreter passes the adversary's exact final cache to completion and
appends completion's ordered hash log after the adversary's log. This is a joint law for result,
cache and log, valid also when the adversary returns `none` after making queries. -/
theorem randomizedRestoredExecutionWithAdversaryLog_handoff
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    randomOracleLoggedRun (randomizedRestoredExecutionWithAdversaryLog rounds adversary) cache =
      randomOracleLoggedRun adversary.withQueryLog cache >>= fun phase =>
        (fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
          randomOracleLoggedRun
            (randomizedCompletionAfterAdversaryLog rounds phase.1.1) phase.2 := by
  exact randomOracleLoggedRun_bind adversary.withQueryLog
    (randomizedCompletionAfterAdversaryLog rounds) cache

/-- The fixed-table interpreter has the same state and ordered-log handoff, with private uniform
sampling still interleaved in both phases. -/
theorem randomizedRestoredExecutionWithAdversaryLog_fixedTable_handoff
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    fixedTableLoggedRun (randomizedRestoredExecutionWithAdversaryLog rounds adversary)
        table cache =
      fixedTableLoggedRun adversary.withQueryLog table cache >>= fun phase =>
        (fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
          fixedTableLoggedRun
            (randomizedCompletionAfterAdversaryLog rounds phase.1.1) table phase.2 := by
  exact fixedTableLoggedRun_bind adversary.withQueryLog
    (randomizedCompletionAfterAdversaryLog rounds) table cache

/-- A single private sample contributes no hash-log entry; a single restoration query records
its actual answer, whether the answer came from the cache or the fixed table. -/
private theorem fixedTable_single_query_log
    [DecidableEq Input] [DecidableEq Salt]
    (query : (unifSpec + oracleSpec Input Salt rounds).Domain)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (result : (((unifSpec + oracleSpec Input Salt rounds).Range query ×
      QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (liftM ((unifSpec + oracleSpec Input Salt rounds).query query)) table cache)) :
    result.1.2 = QueryLog.snd ([(⟨query, result.1.1⟩ :
      (q : (unifSpec + oracleSpec Input Salt rounds).Domain) ×
        (unifSpec + oracleSpec Input Salt rounds).Range q)] :
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) := by
  cases query with
  | inl coin =>
      rw [fixedTableLoggedRun_uniformQuery] at supported
      rw [support_map] at supported
      obtain ⟨u, _, rfl⟩ := supported
      rfl
  | inr key =>
      rw [fixedTableLoggedRun_hashQuery] at supported
      rw [support_map] at supported
      obtain ⟨p, _, rfl⟩ := supported
      rfl

/-- Source-level query logging prepends exactly the query and answer before the continuation's
log, with the same oracle effects as the uninstrumented computation. -/
private theorem withQueryLog_query_bind {A : Type}
    (query : (unifSpec + oracleSpec Input Salt rounds).Domain)
    (next : (unifSpec + oracleSpec Input Salt rounds).Range query →
      OracleComp (unifSpec + oracleSpec Input Salt rounds) A) :
    (liftM ((unifSpec + oracleSpec Input Salt rounds).query query) >>= next).withQueryLog =
      (liftM ((unifSpec + oracleSpec Input Salt rounds).query query) >>= fun answer =>
        (fun p => (p.1, (⟨query, answer⟩ :
          (q : (unifSpec + oracleSpec Input Salt rounds).Domain) ×
            (unifSpec + oracleSpec Input Salt rounds).Range q) :: p.2)) <$>
          (next answer).withQueryLog) := by
  exact OracleComp.run_simulateQ_loggingOracle_query_bind query next

/-- Mapping the returned value leaves the fixed-table cache and ordered hash log untouched. -/
theorem fixedTableLoggedRun_map {A B : Type} [DecidableEq Input] [DecidableEq Salt]
    (f : A → B) (program : OracleComp (unifSpec + oracleSpec Input Salt rounds) A)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    fixedTableLoggedRun (f <$> program) table cache =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        fixedTableLoggedRun program table cache := by
  simp [fixedTableLoggedRun, simulateQ_map, StateT.run_map]

/-- The log returned by source instrumentation is the outer fixed-table interpreter's exact
hash-query log for the adversary phase. Uniform samples are omitted from both hash logs. -/
theorem fixedTable_withQueryLog_hashLog_eq {A : Type}
    [DecidableEq Input] [DecidableEq Salt]
    (adversary : OracleComp (unifSpec + oracleSpec Input Salt rounds) A)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (result : ((A × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
      QueryLog (oracleSpec Input Salt rounds)) ×
        (oracleSpec Input Salt rounds).QueryCache)
    (supported : result ∈ support (fixedTableLoggedRun adversary.withQueryLog table cache)) :
    result.1.1.2.snd = result.1.2 := by
  induction adversary using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp [OracleComp.withQueryLog, fixedTableLoggedRun] at supported
      subst result
      rfl
  | query_bind query next ih =>
      rw [withQueryLog_query_bind, fixedTableLoggedRun_bind] at supported
      obtain ⟨phase, hphase, hrest⟩ :=
        (mem_support_bind_iff _ _ _).mp supported
      rw [support_map] at hrest
      obtain ⟨mapped, hmapped, rfl⟩ := hrest
      rw [fixedTableLoggedRun_map, support_map] at hmapped
      obtain ⟨tail, htail, rfl⟩ := hmapped
      have hsource := ih phase.1.1 phase.2 tail htail
      have hone := fixedTable_single_query_log query table cache phase hphase
      simp only [QueryLog.snd, List.filterMap_cons] at hsource hone ⊢
      rw [hsource, hone]
      cases query <;> simp

theorem randomOracleLoggedRun_map {A B : Type}
    [DecidableEq Input] [DecidableEq Salt]
    (f : A → B) (program : OracleComp (unifSpec + oracleSpec Input Salt rounds) A)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    randomOracleLoggedRun (f <$> program) cache =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        randomOracleLoggedRun program cache := by
  simp [randomOracleLoggedRun, simulateQ_map, StateT.run_map]

/-- The source adversary-phase log also agrees with the actual cached interpreter's ordered
hash log, including cache hits and branches that later return `none`. -/
theorem randomOracle_withQueryLog_hashLog_eq {A : Type}
    [DecidableEq Input] [DecidableEq Salt]
    (adversary : OracleComp (unifSpec + oracleSpec Input Salt rounds) A)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (result : ((A × QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
      QueryLog (oracleSpec Input Salt rounds)) ×
        (oracleSpec Input Salt rounds).QueryCache)
    (supported : result ∈ support (randomOracleLoggedRun adversary.withQueryLog cache)) :
    result.1.1.2.snd = result.1.2 := by
  induction adversary using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp [OracleComp.withQueryLog, randomOracleLoggedRun] at supported
      subst result
      rfl
  | query_bind query next ih =>
      rw [withQueryLog_query_bind, randomOracleLoggedRun_bind] at supported
      obtain ⟨phase, hphase, hrest⟩ :=
        (mem_support_bind_iff _ _ _).mp supported
      rw [support_map] at hrest
      obtain ⟨mapped, hmapped, rfl⟩ := hrest
      rw [randomOracleLoggedRun_map, support_map] at hmapped
      obtain ⟨tail, htail, rfl⟩ := hmapped
      have hsource := ih phase.1.1 phase.2 tail htail
      have hone : phase.1.2 = QueryLog.snd ([(⟨query, phase.1.1⟩ :
          (q : (unifSpec + oracleSpec Input Salt rounds).Domain) ×
            (unifSpec + oracleSpec Input Salt rounds).Range q)] :
          QueryLog (unifSpec + oracleSpec Input Salt rounds)) := by
        cases query with
        | inl coin =>
            rw [randomOracleLoggedRun_uniformQuery] at hphase
            rw [support_map] at hphase
            obtain ⟨u, _, rfl⟩ := hphase
            rfl
        | inr key =>
            rw [randomOracleLoggedRun_hashQuery] at hphase
            rw [support_map] at hphase
            obtain ⟨p, _, rfl⟩ := hphase
            rfl
      simp only [QueryLog.snd, List.filterMap_cons] at hsource hone ⊢
      rw [hsource, hone]
      cases query <;> simp

/-- A fixed-table hash query returns that table's answer from an agreeing cache, records one
ordered query entry even on a hit, and leaves a cache that still agrees with the table. -/
private theorem fixedTable_hash_query_support
    [DecidableEq Input] [DecidableEq Salt]
    (key : Key Input Salt rounds) (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : ((key.Challenge × QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (liftM ((unifSpec + oracleSpec Input Salt rounds).query (.inr key))) table cache)) :
    result.1.1 = table key ∧ result.1.2 = [⟨key, table key⟩] ∧
      result.2.AgreesWithFn (QueryImpl.ofFn table) := by
  rw [fixedTableLoggedRun_hashQuery] at supported
  rw [support_map] at supported
  obtain ⟨p, hp, rfl⟩ := supported
  cases hc : cache key with
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst p
      have hvalue : table key = value := agree hc
      simp [hvalue, agree]
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc] at hp
      change p ∈ support (pure (table key, cache.cacheQuery key (table key))) at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst p
      refine ⟨rfl, rfl, ?_⟩
      exact (QueryCache.agreesWithFn_cacheQuery_iff cache key (table key)
        (QueryImpl.ofFn table) hc).mpr ⟨agree, rfl⟩

/-- Every interleaved fixed-table query preserves agreement of the cache with the table.
Private samples leave the cache alone. -/
private theorem fixedTable_single_query_cache_agrees
    [DecidableEq Input] [DecidableEq Salt]
    (query : (unifSpec + oracleSpec Input Salt rounds).Domain)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : (((unifSpec + oracleSpec Input Salt rounds).Range query ×
      QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (liftM ((unifSpec + oracleSpec Input Salt rounds).query query)) table cache)) :
    result.2.AgreesWithFn (QueryImpl.ofFn table) := by
  cases query with
  | inl coin =>
      rw [fixedTableLoggedRun_uniformQuery, support_map] at supported
      obtain ⟨u, _, rfl⟩ := supported
      exact agree
  | inr key =>
      exact (fixedTable_hash_query_support key table cache agree result supported).2.2

/-- The fixed-table interpreter keeps every reached cache consistent with the chosen complete
table, even when private samples and hash queries are interleaved adaptively. -/
theorem fixedTable_cache_agrees {A : Type}
    [DecidableEq Input] [DecidableEq Salt]
    (program : OracleComp (unifSpec + oracleSpec Input Salt rounds) A)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : ((A × QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun program table cache)) :
    result.2.AgreesWithFn (QueryImpl.ofFn table) := by
  induction program using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      have hresult : result = ((value, []), cache) := by
        simpa [fixedTableLoggedRun] using supported
      subst result
      exact agree
  | query_bind query next ih =>
      rw [fixedTableLoggedRun_bind] at supported
      obtain ⟨first, hfirst, hrest⟩ := (mem_support_bind_iff _ _ _).mp supported
      rw [support_map] at hrest
      obtain ⟨tail, htail, rfl⟩ := hrest
      exact ih first.1.1 first.2
        (fixedTable_single_query_cache_agrees query table cache agree first hfirst)
        tail htail

/-- Fixed-table execution of any right-summand restoration program agrees with deterministic
table evaluation and its complete ordered query log. The cache may be nonempty provided it
agrees with the table; this is exactly the invariant at the adversary/completion handoff. -/
theorem fixedTable_restorationQueries_run {A : Type}
    [DecidableEq Input] [DecidableEq Salt]
    (program : OracleComp (oracleSpec Input Salt rounds) A)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : ((A × QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (simulateQ (restorationQueries Input Salt rounds) program) table cache)) :
    result.1.1 = evalWithAnswerFn (QueryImpl.ofFn table) program ∧
      result.1.2 = tableQueryLog program table ∧
      result.2.AgreesWithFn (QueryImpl.ofFn table) := by
  induction program using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      have hresult : result = ((value, []), cache) := by
        simpa [fixedTableLoggedRun] using supported
      subst result
      exact ⟨rfl, rfl, agree⟩
  | query_bind key next ih =>
      simp only [simulateQ_bind, simulateQ_liftM_query] at supported
      rw [fixedTableLoggedRun_bind] at supported
      obtain ⟨first, hfirst, hrest⟩ := (mem_support_bind_iff _ _ _).mp supported
      rw [support_map] at hrest
      obtain ⟨tail, htail, rfl⟩ := hrest
      have hfirst' := fixedTable_hash_query_support key table cache agree first hfirst
      rcases hfirst' with ⟨hvalue, hlog, hagree⟩
      rw [hvalue] at htail
      have htail' := ih (table key) first.2 hagree tail htail
      rcases htail' with ⟨hout, htlog, htagree⟩
      refine ⟨?_, ?_, htagree⟩
      · simpa only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
          QueryImpl.ofFn_apply] using hout
      · simp only [tableQueryLog_query_bind, hlog, htlog,
          List.singleton_append]

/-- Completion after an agreeing adversary cache yields the selected native path and exactly
the protocol's challenge-key sequence, including queries that hit the adversary cache. -/
theorem fixedTable_completion_path_keys [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (z : Input) (messages : Messages Salt rounds)
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : (((protocol rounds).tree.ExecutionPath ×
      QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (simulateQ (restorationQueries Input Salt rounds) (complete rounds z messages))
      table cache)) :
    result.1.1 = completedPath rounds z messages table ∧
      result.1.2.map Sigma.fst = completionKeys rounds z messages := by
  obtain ⟨hpath, hlog, _⟩ := fixedTable_restorationQueries_run
    (complete rounds z messages) table cache agree result supported
  refine ⟨?_, ?_⟩
  · simpa only [complete_eval] using hpath
  · rw [hlog]
    exact complete_log_keys rounds z messages table

/-- A selected adversary output is completed in the same fixed-table run; the retained phase log
is returned verbatim, while the suffix hash log contains exactly the completion keys. -/
theorem fixedTable_completionAfterAdversaryLog_selected
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (z : Input) (messages : Messages Salt rounds) (witness : W)
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (table : Table Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (agree : cache.AgreesWithFn (QueryImpl.ofFn table))
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedCompletionAfterAdversaryLog rounds
        (some (z, messages, witness), adversaryLog)) table cache)) :
    result.1.1 = (some (z, completedPath rounds z messages table, witness), adversaryLog) ∧
      result.1.2.map Sigma.fst = completionKeys rounds z messages := by
  have hprogram : randomizedCompletionAfterAdversaryLog rounds
      (some (z, messages, witness), adversaryLog) =
      (fun path => (some (z, path, witness), adversaryLog)) <$>
        simulateQ (restorationQueries Input Salt rounds) (complete rounds z messages) := by
    simp only [randomizedCompletionAfterAdversaryLog, map_eq_pure_bind]
  rw [hprogram, fixedTableLoggedRun_map, support_map] at supported
  obtain ⟨completion, hcompletion, rfl⟩ := supported
  obtain ⟨hpath, hkeys⟩ := fixedTable_completion_path_keys
    rounds z messages table cache agree completion hcompletion
  exact ⟨by simp [hpath], hkeys⟩

/-- Completion returns the adversary's source log unchanged in the actual cached run. This
holds for both selected and failed adversary outputs. -/
theorem randomOracle_completion_sourceLog [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (selectedAndLog : Option (Input × Messages Salt rounds × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedCompletionAfterAdversaryLog rounds selectedAndLog) cache)) :
    result.1.1.2 = selectedAndLog.2 := by
  rcases selectedAndLog with ⟨selected, adversaryLog⟩
  cases selected with
  | none =>
      simp [randomizedCompletionAfterAdversaryLog, randomOracleLoggedRun] at supported
      subst result
      rfl
  | some data =>
      rcases data with ⟨z, messages, witness⟩
      have hprogram : randomizedCompletionAfterAdversaryLog rounds
          (some (z, messages, witness), adversaryLog) =
          (fun path => (some (z, path, witness), adversaryLog)) <$>
            simulateQ (restorationQueries Input Salt rounds) (complete rounds z messages) := by
        simp only [randomizedCompletionAfterAdversaryLog, map_eq_pure_bind]
      rw [hprogram, randomOracleLoggedRun_map, support_map] at supported
      obtain ⟨completion, _, rfl⟩ := supported
      rfl

/-- Every interleaved fixed-table run retains the adversary's hash log; selected runs append
exactly the selected path's completion log, while failed selections append nothing. -/
theorem fixedTable_restored_trace [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (table : Table Input Salt rounds)
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅)) :
    (result.1.1.1 = none ∧ result.1.2 = result.1.1.2.snd) ∨
      ∃ z messages witness suffixLog,
        result.1.1.1 = some (z, completedPath rounds z messages table, witness) ∧
        result.1.2 = result.1.1.2.snd ++ suffixLog ∧
        suffixLog.map Sigma.fst = completionKeys rounds z messages := by
  rw [randomizedRestoredExecutionWithAdversaryLog_fixedTable_handoff] at supported
  obtain ⟨phase, hphase, hrest⟩ := (mem_support_bind_iff _ _ _).mp supported
  rw [support_map] at hrest
  obtain ⟨suffix, hsuffix, rfl⟩ := hrest
  have hsource := fixedTable_withQueryLog_hashLog_eq adversary table ∅ phase hphase
  have hagree : phase.2.AgreesWithFn (QueryImpl.ofFn table) :=
    fixedTable_cache_agrees adversary.withQueryLog table ∅ (by simp [QueryCache.AgreesWithFn])
      phase hphase
  rcases phase with ⟨⟨⟨selected, sourceLog⟩, hashLog⟩, phaseCache⟩
  cases selected with
  | none =>
      have hsuffix' : suffix = (((none, sourceLog), []), phaseCache) := by
        simpa [randomizedCompletionAfterAdversaryLog, fixedTableLoggedRun] using hsuffix
      subst suffix
      left
      simp [hsource]
  | some selected =>
      rcases selected with ⟨z, messages, witness⟩
      obtain ⟨hout, hkeys⟩ := fixedTable_completionAfterAdversaryLog_selected
        rounds z messages witness sourceLog table phaseCache hagree suffix hsuffix
      right
      refine ⟨z, messages, witness, suffix.1.2, ?_, ?_, hkeys⟩
      · exact congrArg Prod.fst hout
      · simp only [hsource, hout]

/-- A bad extraction must lie on the selected side of the joint trace decomposition. -/
theorem fixedTable_badExtract_trace [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (table : Table Input Salt rounds)
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅))
    (bad : badExtractOnPath state extractor Z terminalWitness result.1.1.1) :
    ∃ z messages witness suffixLog,
      result.1.1.1 = some (z, completedPath rounds z messages table, witness) ∧
      result.1.2 = result.1.1.2.snd ++ suffixLog ∧
      suffixLog.map Sigma.fst = completionKeys rounds z messages := by
  rcases fixedTable_restored_trace rounds adversary table result supported with
    ⟨hnone, _⟩ | hselected
  · rw [hnone] at bad
    exact False.elim bad
  · exact hselected

/-- Every bad extraction event in the actual interleaved game is witnessed by a queried
restoration key in the same fixed table and the same joint execution trace. -/
theorem fixedTable_badExtract_has_bad_query [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (table : Table Input Salt rounds)
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅))
    (bad : badExtractOnPath state extractor Z terminalWitness result.1.1.1) :
    ∃ query ∈ result.1.2, badKey state extractor Z query.1 table := by
  obtain ⟨z, messages, witness, suffixLog, hresult, hlog, hkeys⟩ :=
    fixedTable_badExtract_trace rounds adversary state extractor Z terminalWitness
      table result supported bad
  have hbad : badExtractOnPath state extractor Z terminalWitness
      (some (z, completedPath rounds z messages table, witness)) := by
    simpa only [hresult] using bad
  obtain ⟨key, hkey, hbadkey⟩ := badExtractOnPath_completion
    state extractor Z preserving terminalWitness z messages witness table hbad
  have hmem : key ∈ suffixLog.map Sigma.fst := by simpa only [hkeys] using hkey
  obtain ⟨query, hquery, hquerykey⟩ := List.mem_map.mp hmem
  refine ⟨query, ?_, ?_⟩
  · rw [hlog]
    exact List.mem_append.mpr (Or.inr hquery)
  · simpa only [hquerykey] using hbadkey

/-- A failed adversary selection still pays for every distinct restoration key it queried. -/
theorem roundFreshCharge_adversary_le [DecidableEq Input] [DecidableEq Salt]
    (errors : RoundErrors rounds)
    (adversaryLog : QueryLog (unifSpec + oracleSpec Input Salt rounds)) :
    roundFreshCharge errors adversaryLog.snd ≤
      (adversaryHashKeys adversaryLog).card * Finset.univ.sup errors := by
  unfold roundFreshCharge adversaryHashKeys
  calc
    (∑ key ∈ (adversaryLog.snd.map Sigma.fst).toFinset, keyError errors key) ≤
        ∑ _key ∈ (adversaryLog.snd.map Sigma.fst).toFinset,
          Finset.univ.sup errors :=
      Finset.sum_le_sum (fun key _ => keyError_le_max errors key)
    _ = (adversaryLog.snd.map Sigma.fst).toFinset.card *
        Finset.univ.sup errors := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The actual distinct-key charge of every joint fixed-table trace is bounded by the
adversary's observed distinct-key count and one local error per completion round. -/
theorem fixedTable_joint_freshCharge_le [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (table : Table Input Salt rounds)
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (fixedTableLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) table ∅)) :
    freshQueryCharge (keyError errors) result.1.2 ≤
      (adversaryHashKeys result.1.1.2).card * Finset.univ.sup errors +
        ∑ j, errors j := by
  change roundFreshCharge errors result.1.2 ≤ _
  rcases fixedTable_restored_trace rounds adversary table result supported with
    ⟨_, hlog⟩ | ⟨z, messages, witness, suffixLog, _, hlog, hkeys⟩
  · rw [hlog]
    exact (roundFreshCharge_adversary_le errors result.1.1.2).trans
      (le_add_right le_rfl)
  · rw [hlog]
    exact roundFreshCharge_append_le errors result.1.1.2 suffixLog z messages hkeys

/-- The pointwise bound holds on the actual cached random-oracle support, over arbitrary input
and salt types. The support bridge keeps the entire output, log and cache tuple unchanged. -/
theorem randomOracle_joint_freshCharge_le [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅)) :
    freshQueryCharge (keyError errors) result.1.2 ≤
      (adversaryHashKeys result.1.1.2).card * Finset.univ.sup errors +
        ∑ j, errors j := by
  obtain ⟨table, htable⟩ := mem_support_fixedTableLoggedRun_of_randomOracle
    (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅ result supported
  exact fixedTable_joint_freshCharge_le rounds errors adversary table result htable

/-- A cap on distinct keys in the actual cached adversary phase reaches the returned
adversary log of every joint run, including failed selections. -/
theorem randomOracle_joint_adversaryKeys_le [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅)) :
    (adversaryHashKeys result.1.1.2).card ≤ Q := by
  change result ∈ support (randomOracleLoggedRun
    (adversary.withQueryLog >>= randomizedCompletionAfterAdversaryLog rounds) ∅) at supported
  rw [randomOracleLoggedRun_bind] at supported
  obtain ⟨phase, hphase, hrest⟩ := (mem_support_bind_iff _ _ _).mp supported
  rw [support_map] at hrest
  obtain ⟨suffix, hsuffix, rfl⟩ := hrest
  have hlog := randomOracle_completion_sourceLog rounds phase.1.1 phase.2 suffix hsuffix
  have hsource := randomOracle_withQueryLog_hashLog_eq adversary ∅ phase hphase
  change (adversaryHashKeys suffix.1.1.2).card ≤ Q
  rw [hlog]
  change ((phase.1.1.2.snd.map Sigma.fst).toFinset).card ≤ Q
  rw [hsource]
  exact actualQueryBound phase hphase

/-- The familiar `Q * max + sum` budget follows from the actual distinct-query cap, not from
a syntactic count of all abstract paths. -/
theorem randomOracle_joint_freshCharge_le_queryBound [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (result : (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache))
    (supported : result ∈ support (randomOracleLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅)) :
    freshQueryCharge (keyError errors) result.1.2 ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  calc
    freshQueryCharge (keyError errors) result.1.2 ≤
        (adversaryHashKeys result.1.1.2).card * Finset.univ.sup errors +
          ∑ j, errors j :=
      randomOracle_joint_freshCharge_le rounds errors adversary result supported
    _ ≤ Q * Finset.univ.sup errors + ∑ j, errors j := by
      gcongr
      exact randomOracle_joint_adversaryKeys_le rounds adversary Q actualQueryBound
        result supported

/-- Expected distinct adversary keys as carried in the actual joint run. The source phase log
is part of the returned value, so this includes keys queried on failed selections. -/
noncomputable def expectedJointAdversaryKeys [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) : ENNReal :=
  letI : MeasurableSpace
      (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  ∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
    ∂𝒟[randomOracleLoggedRun
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅]

/-- Expected number of distinct hash keys in the actual cached adversary phase. -/
noncomputable def expectedAdversaryFreshKeys [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) : ENNReal :=
  letI : MeasurableSpace
      (((Option (Input × Messages Salt rounds × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  ∫⁻ phase, ((freshKeysOfLog phase.1.2).card : ENNReal)
    ∂𝒟[randomOracleLoggedRun adversary.withQueryLog ∅]

private theorem completion_expected_adversaryKeys
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (selectedAndLog : Option (Input × Messages Salt rounds × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds))
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    letI : MeasurableSpace
      (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
    (∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
      ∂𝒟[randomOracleLoggedRun
        (randomizedCompletionAfterAdversaryLog rounds selectedAndLog) cache]) =
      (adversaryHashKeys selectedAndLog.2).card := by
  let : MeasurableSpace
      (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  have hae := evalDist.ae_of_forall_mem_support
    (randomOracleLoggedRun (randomizedCompletionAfterAdversaryLog rounds selectedAndLog)
      cache)
    (fun result => ((adversaryHashKeys result.1.1.2).card : ENNReal) =
      (adversaryHashKeys selectedAndLog.2).card)
    MeasurableSet.of_discrete
    (fun result hresult => by
      rw [randomOracle_completion_sourceLog rounds selectedAndLog cache result hresult])
  calc
    (∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
      ∂𝒟[randomOracleLoggedRun
        (randomizedCompletionAfterAdversaryLog rounds selectedAndLog) cache]) =
        ∫⁻ _, ((adversaryHashKeys selectedAndLog.2).card : ENNReal)
          ∂𝒟[randomOracleLoggedRun
            (randomizedCompletionAfterAdversaryLog rounds selectedAndLog) cache] :=
      lintegral_congr_ae hae
    _ = (adversaryHashKeys selectedAndLog.2).card := by
      rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-- Completion preserves the adversary's distinct-key count in expectation. Thus the count
carried by the joint run is exactly the count measured at the actual adversary-phase boundary. -/
theorem expectedJointAdversaryKeys_eq_expectedAdversaryFreshKeys
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    expectedJointAdversaryKeys rounds adversary =
      expectedAdversaryFreshKeys rounds adversary := by
  let Phase :=
    (((Option (Input × Messages Salt rounds × W) ×
      QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
        QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache)
  let : MeasurableSpace
      (((Option (Input × Messages Salt rounds × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  let : MeasurableSpace
      (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  let phaseRun := randomOracleLoggedRun adversary.withQueryLog ∅
  let jointRun := randomOracleLoggedRun
    (randomizedRestoredExecutionWithAdversaryLog rounds adversary) ∅
  change (∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
    ∂𝒟[jointRun]) =
    ∫⁻ phase, ((freshKeysOfLog phase.1.2).card : ENNReal) ∂𝒟[phaseRun]
  have hbind : jointRun = phaseRun >>= fun phase =>
      (fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
        randomOracleLoggedRun
          (randomizedCompletionAfterAdversaryLog rounds phase.1.1) phase.2 := by
    simpa only [jointRun, phaseRun] using
      randomizedRestoredExecutionWithAdversaryLog_handoff rounds adversary ∅
  rw [hbind, lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
  have hinner (phase : Phase) :
      (∫⁻ result, ((adversaryHashKeys result.1.1.2).card : ENNReal)
        ∂𝒟[(fun suffix => ((suffix.1.1, phase.1.2 ++ suffix.1.2), suffix.2)) <$>
          randomOracleLoggedRun
            (randomizedCompletionAfterAdversaryLog rounds phase.1.1) phase.2]) =
      (adversaryHashKeys phase.1.1.2).card := by
    rw [lintegral_evalDist_map_of_discrete]
    exact completion_expected_adversaryKeys rounds phase.1.1 phase.2
  simp_rw [hinner]
  apply lintegral_congr_ae
  have hae := evalDist.ae_of_forall_mem_support phaseRun
    (fun phase => phase.1.1.2.snd = phase.1.2)
    MeasurableSet.of_discrete
    (fun phase hphase => randomOracle_withQueryLog_hashLog_eq adversary ∅ phase hphase)
  filter_upwards [hae] with phase hphase
  simp only [adversaryHashKeys, freshKeysOfLog, hphase]

/-- The expected charge of the *actual* joint cached run obeys the roundwise budget.
No global query cap is assumed, and `ENNReal` handles zero and infinite errors directly. -/
theorem expectedJointFreshCharge_le [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    expectedFreshQueryCharge
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary)
      (keyError errors) ≤
      Finset.univ.sup errors * expectedJointAdversaryKeys rounds adversary +
        ∑ j, errors j := by
  let program := randomizedRestoredExecutionWithAdversaryLog rounds adversary
  let : MeasurableSpace
      (((Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  have hae := evalDist.ae_of_forall_mem_support
    (randomOracleLoggedRun program ∅)
    (fun result => freshQueryCharge (keyError errors) result.1.2 ≤
      Finset.univ.sup errors * (adversaryHashKeys result.1.1.2).card +
        ∑ j, errors j)
    MeasurableSet.of_discrete
    (fun result hresult => by
      have h := randomOracle_joint_freshCharge_le rounds errors adversary result hresult
      simpa only [mul_comm] using h)
  change (∫⁻ result, freshQueryCharge (keyError errors) result.1.2
    ∂𝒟[randomOracleLoggedRun program ∅]) ≤ _
  calc
    (∫⁻ result, freshQueryCharge (keyError errors) result.1.2
      ∂𝒟[randomOracleLoggedRun program ∅]) ≤
        ∫⁻ result, Finset.univ.sup errors *
          (adversaryHashKeys result.1.1.2).card + ∑ j, errors j
          ∂𝒟[randomOracleLoggedRun program ∅] := lintegral_mono_ae hae
    _ = Finset.univ.sup errors * expectedJointAdversaryKeys rounds adversary +
          ∑ j, errors j := by
      rw [lintegral_add_left Measurable.of_discrete,
        lintegral_const_mul _ Measurable.of_discrete, lintegral_const,
        evalDist_apply_univ_eq_one, mul_one]
      rfl

/-- The second required inequality, with the adversary count measured at the actual cached
phase boundary rather than reconstructed from a separate execution. -/
theorem expectedJointFreshCharge_le_actualAdversary
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (errors : RoundErrors rounds)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    expectedFreshQueryCharge
      (randomizedRestoredExecutionWithAdversaryLog rounds adversary)
      (keyError errors) ≤
      Finset.univ.sup errors * expectedAdversaryFreshKeys rounds adversary +
        ∑ j, errors j := by
  simpa only [expectedJointAdversaryKeys_eq_expectedAdversaryFreshKeys rounds adversary]
    using expectedJointFreshCharge_le rounds errors adversary

/-- A support-level cap on distinct hash keys in the actual cached adversary run bounds its
expectation. The cap is measured on the adversary phase itself, including failure branches. -/
theorem expectedAdversaryFreshKeys_le_queryBound
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    expectedAdversaryFreshKeys rounds adversary ≤ Q := by
  let : MeasurableSpace
      (((Option (Input × Messages Salt rounds × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) ×
          QueryLog (oracleSpec Input Salt rounds)) ×
            (oracleSpec Input Salt rounds).QueryCache) := ⊤
  have hae := evalDist.ae_of_forall_mem_support
    (randomOracleLoggedRun adversary.withQueryLog ∅)
    (fun phase => ((freshKeysOfLog phase.1.2).card : ENNReal) ≤ Q)
    MeasurableSet.of_discrete
    (fun phase hphase => Nat.cast_le.mpr (actualQueryBound phase hphase))
  change (∫⁻ phase, ((freshKeysOfLog phase.1.2).card : ENNReal)
    ∂𝒟[randomOracleLoggedRun adversary.withQueryLog ∅]) ≤ Q
  calc
    _ ≤ ∫⁻ _, (Q : ENNReal)
          ∂𝒟[randomOracleLoggedRun adversary.withQueryLog ∅] :=
      lintegral_mono_ae hae
    _ = Q := by rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-- On the actual total cached adversary run, the support cap used in the `Q` corollaries is
equivalent to an almost-sure cap. Every supported finite transcript has positive mass. -/
theorem actualAdversaryQueryBound_iff_probOne
    [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Q : ℕ) :
    (∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) ↔
      Pr{let phase ← (randomOracleLoggedRun adversary.withQueryLog ∅)}[
        (freshKeysOfLog phase.1.2).card ≤ Q] = 1 := by
  exact (OracleComp.prEvent_eq_one_iff
    (randomOracleLoggedRun adversary.withQueryLog ∅)
    (fun phase => (freshKeysOfLog phase.1.2).card ≤ Q)).symm

/-- Execute the existing native verifier on the same completed challenge path. -/
def randomizedVerificationGame (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
        Out z path.toBranchPath × W)) := do
  match (← adversary) with
  | none => pure none
  | some (z, messages, witness) =>
      let path ← simulateQ (restorationQueries Input Salt rounds) (complete rounds z messages)
      let result ← executeStrategies (unifSpec + oracleSpec Input Salt rounds)
        (protocol rounds).tree (protocol rounds).roles (protocol rounds).oracles initial (impl z)
        (scriptedProver (unifSpec + oracleSpec Input Salt rounds) rounds messages)
        (challengeVerifier (unifSpec + oracleSpec Input Salt rounds) rounds initial
          (pathPrograms (unifSpec + oracleSpec Input Salt rounds) rounds path) (Out z)
          (terminal z))
      pure (some ⟨z, result.1, result.2.2, witness⟩)

/-- Native replay preserves the selected path exactly. In particular, replay adds no ambient
queries after completion, and the terminal value comes from the actual source-only interpreter. -/
theorem randomizedVerificationGame_eq (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    randomizedVerificationGame initial impl Out terminal adversary =
      (fun result => result.map fun outcome =>
        (⟨outcome.1, outcome.2.1,
          terminalObservation initial impl Out terminal outcome.1 outcome.2.1,
          outcome.2.2⟩ :
          (z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
            Out z path.toBranchPath × W)) <$>
        randomizedRestoredExecution rounds adversary := by
  simp only [randomizedVerificationGame, randomizedRestoredExecution,
    map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro selected
  cases selected with
  | none => rfl
  | some data =>
      rcases data with ⟨z, messages, witness⟩
      simp only [bind_assoc, pure_bind, Option.map_some]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro path supported
      rw [execute_pathReplay _ _ _ _ messages path
        (complete_support_matches rounds z messages path
          (simulateQ_support_subset _ _ supported))]
      rfl

/-- Close the actual native verifier output under the completed path's own source handler. -/
def randomizedClosedVerificationGame (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
        Option (ClosedClaim (Stmt z path.toBranchPath) (family z path.toBranchPath)) × W)) :=
  (fun result => result.map fun outcome =>
    ⟨outcome.1, outcome.2.1,
      outcome.2.2.1.map (fun claim => claim.closeWith
        (outcome.2.1.closingImpl (protocol rounds).oracles initial (impl outcome.1))),
      outcome.2.2.2⟩) <$>
    randomizedVerificationGame initial impl (OracleOutput initial Stmt family) terminal adversary

/-- The closed game observes the same native terminal output and the same completion path. -/
theorem randomizedClosedVerificationGame_eq (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Stmt : Input → (protocol rounds).tree.BranchPath → Type)
    {Idx : Input → (protocol rounds).tree.BranchPath → Type}
    {Realization : (z : Input) → (p : (protocol rounds).tree.BranchPath) → Idx z p → Type}
    (family : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleFamily (Idx z p) (Realization z p))
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (OracleOutput initial Stmt family z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    randomizedClosedVerificationGame initial impl Stmt family terminal adversary =
      (fun result => result.map fun outcome =>
        (⟨outcome.1, outcome.2.1,
          closedTerminalObservation initial impl Stmt family terminal outcome.1 outcome.2.1,
          outcome.2.2⟩ :
          (z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
            Option (ClosedClaim (Stmt z path.toBranchPath)
              (family z path.toBranchPath)) × W)) <$>
        randomizedRestoredExecution rounds adversary := by
  rw [randomizedClosedVerificationGame, randomizedVerificationGame_eq, Functor.map_map]
  congr 1
  funext result
  cases result with
  | none => rfl
  | some outcome => rfl

end Interaction.Oracle.Security.StateRestoration
