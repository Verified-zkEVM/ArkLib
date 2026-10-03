/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationBudget
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

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

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
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
private theorem sum_toFinset_le_list_sum {A : Type} [DecidableEq A]
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

/-- Log the adversary before completion to keep the phase boundary as ordinary returned data.
This observes source calls without introducing new uniform or restoration queries. -/
def randomizedRestoredExecutionWithAdversaryLog (rounds : List Round)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option (Input × (protocol rounds).tree.ExecutionPath × W) ×
        QueryLog (unifSpec + oracleSpec Input Salt rounds)) := do
  let (selected, adversaryLog) ← adversary.withQueryLog
  match selected with
  | none => pure (none, adversaryLog)
  | some (z, messages, witness) =>
      let path ← simulateQ (restorationQueries Input Salt rounds) (complete rounds z messages)
      pure (some (z, path, witness), adversaryLog)

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
  simp only [randomizedRestoredExecutionWithAdversaryLog, randomizedRestoredExecution,
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

/-- Observe the selected native path while retaining the adversary's exact source query log.
Both scalar observations and closed oracle outputs use this one owner-level wrapper. -/
def randomizedObservedGameWithAdversaryLog
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds)
      (Option ((z : Input) × (path : (protocol rounds).tree.ExecutionPath) ×
        Out z path × W) × QueryLog (unifSpec + oracleSpec Input Salt rounds)) :=
  (fun result =>
    (result.1.map fun outcome =>
      (⟨outcome.1, outcome.2.1, observe outcome.1 outcome.2.1, outcome.2.2⟩ :
        (z : Input) × (path : (protocol rounds).tree.ExecutionPath) × Out z path × W),
      result.2)) <$> randomizedRestoredExecutionWithAdversaryLog rounds adversary

/-- Erasing the adversary-phase log gives the ordinary observed joint game as an exact
`OracleComp` equation; every stateful logged interpreter therefore preserves its cache and log. -/
theorem randomizedObservedGameWithAdversaryLog_erase
    (Out : (z : Input) → (protocol rounds).tree.ExecutionPath → Type)
    (observe : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) → Out z path)
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    Prod.fst <$> randomizedObservedGameWithAdversaryLog Out observe adversary =
      (fun result => result.map fun outcome =>
        (⟨outcome.1, outcome.2.1, observe outcome.1 outcome.2.1, outcome.2.2⟩ :
          (z : Input) × (path : (protocol rounds).tree.ExecutionPath) × Out z path × W)) <$>
        randomizedRestoredExecution rounds adversary := by
  rw [randomizedObservedGameWithAdversaryLog, Functor.map_map]
  conv_rhs => rw [← randomizedRestoredExecutionWithAdversaryLog_erase rounds adversary]
  rw [Functor.map_map]

/-- The scalar observed game erases to the existing native verifier exactly. -/
theorem randomizedObservedGame_scalar_erase (initial : PFunctor)
    (impl : Input → QueryImpl (ofPFunctor initial) Id)
    (Out : Input → (protocol rounds).tree.BranchPath → Type)
    (terminal : (z : Input) → (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out z p))
    (adversary : RandomizedRestorationAdversary Input Salt W rounds) :
    Prod.fst <$> randomizedObservedGameWithAdversaryLog
      (fun z path => Out z path.toBranchPath)
      (terminalObservation initial impl Out terminal) adversary =
        randomizedVerificationGame initial impl Out terminal adversary := by
  rw [randomizedObservedGameWithAdversaryLog_erase, randomizedVerificationGame_eq]

/-- The closed observed game erases to the existing native verifier and actual closing handler. -/
theorem randomizedObservedGame_closed_erase (initial : PFunctor)
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
    Prod.fst <$> randomizedObservedGameWithAdversaryLog
      (fun z path => Option (ClosedClaim (Stmt z path.toBranchPath)
        (family z path.toBranchPath)))
      (closedTerminalObservation initial impl Stmt family terminal) adversary =
        randomizedClosedVerificationGame initial impl Stmt family terminal adversary := by
  rw [randomizedObservedGameWithAdversaryLog_erase, randomizedClosedVerificationGame_eq]

end Interaction.Oracle.Security.StateRestoration
