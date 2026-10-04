/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyCertificateSecurity
public import ArkLib.Interaction.Oracle.FiatShamir.SingleSaltSecurity

/-!
# Accepted canonical transcripts and stopped native verification

The canonical state-restoration game reconstructs a complete transcript before its pure verifier
observes it. This file makes the observer reject precisely the paths on which the native verifier
would stop at a prefix guard, then compares the accepted failure event at the same random table.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec ProtocolSpec

namespace Interaction.Oracle.FiatShamir

open Security Security.StateRestoration

/-- Evaluate every prefix guard from an already completed native path. No answer table is an
argument: the challenge in the path selects the next guard continuation. -/
def guardsPassPath {Input : Type} : (rounds : List Round) →
    GuardSchedule Input PUnit rounds → Input →
      (protocol rounds).tree.ExecutionPath → Bool
  | [], _, _, _ => true
  | _ :: rounds, guards, z, path =>
      guards.1 z path.1 PUnit.unit &&
        guardsPassPath rounds (guards.2 path.1 PUnit.unit path.2.1) z path.2.2

/-- Guard acceptance reconstructed from the full path agrees with the fixed-table predicate
that controls actual stopped execution. -/
theorem guardsPassPath_completedPath {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : Messages PUnit rounds) (table : Table Input PUnit rounds) :
    guardsPassPath rounds guards z (completedPath rounds z messages table) =
      guardsPass rounds guards z messages table := by
  revert guards messages table
  induction rounds with
  | nil =>
      intro guards messages table
      cases messages
      rfl
  | cons round rounds ih =>
      intro guards messages table
      rcases messages with ⟨message, salt, messages⟩
      cases salt
      simpa only [guardsPassPath, guardsPass, completedPath, Prod.fst, Prod.snd]
        using congrArg (fun b => guards.1 z message PUnit.unit && b)
          (ih (guards.2 message PUnit.unit (table (Key.here z message PUnit.unit)))
            messages (fun q => table (Key.later message PUnit.unit q)))

/-- Stopped completion at a fixed table is a filtered full completion. The filter uses only
the completed path, including its previously sampled challenge answers. -/
theorem stoppedPath_eq_completedPath_filter {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : Messages PUnit rounds) (table : Table Input PUnit rounds) :
    stoppedPath rounds guards z messages table =
      (some (completedPath rounds z messages table)).filter
        (fun path => guardsPassPath rounds guards z path) := by
  by_cases hp : guardsPass rounds guards z messages table = true
  · rw [stoppedPath_eq_some_completedPath rounds guards z messages table hp]
    have hpath := guardsPassPath_completedPath rounds guards z messages table
    simp [Option.filter, hpath, hp]
  · cases hs : stoppedPath rounds guards z messages table with
    | none =>
        have hpath := guardsPassPath_completedPath rounds guards z messages table
        have hf : guardsPass rounds guards z messages table = false :=
          Bool.eq_false_iff.mpr hp
        simp [Option.filter, hpath, hf]
    | some path =>
        exact False.elim (hp (stoppedPath_some_implies_pass rounds guards z messages table hs))

/-- The canonical pure observer accepts a full transcript exactly when its native prefix
guards and terminal predicate would accept. It needs only the reconstructed path. -/
def matchedLegacyObserve {Input Output : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds)
    (accepts : Input → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option Output)
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) : Option Output :=
  if guardsPassPath rounds guards z path && accepts z path then observe z path else none

/-- Filter an already completed selected native path according to the actual verifier's
acceptance decision. This is a value projection only, not a log or cache equation. -/
def acceptedCompletedSelection {Input W : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds)
    (accepts : Input → (protocol rounds).tree.ExecutionPath → Bool)
    (selected : Option (Input × (protocol rounds).tree.ExecutionPath × W)) :
    Option (Input × (protocol rounds).tree.ExecutionPath × W) :=
  selected.filter (fun triple =>
    guardsPassPath rounds guards triple.1 triple.2.1 && accepts triple.1 triple.2.1)

/-- The pure canonical observer's output relation is equivalent to the native guard and
terminal acceptance conditions followed by the original output relation. -/
theorem legacyOutputRelation_matched {Input Output W : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds)
    (accepts : Input → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option Output)
    (relOut : Set (Output × W)) (z : Input)
    (path : (protocol rounds).tree.ExecutionPath) (witness : W) :
    legacyOutputRelation (matchedLegacyObserve rounds guards accepts observe) relOut
      z path witness ↔
    guardsPassPath rounds guards z path = true ∧ accepts z path = true ∧
      legacyOutputRelation observe relOut z path witness := by
  unfold legacyOutputRelation matchedLegacyObserve
  by_cases hg : guardsPassPath rounds guards z path = true
  · by_cases ha : accepts z path = true
    · simp [hg, ha]
    · simp [hg, ha]
  · simp [hg]

universe w

/-- Pointwise accepted failure is unchanged when moving guard and terminal filtering from
the canonical pure observer to the actual native returned value. The named extractor and exact
terminal seed are identical on both sides. -/
theorem legacyFailure_matched_eq_accepted {Input Output W WitIn : Type}
    (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds)
    (accepts : Input → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option Output)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (relIn : Set (Input × WitIn)) (relOut : Set (Output × W))
    (z : Input) (path : (protocol rounds).tree.ExecutionPath) (witness : W) :
    relationKSFailEvent relIn relOut
      (nativeLegacyResult rounds state extractor seed witnessMap
        (matchedLegacyObserve rounds guards accepts observe)
        (z, toLegacyTranscript rounds (toPublicPath rounds path), witness)) ↔
    badStoppedRelation state extractor
      (legacyInputRelation state witnessMap relIn)
      (legacyOutputRelation observe relOut) seed Set.univ
      (acceptedCompletedSelection rounds guards accepts (some (z, path, witness))) := by
  have hpath : legacyToRestorationPath rounds
      (toLegacyTranscript rounds (toPublicPath rounds path)) = path := by
    simp [legacyToRestorationPath, toRestorationPath_toPublicPath]
  dsimp only [nativeLegacyResult]
  rw [hpath]
  rw [legacyFailure_eq_badStoppedRelation state extractor seed witnessMap
    (matchedLegacyObserve rounds guards accepts observe) relIn relOut z path witness]
  simp only [badStoppedRelation]
  rw [legacyOutputRelation_matched rounds guards accepts observe relOut z path witness]
  by_cases hg : guardsPassPath rounds guards z path = true
  · by_cases ha : accepts z path = true
    · simp [acceptedCompletedSelection, Option.filter, hg, ha]
    · simp [acceptedCompletedSelection, Option.filter, hg, ha]
  · simp [acceptedCompletedSelection, Option.filter, hg]

/-- Relation failure on a complete selected path with the matched observer is the same event
as relation failure on its accepted-only value projection. -/
theorem badStoppedRelation_matched {Input Output W WitIn : Type}
    (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds)
    (accepts : Input → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option Output)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (relIn : Set (Input × WitIn)) (relOut : Set (Output × W))
    (selected : Option (Input × (protocol rounds).tree.ExecutionPath × W)) :
    badStoppedRelation state extractor
      (legacyInputRelation state witnessMap relIn)
      (legacyOutputRelation (matchedLegacyObserve rounds guards accepts observe) relOut)
      seed Set.univ selected ↔
    badStoppedRelation state extractor
      (legacyInputRelation state witnessMap relIn)
      (legacyOutputRelation observe relOut) seed Set.univ
      (acceptedCompletedSelection rounds guards accepts selected) := by
  cases selected with
  | none => rfl
  | some data =>
      rcases data with ⟨z, path, witness⟩
      simp only [badStoppedRelation]
      rw [legacyOutputRelation_matched rounds guards accepts observe relOut z path witness]
      by_cases hg : guardsPassPath rounds guards z path = true
      · by_cases ha : accepts z path = true
        · simp [acceptedCompletedSelection, Option.filter, hg, ha]
        · simp [acceptedCompletedSelection, Option.filter, hg, ha]
      · simp [acceptedCompletedSelection, Option.filter, hg]

/-- Repackage the output of the same routed legacy prover as a native proof with one global
salt. Its query program is unchanged, including every private uniform draw. -/
noncomputable def legacySingleSaltAdversary {Statement GlobalSalt W : Type} (rounds : List Round)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) (Statement × GlobalSalt) W (legacySpec rounds) unifSpec) :
    SingleSaltAdversary Statement GlobalSalt W rounds :=
  (fun result => some (result.1.1,
      (result.1.2, (fullLegacyMessagesEquiv rounds).symm result.2.1), result.2.2)) <$>
    simulateQ (legacyProverRoute rounds (legacyQueryInNative rounds)) prover

/-- The canonical prover translated to a single-salt proof induces exactly the native
restoration adversary already used by the table-coupling theorem. -/
theorem induced_legacySingleSaltAdversary {Statement GlobalSalt W : Type}
    (rounds : List Round)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) (Statement × GlobalSalt) W (legacySpec rounds) unifSpec) :
    inducedAdversary (legacySingleSaltAdversary rounds prover) =
      simulateLegacyProver rounds prover := by
  unfold inducedAdversary legacySingleSaltAdversary simulateLegacyProver
    simulateLegacyProverWith
  simp only [Functor.map_map]
  congr 1

/-- The value-only stopped verifier. The adversary and verifier still query the same native
oracle; only the phase log is omitted from this projection. -/
def stoppedAcceptedValueExecution {Input W : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds)
    (accepts : Input → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : RandomizedRestorationAdversary Input PUnit W rounds) :
    OracleComp (unifSpec + oracleSpec Input PUnit rounds)
      (Option (Input × (protocol rounds).tree.ExecutionPath × W)) := do
  let selected ← adversary
  match selected with
  | none => pure none
  | some (z, messages, witness) =>
      let path ← simulateQ (restorationQueries Input PUnit rounds)
        (stoppedComplete rounds guards z messages)
      pure ((path.filter (accepts z)).map (fun p => (z, p, witness)))

set_option backward.isDefEq.respectTransparency false in
/-- Erasing only the phase log of the actual accepted single-salt experiment leaves its
value-only stopped execution. This does not erase the verifier's effects from the run. -/
theorem singleSaltAcceptedExecution_erase {Statement GlobalSalt W : Type}
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt W rounds) :
    Prod.fst <$> singleSaltAcceptedExecution rounds guards accepts adversary =
      stoppedAcceptedValueExecution rounds guards accepts (inducedAdversary adversary) := by
  unfold singleSaltAcceptedExecution
  rw [singleSaltExecution_eq_stopped guards adversary]
  let finish : Option ((Statement × GlobalSalt) × Messages PUnit rounds × W) →
      OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)
        (Option ((Statement × GlobalSalt) × (protocol rounds).tree.ExecutionPath × W)) :=
    fun selected => match selected with
    | none => pure none
    | some (z, messages, witness) => do
        let path ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit rounds)
          (stoppedComplete rounds guards z messages)
        pure ((path.filter (accepts z)).map (fun p => (z, p, witness)))
  have hstep (selected : Option ((Statement × GlobalSalt) × Messages PUnit rounds × W))
      (log : QueryLog (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)) :
      (fun result => (acceptSingleSaltResult accepts result).1) <$>
        randomizedStoppedCompletionAfterAdversaryLog rounds guards (selected, log) =
      finish selected := by
    cases selected with
    | none => rfl
    | some data =>
        rcases data with ⟨z, messages, witness⟩
        simp only [randomizedStoppedCompletionAfterAdversaryLog, finish,
          map_bind, map_pure]
        congr 1
        funext path
        cases path with
        | none => rfl
        | some path =>
            cases h : accepts z path <;>
              simp [acceptSingleSaltResult, Option.filter, h]
  unfold randomizedStoppedRestoredExecutionWithAdversaryLog
  simp only [Functor.map_map, map_bind]
  simp_rw [hstep]
  unfold stoppedAcceptedValueExecution
  rw [← bind_map_left Prod.fst]
  have hlog : Prod.fst <$> (inducedAdversary adversary).withQueryLog =
      inducedAdversary adversary := by
    simpa only [withQueryLog, OracleSpec.loggingOracle] using
      loggingOracle.fst_map_run_simulateQ (inducedAdversary adversary)
  rw [hlog]
  simp only [finish]
  apply bind_congr
  intro selected
  cases selected with
  | none => rfl
  | some data =>
      rcases data with ⟨z, messages, witness⟩
      rfl

/-- At a paired fixed table, executing the stopped verifier returns its genuine stopped path.
The private-uniform interpreter is present but this verifier makes no such draw. -/
theorem nativeStopped_at_fixedTable {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : Messages PUnit rounds) :
    simulateQ (nativeFixedTableCoinImpl rounds table)
      (simulateQ (restorationQueries Input PUnit rounds)
        (stoppedComplete rounds guards z messages)) =
      pure (stoppedPath rounds guards z messages table) := by
  simp only [← QueryImpl.simulateQ_compose]
  change simulateQ ((QueryImpl.ofFn table).liftTarget ProbComp)
    (stoppedComplete rounds guards z messages) = _
  rw [simulateQ_liftTarget]
  exact congrArg pure (stoppedComplete_eval rounds guards z messages table)

/-- The actual stopped verifier at one fixed table returns exactly the completed full path
filtered by the path-reconstructed guard decisions and terminal check. -/
theorem stoppedAcceptedValue_at_fixedTable {Input W : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    (guards : GuardSchedule Input PUnit rounds)
    (accepts : Input → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : RandomizedRestorationAdversary Input PUnit W rounds) :
    simulateQ (nativeFixedTableCoinImpl rounds table)
      (stoppedAcceptedValueExecution rounds guards accepts adversary) =
    acceptedCompletedSelection rounds guards accepts <$>
      simulateQ (nativeFixedTableCoinImpl rounds table)
        (randomizedRestoredExecution rounds adversary) := by
  unfold stoppedAcceptedValueExecution randomizedRestoredExecution
  simp only [simulateQ_bind, map_bind]
  apply bind_congr
  intro selected
  cases selected with
  | none => rfl
  | some data =>
      rcases data with ⟨z, messages, witness⟩
      simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure]
      rw [nativeStopped_at_fixedTable, nativeComplete_at_fixedTable]
      simp only [pure_bind]
      rw [stoppedPath_eq_completedPath_filter]
      by_cases hg : guardsPassPath rounds guards z
          (completedPath rounds z messages table) = true
      · by_cases ha : accepts z (completedPath rounds z messages table) = true
        · simp [acceptedCompletedSelection, Option.filter, hg, ha]
        · simp [acceptedCompletedSelection, Option.filter, hg, ha]
      · simp [acceptedCompletedSelection, Option.filter, hg]

/-- At each fixed full table, the actual canonical transcript and pure matched verifier have
the same extraction-failure probability as the native stopped, terminal-filtered execution of
the translated arbitrary prover. Every private coin is preserved by the existing program route.
-/
theorem legacyFailure_fixedTable_eq_stopped {Input W WitIn Output : Type}
    (rounds : List Round) (table : Table Input PUnit rounds)
    (guards : GuardSchedule Input PUnit rounds)
    (accepts : Input → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option Output)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (relIn : Set (Input × WitIn)) (relOut : Set (Output × W))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    Pr{let selected ← legacyFixedTableTranscript rounds
        (nativeTableToLegacy rounds table) prover}[
      relationKSFailEvent relIn relOut
        (nativeLegacyResult rounds state extractor seed witnessMap
          (matchedLegacyObserve rounds guards accepts observe) selected)] =
    Pr{let selected ← simulateQ (nativeFixedTableCoinImpl rounds table)
        (stoppedAcceptedValueExecution rounds guards accepts
          (simulateLegacyProver rounds prover))}[
      badStoppedRelation state extractor
        (legacyInputRelation state witnessMap relIn)
        (legacyOutputRelation observe relOut) seed Set.univ selected] := by
  rw [legacyFailure_fixedTable_eq_native rounds table state extractor seed witnessMap
    (matchedLegacyObserve rounds guards accepts observe) relIn relOut prover]
  rw [stoppedAcceptedValue_at_fixedTable]
  rw [prEvent_map]
  exact prEvent_congr _ _ _
    (badStoppedRelation_matched rounds guards accepts observe state extractor seed witnessMap
      relIn relOut)

/-- Forgetting the log and cache after the actual native accepted run at one full table gives
the value-only stopped experiment. No equality of rejected transcripts, logs or costs is used. -/
theorem fixedTable_singleSaltAccepted_value {Statement GlobalSalt W : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (rounds : List Round) (table : Table (Statement × GlobalSalt) PUnit rounds)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt W rounds) :
    (fun joint => joint.1.1.1) <$>
      fixedTableLoggedRun
        (singleSaltAcceptedExecution rounds guards accepts adversary) table ∅ =
    simulateQ (nativeFixedTableCoinImpl rounds table)
      (stoppedAcceptedValueExecution rounds guards accepts
        (inducedAdversary adversary)) := by
  have hvalue := fixedTableLoggedRun_value table
    (singleSaltAcceptedExecution rounds guards accepts adversary) ∅
    (fixedTableCacheCompatible_empty table)
  calc
    _ = Prod.fst <$> simulateQ (nativeFixedTableCoinImpl rounds table)
          (singleSaltAcceptedExecution rounds guards accepts adversary) := by
            simpa only [Functor.map_map, nativeFixedTableCoinImpl] using
              congrArg (Prod.fst <$> ·) hvalue
    _ = simulateQ (nativeFixedTableCoinImpl rounds table)
          (Prod.fst <$> singleSaltAcceptedExecution rounds guards accepts adversary) := by
            rw [← simulateQ_map]
    _ = _ := by rw [singleSaltAcceptedExecution_erase]

/-- One uniformly sampled full table couples the canonical legacy game to the actual native
stopped and terminal-filtered run. The arbitrary legacy prover keeps its adaptive hash calls
and every independent private draw. -/
theorem legacyFailure_eager_eq_singleSaltAccepted
    {Statement GlobalSalt W WitIn Output : Type} (rounds : List Round)
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    [SampleableType (Table (Statement × GlobalSalt) PUnit rounds)]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : (Statement × GlobalSalt) →
      (protocol rounds).tree.ExecutionPath → Option Output)
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) →
      RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Statement × GlobalSalt) →
      (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Statement × GlobalSalt) → (state z).Witness → WitIn)
    (relIn : Set ((Statement × GlobalSalt) × WitIn))
    (relOut : Set (Output × W))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) (Statement × GlobalSalt) W
      (legacySpec rounds) unifSpec) :
    Pr{let selected ← (($ᵗ (Table (Statement × GlobalSalt) PUnit rounds)) >>=
        fun table => legacyFixedTableTranscript rounds
          (nativeTableToLegacy rounds table) prover)}[
      relationKSFailEvent relIn relOut
        (nativeLegacyResult rounds state extractor seed witnessMap
          (matchedLegacyObserve rounds guards accepts observe) selected)] =
    Pr{let joint ← (($ᵗ (Table (Statement × GlobalSalt) PUnit rounds)) >>= fun table =>
        fixedTableLoggedRun
          (singleSaltAcceptedExecution rounds guards accepts
            (legacySingleSaltAdversary rounds prover)) table ∅)}[
      badStoppedRelation state extractor
        (legacyInputRelation state witnessMap relIn)
        (legacyOutputRelation observe relOut) seed Set.univ joint.1.1.1] := by
  apply prEvent_bind_congr
  intro table
  rw [legacyFailure_fixedTable_eq_stopped rounds table guards accepts observe state
    extractor seed witnessMap relIn relOut prover]
  have hvalue := fixedTable_singleSaltAccepted_value rounds table guards accepts
    (legacySingleSaltAdversary rounds prover)
  rw [induced_legacySingleSaltAdversary] at hvalue
  rw [← hvalue, prEvent_map]

/-- The actual accepted single-salt run has the same event probabilities under its lazy shared
cache and an eagerly sampled uniform full table. The joint distribution retains logs and cache;
the accepted-event bridge below projects only its returned value. -/
theorem singleSaltAccepted_lazy_eq_eager
    {Statement GlobalSalt W : Type} (rounds : List Round)
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    [Finite Statement] [Finite GlobalSalt]
    [SampleableType (Table (Statement × GlobalSalt) PUnit rounds)]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt W rounds)
    (event : StoppedJointResult (Statement × GlobalSalt) PUnit W rounds → Prop) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution rounds guards accepts adversary) ∅)}[event joint] =
    Pr{let joint ← (($ᵗ (Table (Statement × GlobalSalt) PUnit rounds)) >>=
      fun table => fixedTableLoggedRun
        (singleSaltAcceptedExecution rounds guards accepts adversary) table ∅)}[
      event joint] := by
  let : MeasurableSpace (StoppedJointResult (Statement × GlobalSalt) PUnit W rounds) := ⊤
  apply prEvent_congr_of_evalDist_eq
  have h := evalDist_randomOracleLoggedRun_eq_fixedTable_finite
    (singleSaltAcceptedExecution rounds guards accepts adversary) ∅
  simpa only [completeTable_empty] using h

/-- The canonical full-transcript experiment with a path-matched pure observer has exactly the
accepted extraction-failure probability of the actual lazy, shared-cache native single-salt
execution. The same arbitrary prover and supplied terminal seed occur on both sides. -/
theorem legacyFailure_eq_actual_singleSaltAccepted
    {Statement GlobalSalt W WitIn Output : Type} (rounds : List Round)
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    [Finite Statement] [Finite GlobalSalt]
    [SampleableType (Table (Statement × GlobalSalt) PUnit rounds)]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : (Statement × GlobalSalt) →
      (protocol rounds).tree.ExecutionPath → Option Output)
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) →
      RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Statement × GlobalSalt) →
      (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Statement × GlobalSalt) → (state z).Witness → WitIn)
    (relIn : Set ((Statement × GlobalSalt) × WitIn))
    (relOut : Set (Output × W))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) (Statement × GlobalSalt) W
      (legacySpec rounds) unifSpec) :
    Pr{let selected ← (($ᵗ (Table (Statement × GlobalSalt) PUnit rounds)) >>=
        fun table => legacyFixedTableTranscript rounds
          (nativeTableToLegacy rounds table) prover)}[
      relationKSFailEvent relIn relOut
        (nativeLegacyResult rounds state extractor seed witnessMap
          (matchedLegacyObserve rounds guards accepts observe) selected)] =
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution rounds guards accepts
        (legacySingleSaltAdversary rounds prover)) ∅)}[
      badStoppedRelation state extractor
        (legacyInputRelation state witnessMap relIn)
        (legacyOutputRelation observe relOut) seed Set.univ joint.1.1.1] := by
  exact (legacyFailure_eager_eq_singleSaltAccepted rounds guards accepts observe
    state extractor seed witnessMap relIn relOut prover).trans
    (singleSaltAccepted_lazy_eq_eager rounds guards accepts
      (legacySingleSaltAdversary rounds prover) _).symm

/-- The concrete canonical state-restoration knowledge game, with its pure matched verifier
and named backward extractor, is exactly the accepted failure event of the public-message
single-salt native verifier. The equality holds for each arbitrary coin-bearing prover. -/
theorem coinKSExperimentProb_eq_actual_singleSaltAccepted
    {Statement GlobalSalt W WitIn Output : Type} (rounds : List Round)
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    [Finite Statement] [Finite GlobalSalt]
    [∀ i, SampleableType ((legacySpec rounds).Challenge i)]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : (Statement × GlobalSalt) →
      (protocol rounds).tree.ExecutionPath → Option Output)
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) →
      RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Statement × GlobalSalt) →
      (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Statement × GlobalSalt) → (state z).Witness → WitIn)
    (relIn : Set ((Statement × GlobalSalt) × WitIn))
    (relOut : Set (Output × W))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) (Statement × GlobalSalt) W
      (legacySpec rounds) unifSpec) :
    letI := finiteTableSampler (Input := Statement × GlobalSalt) (Salt := PUnit) rounds
    Verifier.StateRestoration.coinKSExperimentProb
      (nativeFiniteLegacyInit (Input := Statement × GlobalSalt) (Salt := PUnit) rounds
        (legacySpec rounds)
        (fun table => QueryImpl.ofFn (nativeTableToLegacy rounds table)))
      (emptyLegacyImpl rounds)
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
      (nativeBackwardLegacyExtractor (OracleSpec.ofPFunctor 0) (legacySpec rounds)
        (legacyToRestorationPath rounds) state extractor seed witnessMap)
      relIn relOut
      (nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
        (legacyToRestorationPath rounds)
        (matchedLegacyObserve rounds guards accepts observe)) prover =
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution rounds guards accepts
        (legacySingleSaltAdversary rounds prover)) ∅)}[
      badStoppedRelation state extractor
        (legacyInputRelation state witnessMap relIn)
        (legacyOutputRelation observe relOut) seed Set.univ joint.1.1.1] := by
  let _ := finiteTableSampler (Input := Statement × GlobalSalt) (Salt := PUnit) rounds
  rw [coinKSExperimentProb_eq_fixedTable]
  simpa only [nativeFiniteLegacyInit, QueryImpl.ofFn, bind_map_left] using
    legacyFailure_eq_actual_singleSaltAccepted rounds guards accepts observe
      state extractor seed witnessMap relIn relOut prover

/-- A statement-level guard schedule gives an explicitly salt-independent schedule on the
native salted input. This is the common interface of the canonical NARG verifier. -/
def liftStatementGuards {Statement GlobalSalt : Type} : (rounds : List Round) →
    GuardSchedule Statement PUnit rounds →
      GuardSchedule (Statement × GlobalSalt) PUnit rounds
  | [], _ => PUnit.unit
  | _ :: rounds, guards =>
      (fun z message salt => guards.1 z.1 message salt,
        fun message salt challenge =>
          liftStatementGuards rounds (guards.2 message salt challenge))

/-- Guard reconstruction commutes with forgetting the single global salt from the input. -/
theorem guardsPassPath_liftStatement {Statement GlobalSalt : Type}
    (rounds : List Round) (guards : GuardSchedule Statement PUnit rounds)
    (z : Statement × GlobalSalt) (path : (protocol rounds).tree.ExecutionPath) :
    guardsPassPath rounds (liftStatementGuards rounds guards) z path =
      guardsPassPath rounds guards z.1 path := by
  revert guards path
  induction rounds with
  | nil => intro guards path; rfl
  | cons round rounds ih =>
      intro guards path
      change (guards.1 z.1 path.1 PUnit.unit &&
        guardsPassPath rounds
          (liftStatementGuards rounds (guards.2 path.1 PUnit.unit path.2.1))
          z path.2.2) =
        (guards.1 z.1 path.1 PUnit.unit &&
          guardsPassPath rounds (guards.2 path.1 PUnit.unit path.2.1) z.1 path.2.2)
      rw [ih]

/-- Under salt-independent guards and terminal acceptance, the matched canonical observer
depends on the statement and completed path only. -/
theorem matchedLegacyObserve_liftStatement
    {Statement GlobalSalt Output : Type} (rounds : List Round)
    (guards : GuardSchedule Statement PUnit rounds)
    (accepts : Statement → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : Statement → (protocol rounds).tree.ExecutionPath → Option Output)
    (z : Statement × GlobalSalt) (path : (protocol rounds).tree.ExecutionPath) :
    matchedLegacyObserve rounds (liftStatementGuards rounds guards)
      (fun z path => accepts z.1 path) (fun z path => observe z.1 path) z path =
    matchedLegacyObserve rounds guards accepts observe z.1 path := by
  simp only [matchedLegacyObserve, guardsPassPath_liftStatement]

/-- The canonical salt-lifted pure verifier is definitionally the same pure decoder on the
salted input; only its statement argument is projected. -/
theorem saltedIPVerifier_nativeLegacy
    {Statement GlobalSalt Output : Type} (rounds : List Round)
    (observe : Statement → (protocol rounds).tree.ExecutionPath → Option Output) :
    saltedIPVerifier (Salt := GlobalSalt)
      (nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
        (legacyToRestorationPath rounds) observe) =
    nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
      (legacyToRestorationPath rounds) (fun z path => observe z.1 path) := rfl

/-- For every adaptive NARG prover with private coins, the canonical shared-oracle FS
extraction-failure game equals the accepted event of the actual native stopped verifier.
The prefix guards, terminal predicate and observation here depend on the unsalted statement
and completed path, matching the canonical IP verifier interface. -/
theorem fsNARGFailure_eq_actual_singleSaltAccepted
    {Statement GlobalSalt WitIn Output : Type} (rounds : List Round)
    [VCVCompatible GlobalSalt]
    [∀ i, VCVCompatible ((legacySpec rounds).Challenge i)]
    [∀ i, SampleableType ((legacySpec rounds).Challenge i)]
    [∀ i, DecidableEq ((legacySpec rounds).Message i)]
    [DecidableEq Statement]
    [Finite Statement]
    (guards : GuardSchedule Statement PUnit rounds)
    (accepts : Statement → (protocol rounds).tree.ExecutionPath → Bool)
    (observe : Statement → (protocol rounds).tree.ExecutionPath → Option Output)
    (state : (Statement × GlobalSalt) → KnowledgeState.{w})
    (extractor : (z : Statement × GlobalSalt) →
      RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Statement × GlobalSalt) →
      (path : (protocol rounds).tree.ExecutionPath) →
      Unit → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Statement × GlobalSalt) → (state z).Witness → WitIn)
    (relIn : Set (Statement × WitIn)) (langOut : Set Output)
    (P : OracleComp (((OracleSpec.ofPFunctor 0) +
      fsChallengeOracle (Statement × GlobalSalt) (legacySpec rounds)) + unifSpec)
      (Statement × FSSaltedProof (legacySpec rounds) GlobalSalt)) :
    letI := finiteTableSampler (Input := Statement × GlobalSalt) (Salt := PUnit) rounds
    Pr{let result ← (adaptiveNARGKnowledgeSoundnessExpWithCoins
      (nativeFiniteLegacyInit (Input := Statement × GlobalSalt) (Salt := PUnit) rounds
        (legacySpec rounds)
        (fun table => QueryImpl.ofFn (nativeTableToLegacy rounds table)))
      ((emptyLegacyImpl (Input := Statement × GlobalSalt) rounds).addLift
        (srChallengeQueryImpl' (Statement := Statement × GlobalSalt)
          (pSpec := legacySpec rounds)))
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
      (Verifier.singleSaltFiatShamir (Salt := GlobalSalt)
        (nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
          (legacyToRestorationPath rounds)
          (matchedLegacyObserve rounds guards accepts observe)))
      (fsSRDelegatingNargExtractor
        (nativeBackwardLegacyExtractor (OracleSpec.ofPFunctor 0) (legacySpec rounds)
          (legacyToRestorationPath rounds) state extractor seed witnessMap)) P)}[
      nargKSFailEvent relIn langOut result] =
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution rounds (liftStatementGuards rounds guards)
        (fun z path => accepts z.1 path)
        (legacySingleSaltAdversary rounds (srInducedProverKS (Salt := GlobalSalt) P))) ∅)}[
      badStoppedRelation state extractor
        (legacyInputRelation state witnessMap (relInSalted relIn))
        (legacyOutputRelation (fun z path => observe z.1 path)
          (unitOutputRelation langOut)) seed Set.univ joint.1.1.1] := by
  let _ := finiteTableSampler (Input := Statement × GlobalSalt) (Salt := PUnit) rounds
  have hcanonical := fsKSShared_failure_eq
    (auxImpl := (unifSpec.passthrough : QueryImpl unifSpec ProbComp))
    (auxImplE := (unifSpec.passthrough : QueryImpl unifSpec ProbComp))
    (V := nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
      (legacyToRestorationPath rounds)
      (matchedLegacyObserve rounds guards accepts observe))
    (E := nativeBackwardLegacyExtractor (OracleSpec.ofPFunctor 0) (legacySpec rounds)
      (legacyToRestorationPath rounds) state extractor seed witnessMap)
    (fsInit := nativeFiniteLegacyInit (Input := Statement × GlobalSalt) (Salt := PUnit)
      rounds (legacySpec rounds)
      (fun table => QueryImpl.ofFn (nativeTableToLegacy rounds table)))
    (fsImpl := emptyLegacyImpl (Input := Statement × GlobalSalt) rounds)
    (relIn := relIn) (langOut := langOut) P
  rw [saltedIPVerifier_nativeLegacy] at hcanonical
  have hbridge := coinKSExperimentProb_eq_actual_singleSaltAccepted rounds
    (liftStatementGuards rounds guards) (fun z path => accepts z.1 path)
    (fun z path => observe z.1 path) state extractor seed witnessMap
    (relInSalted relIn) (unitOutputRelation langOut)
    (srInducedProverKS (Salt := GlobalSalt) P)
  have hmatched : matchedLegacyObserve rounds (liftStatementGuards rounds guards)
      (fun z path => accepts z.1 path) (fun z path => observe z.1 path) =
      (fun (z : Statement × GlobalSalt) path =>
        matchedLegacyObserve rounds guards accepts observe z.1 path) := by
    funext z path
    exact matchedLegacyObserve_liftStatement rounds guards accepts observe z path
  rw [hmatched] at hbridge
  exact hcanonical.trans hbridge

end Interaction.Oracle.FiatShamir
