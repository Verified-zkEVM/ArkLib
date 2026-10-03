/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.Knowledge
public import ArkLib.Interaction.Oracle.Protocol
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-!
# Backward extraction in the state-restoration experiment

A fixed-round public-coin oracle protocol is presented using the existing native protocol tree.
Each restoration key contains its input, round, prover-message prefix, and salt prefix. Previous
verifier challenges are deliberately absent from the key. A key's knowledge state reconstructs
its strict ancestors from the same table, and changing its own response cannot change that state.

For an arbitrary adaptive adversary, completion reads the selected transcript's challenges from
the same cached oracle. A valid terminal knowledge witness whose backward extraction fails has
probability at most `(Q + k) * error`. Inputs and salts may have infinite types; challenges have
finite nonempty uniform samplers. The probability proof allows out-of-order and repeated queries.
This module proves the native-path knowledge bound. The concrete native verifier realization and
its terminal witness relations are separate endpoint obligations, not assumed execution equations.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

/-- One fixed round: a prover oracle message, its permitted interface, and a uniform challenge. -/
structure Round where
  Message : Type
  Challenge : Type
  interface : OracleInterface Message
  decEqMessage : DecidableEq Message
  finiteMessage : Finite Message
  finiteChallenge : Finite Challenge
  nonemptyChallenge : Nonempty Challenge
  sampleChallenge : SampleableType Challenge

attribute [instance] Round.decEqMessage Round.finiteMessage Round.finiteChallenge
  Round.nonemptyChallenge Round.sampleChallenge

/-- The fixed presentation uses native oracle-message and public-receiver nodes. -/
def protocol : List Round → Protocol
  | [] => .done
  | round :: rounds => .oracleWith round.Message round.interface
      (.public .receiver round.Challenge (fun _ => protocol rounds))

/-- Salted keys encode the round by their depth and retain each message and salt through that round.
No earlier verifier response is part of a key. -/
@[reducible] def Key (Input Salt : Type) : List Round → Type
  | [] => Empty
  | round :: rounds => (Input × round.Message × Salt) ⊕
      (round.Message × Salt × Key Input Salt rounds)

namespace Key

variable {Input Salt : Type}

/-- The first round key for this input, prover message, and salt. -/
@[match_pattern, reducible] def here {round : Round} {rounds : List Round}
    (z : Input) (message : round.Message) (salt : Salt) : Key Input Salt (round :: rounds) :=
  Sum.inl ⟨z, message, salt⟩

/-- A later round key, retaining this earlier prover message and salt. -/
@[match_pattern, reducible] def later {round : Round} {rounds : List Round}
    (message : round.Message) (salt : Salt) (key : Key Input Salt rounds) :
    Key Input Salt (round :: rounds) := Sum.inr ⟨message, salt, key⟩

instance instDecidableEq [DecidableEq Input] [DecidableEq Salt] :
    (rounds : List Round) → DecidableEq (Key Input Salt rounds)
  | [] => inferInstanceAs (DecidableEq Empty)
  | round :: rounds =>
      letI := instDecidableEq rounds
      inferInstanceAs (DecidableEq ((Input × round.Message × Salt) ⊕
        (round.Message × Salt × Key Input Salt rounds)))

/-- Recover the input selected in the complete salted key. -/
def input : {rounds : List Round} → Key Input Salt rounds → Input
  | [], key => nomatch key
  | _ :: _, .inl (z, _, _) => z
  | _ :: _, .inr (_, _, key) => key.input

/-- The answer type is the challenge alphabet of the key's round. -/
@[reducible] def Challenge : {rounds : List Round} → Key Input Salt rounds → Type
  | [], key => nomatch key
  | round :: _, .inl _ => round.Challenge
  | _ :: _, .inr (_, _, key) => key.Challenge

/-- Rounds following the challenge addressed by this key. -/
def remaining : {rounds : List Round} → Key Input Salt rounds → List Round
  | [], key => nomatch key
  | _ :: rounds, .inl _ => rounds
  | _ :: _, .inr (_, _, key) => key.remaining

instance {rounds : List Round} (key : Key Input Salt rounds) : Finite key.Challenge := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl _ => exact round.finiteChallenge
      | inr data => exact ih data.2.2

instance {rounds : List Round} (key : Key Input Salt rounds) : Nonempty key.Challenge := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl _ => exact round.nonemptyChallenge
      | inr data => exact ih data.2.2

instance {rounds : List Round} (key : Key Input Salt rounds) : SampleableType key.Challenge := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl _ => exact round.sampleChallenge
      | inr data => exact ih data.2.2

end Key

/-- A deterministic complete answer assignment, used to prove properties of cached execution. -/
abbrev Table (Input Salt : Type) (rounds : List Round) :=
  (key : Key Input Salt rounds) → key.Challenge

universe w

/-- Reconstruct the native pre-challenge extractor using this key's strict ancestor responses. -/
def keyExtractor {Input Salt : Type} : {rounds : List Round} → {state : KnowledgeState.{w}} →
    RoundExtractor (protocol rounds).tree state → (key : Key Input Salt rounds) →
    Table Input Salt rounds →
    (before : KnowledgeState.{w}) ×
      RoundExtractor (.public key.Challenge (fun _ => (protocol key.remaining).tree)) before
  | [], _, _, key, _ => nomatch key
  | _ :: _, _, extractor, .inl (_, message, _), _ =>
      ⟨(extractor message).1, (extractor message).2.2⟩
  | _ :: _, _, extractor, .inr (message, salt, key), table =>
      let challenge := table (Key.here key.input message salt)
      let afterMessage := (extractor message).2.2
      keyExtractor (afterMessage challenge).2.2 key (fun q => table (Key.later message salt q))

/-- Resampling a target key leaves its reconstructed pre-challenge extractor unchanged. -/
theorem keyExtractor_update {Input Salt : Type} {rounds : List Round}
    [DecidableEq Input] [DecidableEq Salt] {state : KnowledgeState.{w}}
    (extractor : RoundExtractor (protocol rounds).tree state)
    (key : Key Input Salt rounds) (table : Table Input Salt rounds) (value : key.Challenge) :
    keyExtractor extractor key (Function.update table key value) =
      keyExtractor extractor key table := by
  classical
  induction rounds generalizing state with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl data => rfl
      | inr data =>
          rcases data with ⟨message, salt, key⟩
          simp only [keyExtractor]
          have hhere : Function.update table (Key.later message salt key) value
              (Key.here key.input message salt) = table (Key.here key.input message salt) := by
            apply Function.update_of_ne
            simp [Key.here, Key.later]
          rw [hhere]
          have htable : (fun q => Function.update table (Key.later message salt key) value
                (Key.later message salt q)) =
              Function.update (fun q => table (Key.later message salt q)) key value := by
            funext q
            by_cases hq : q = key
            · subst q
              simp
            · simp [Function.update_of_ne hq, Function.update_of_ne
                (show Key.later message salt q ≠ Key.later message salt key by
                  simpa [Key.later] using hq)]
          rw [htable]
          exact ih _ key _ value

/-- Every receiver uses its round's uniform challenge and the same stated local error. -/
def uniformSchedule (error : ENNReal) : (rounds : List Round) →
    RoundExtractor.ChallengeSchedule (protocol rounds).tree (protocol rounds).roles
  | [] => PUnit.unit
  | round :: rounds => fun _ => ⟨⟨$ᵗ round.Challenge, error⟩,
      fun _ => uniformSchedule error rounds⟩

/-- An all-authored-prefix knowledge bound applies to every reconstructed salted key. -/
theorem keyExtractor_local_bound {Input Salt : Type} {rounds : List Round}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (protocol rounds).tree state)
    (error : ENNReal)
    (bounded : RoundExtractor.IsLocallyBounded extractor (protocol rounds).roles
      (uniformSchedule error rounds))
    (key : Key Input Salt rounds) (table : Table Input Salt rounds) :
    Pr{let response ← $ᵗ key.Challenge}[
      RoundExtractor.badChallenge (keyExtractor extractor key table).2 response] ≤ error := by
  induction rounds generalizing state with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl data =>
          rcases data with ⟨z, message, salt⟩
          have h := (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp
            (bounded message).1 PUnit.unit PUnit.unit
          exact h
      | inr data =>
          rcases data with ⟨message, salt, key⟩
          exact ih ((extractor message).2.2 (table (Key.here key.input message salt))).2.2
            ((bounded message).2 (table (Key.here key.input message salt))) key
            (fun q => table (Key.later message salt q))

/-- The complete prover-message and salt sequence returned by a restoration adversary. -/
def Messages (Salt : Type) : List Round → Type
  | [] => PUnit
  | round :: rounds => round.Message × Salt × Messages Salt rounds

/-- The restoration oracle answers each salted key with that round's challenge type. -/
abbrev oracleSpec (Input Salt : Type) (rounds : List Round) : OracleSpec (Key Input Salt rounds) :=
  OracleSpec.ofFn Key.Challenge

/-- Route a suffix key through the retained first prover message and salt. -/
def prependQuery {Input Salt : Type} {round : Round} {rounds : List Round}
    (message : round.Message) (salt : Salt) :
    QueryImpl (oracleSpec Input Salt rounds)
      (OracleComp (oracleSpec Input Salt (round :: rounds))) :=
  fun key => liftM ((oracleSpec Input Salt (round :: rounds)).query (Key.later message salt key))

/-- Complete the selected transcript by reading all challenges from the same restoration oracle. -/
def complete {Input Salt : Type} : (rounds : List Round) → Input → Messages Salt rounds →
    OracleComp (oracleSpec Input Salt rounds) (protocol rounds).tree.ExecutionPath
  | [], _, _ => pure PUnit.unit
  | round :: rounds, z, (message, salt, messages) => do
      let challenge ← liftM ((oracleSpec Input Salt (round :: rounds)).query
        (Key.here z message salt))
      let path ← simulateQ (prependQuery message salt) (complete rounds z messages)
      pure ⟨message, ⟨challenge, path⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Completion makes at most one access per protocol round, including repeated cached keys. -/
theorem complete_queryBound {Input Salt : Type} (rounds : List Round) (z : Input)
    (messages : Messages Salt rounds) :
    IsTotalQueryBound (complete rounds z messages) rounds.length := by
  induction rounds with
  | nil => trivial
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete, List.length_cons, isTotalQueryBound_query_bind_iff, Nat.add_sub_cancel]
      refine ⟨by omega, fun challenge => ?_⟩
      have h := (ih messages).simulateQ_of_step_le (step := 1)
        (fun key => show IsTotalQueryBound
          (prependQuery (Input := Input) message salt key) 1 from by
            change IsTotalQueryBound
              (liftM ((oracleSpec Input Salt (round :: rounds)).query
                (Key.later message salt key)) >>= pure) 1
            exact ⟨by omega, fun _ => trivial⟩)
      have hb := isTotalQueryBound_bind h (fun path => show IsTotalQueryBound
        (pure (⟨message, ⟨challenge, path⟩⟩ : (protocol (round :: rounds)).tree.ExecutionPath) :
          OracleComp (oracleSpec Input Salt (round :: rounds)) _) 0 from trivial)
      simpa only [Nat.mul_one, Nat.add_zero] using hb


/-- The existing native execution path reconstructed from a deterministic challenge table. -/
def completedPath {Input Salt : Type} : (rounds : List Round) → Input →
    Messages Salt rounds → Table Input Salt rounds → (protocol rounds).tree.ExecutionPath
  | [], _, _, _ => PUnit.unit
  | _ :: rounds, z, (message, salt, messages), table =>
      ⟨message, ⟨table (Key.here z message salt),
        completedPath rounds z messages (fun q => table (Key.later message salt q))⟩⟩

/-- The actual challenge keys read when completing this selected message sequence. -/
def completionKeys {Input Salt : Type} : (rounds : List Round) → Input →
    Messages Salt rounds → List (Key Input Salt rounds)
  | [], _, _ => []
  | _ :: rounds, z, (message, salt, messages) =>
      Key.here z message salt ::
        (completionKeys rounds z messages).map (Key.later message salt)

set_option backward.isDefEq.respectTransparency false in
/-- Deterministic execution of completion returns exactly the reconstructed native path. -/
theorem complete_eval {Input Salt : Type} (rounds : List Round) (z : Input)
    (messages : Messages Salt rounds) (table : Table Input Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (complete rounds z messages) =
      completedPath rounds z messages table := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, evalWithAnswerFn_simulateQ, prependQuery,
        evalWithAnswerFn_pure, completedPath]
      exact congrArg (fun path => (⟨message, ⟨table (Key.here z message salt), path⟩⟩ :
          (protocol (round :: rounds)).tree.ExecutionPath))
        (ih messages (fun q => table (Key.later message salt q)))

set_option backward.isDefEq.respectTransparency false in
/-- The completion-key list is the projection of the actual native oracle query log. -/
theorem complete_log_keys {Input Salt : Type} (rounds : List Round) (z : Input)
    (messages : Messages Salt rounds) (table : Table Input Salt rounds) :
    (tableQueryLog (complete rounds z messages) table).map Sigma.fst =
      completionKeys rounds z messages := by
  induction rounds with
  | nil => simp [complete, completionKeys]
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete, tableQueryLog_bind,
        tableQueryLog_pure, List.append_nil, tableQueryLog_simulateQ, prependQuery,
        evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, tableQueryLog_query,
        List.singleton_append, List.map_cons, ← List.map_eq_flatMap, List.map_map,
        Function.comp_def, completionKeys]
      congr 1
      simpa only [List.flatMap_singleton, List.map_map, Function.comp_def] using
        congrArg (List.map (Key.later message salt))
          (ih messages (fun q => table (Key.later message salt q)))

/-- Every completion access refers to the adversary's selected input. -/
theorem completionKeys_input {Input Salt : Type} (rounds : List Round) (z : Input)
    (messages : Messages Salt rounds) (key : Key Input Salt rounds)
    (hkey : key ∈ completionKeys rounds z messages) : key.input = z := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      rcases List.mem_cons.mp hkey with h | h
      · subst key; rfl
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
        exact ih messages q hq

set_option backward.isDefEq.respectTransparency false in
/-- A bad challenge on the completed native path is a bad key in its actual completion log. -/
theorem badChallengeOnPath_completion {Input Salt : Type} {rounds : List Round}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (protocol rounds).tree state)
    (z : Input) (messages : Messages Salt rounds) (table : Table Input Salt rounds)
    (witness : (extractor.terminalState (completedPath rounds z messages table)).Witness)
    (bad : extractor.BadChallengeOnPath (protocol rounds).roles
      (completedPath rounds z messages table) witness) :
    ∃ key ∈ completionKeys rounds z messages,
      RoundExtractor.badChallenge (keyExtractor extractor key table).2 (table key) := by
  induction rounds generalizing state with
  | nil => exact bad.elim
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      rcases bad with bad | bad
      · refine ⟨Key.here z message salt, List.mem_cons_self, ?_⟩
        exact ⟨_, bad.2.1, bad.2.2⟩
      · obtain ⟨key, hkey, hb⟩ := ih
          ((extractor message).2.2 (table (Key.here z message salt))).2.2
          messages (fun q => table (Key.later message salt q)) witness bad
        refine ⟨Key.later message salt key,
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨key, hkey, rfl⟩), ?_⟩
        have hz := completionKeys_input rounds z messages key hkey
        simp only [keyExtractor]
        rw [hz]
        exact hb

instance Key.instFinite {Input Salt : Type} [Finite Input] [Finite Salt] :
    (rounds : List Round) → Finite (Key Input Salt rounds)
  | [] => inferInstanceAs (Finite Empty)
  | round :: rounds =>
      letI : Finite (Key Input Salt rounds) := Key.instFinite (Input := Input) (Salt := Salt) rounds
      inferInstanceAs (Finite ((Input × round.Message × Salt) ⊕
        (round.Message × Salt × Key Input Salt rounds)))

/-- Run the adaptive adversary, then complete its selected transcript using the same oracle. -/
def restoredExecution {Input Salt W : Type} (rounds : List Round)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W)) :
    OracleComp (oracleSpec Input Salt rounds)
      (Input × (protocol rounds).tree.ExecutionPath × W) := do
  let (z, messages, witness) ← adversary
  let path ← complete rounds z messages
  pure (z, path, witness)

/-- The adversary and completion together make at most `Q + k` accesses. -/
theorem restoredExecution_queryBound {Input Salt W : Type} (rounds : List Round)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (bounded : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (restoredExecution rounds adversary) (Q + rounds.length) := by
  apply isTotalQueryBound_bind bounded
  rintro ⟨z, messages, witness⟩
  have h := isTotalQueryBound_bind (complete_queryBound rounds z messages)
    (fun path => show IsTotalQueryBound
      (pure (z, path, witness) : OracleComp (oracleSpec Input Salt rounds) _) 0 from trivial)
  simpa only [Nat.add_zero] using h

/-- A permitted-input key at which some later witness fails backward knowledge preservation. -/
def badKey {Input Salt : Type} {rounds : List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (key : Key Input Salt rounds) (table : Table Input Salt rounds) : Prop :=
  key.input ∈ Z ∧
    RoundExtractor.badChallenge (keyExtractor (extractor key.input) key table).2 (table key)

/-- All-prefix knowledge bounds hold when resampling each target in every background table. -/
theorem badKey_resample_bound {Input Salt : Type} {rounds : List Round}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (uniformSchedule error rounds))
    (key : Key Input Salt rounds) (table : Table Input Salt rounds) :
    Pr{let response ← $ᵗ key.Challenge}[
      badKey state extractor Z key (Function.update table key response)] ≤ error := by
  have hevent : ∀ response, badKey state extractor Z key (Function.update table key response) ↔
      key.input ∈ Z ∧
        RoundExtractor.badChallenge (keyExtractor (extractor key.input) key table).2 response := by
    intro response
    unfold badKey
    rw [keyExtractor_update]
    simp
  simp_rw [hevent]
  by_cases hz : key.input ∈ Z
  · simp only [hz, true_and]
    exact keyExtractor_local_bound (extractor key.input) error
      (bounded key.input hz) key table
  · simp only [hz, false_and]
    simp

/-- Failed backward extraction from terminal knowledge identifies an actually accessed bad key. -/
theorem restored_bad_trace {Input Salt W : Type} {rounds : List Round}
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (table : Table Input Salt rounds)
    (bad : let result :=
        evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution rounds adversary)
      result.1 ∈ Z ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))) :
    ∃ q ∈ tableQueryLog (restoredExecution rounds adversary) table,
      badKey state extractor Z q.1 table := by
  let result := evalWithAnswerFn (QueryImpl.ofFn table) adversary
  rcases hresult : result with ⟨z, messages, witness⟩
  have heval : evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution rounds adversary) =
      (z, completedPath rounds z messages table, witness) := by
    simp only [restoredExecution, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change (result.1,
      evalWithAnswerFn (QueryImpl.ofFn table) (complete rounds result.1 result.2.1), result.2.2) = _
    rw [hresult, complete_eval]
  dsimp only at bad
  rw [heval] at bad
  have hbad := RoundExtractor.extraction_failure_implies_bad_challenge (extractor z)
    (protocol rounds).roles (preserving z bad.1) _ _ bad.2.1 bad.2.2
  obtain ⟨key, hkey, hb⟩ := badChallengeOnPath_completion (extractor z) z messages table _ hbad
  have hz := completionKeys_input rounds z messages key hkey
  have hmem : key ∈ (tableQueryLog (complete rounds z messages) table).map Sigma.fst := by
    rwa [complete_log_keys]
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
  refine ⟨q, ?_, ?_⟩
  · simp only [restoredExecution, tableQueryLog_bind]
    apply List.mem_append_right
    change q ∈ tableQueryLog (complete rounds result.1 result.2.1) table ++ _
    rw [hresult]
    exact List.mem_append_left _ hq
  · change q.1.input ∈ Z ∧ _
    rw [heq, hz]
    exact ⟨bad.1, hb⟩

set_option backward.isDefEq.respectTransparency false in
/-- All-prefix round-by-round knowledge bounds imply the `(Q + k) * error` extraction bound in
the actual cached restoration/completion experiment. The input is selected adaptively, the
terminal witness is supplied by the adversary, and its named carrier map is explicit data. -/
theorem restored_extraction_bound {Input Salt W : Type} {rounds : List Round}
    [DecidableEq Input] [DecidableEq Salt]
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving (protocol rounds).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z) (protocol rounds).roles
      (uniformSchedule error rounds))
    (terminalWitness : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (restoredExecution rounds adversary)).run' ∅}[
      result.1 ∈ Z ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))] ≤
      (Q + rounds.length) * error := by
  rw [← Nat.cast_add]
  apply prEvent_randomOracle_le_of_bad_queries _ (Q + rounds.length)
    (restoredExecution_queryBound rounds adversary Q queryBound) _
    (badKey state extractor Z) error
  · exact badKey_resample_bound state extractor Z error bounded
  · exact restored_bad_trace state extractor Z preserving terminalWitness adversary

end Interaction.Oracle.Security.StateRestoration
