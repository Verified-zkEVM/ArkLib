/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.RoundByRound
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-!
# The state-restoration experiment

A fixed-round public-coin oracle protocol alternates an oracle message with a public challenge;
its shape never depends on a message or a challenge. In the state-restoration experiment every
challenge is the answer of one cached random oracle at a salted key. A key retains its input and
every prover message and salt up to its round, and no earlier challenge. The adversary queries the
oracle adaptively and selects an input, the messages and salts, and an output witness; completion
reads the challenges of that selection from the same oracle.

The passive verifier then decides on the completed transcript. Its decision has no ambient
oracle, and its resource queries are answered from the input data and the transcript's oracle
payloads, so its observation is a value of the completed transcript (`terminalObservation`,
`closedTerminalObservation`). The game is that observation of the restored execution
(`verificationGame_eq`, `closedVerificationGame_eq`).

Each key determines a receiver cursor of the protocol (`keySpine`) and the full prefix of moves
reaching it (`keyHistory`), read from an answer table. Changing the answer at the key itself does
not change that prefix (`keyHistory_update`).
-/

@[expose] public section

namespace Interaction.Core.StateRestoration
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec Oracle

/-- One round: an oracle message with its query interface, then a uniform public challenge. -/
structure Round where
  /-- The prover's oracle message. -/
  Message : Type
  /-- The verifier's public challenge. -/
  Challenge : Type
  /-- The query interface of the oracle message. -/
  interface : OracleInterface Message
  /-- The uniform sampler of the challenge alphabet. -/
  sampleChallenge : SampleableType Challenge

attribute [instance] Round.sampleChallenge

/-- The protocol: each round is an oracle message followed by its public challenge. -/
def protocol : List Round → OracleProtocol
  | [] => .pure ⟨⟩
  | round :: rounds => .liftBind (.oracle round.Message round.interface)
      (fun _ => .liftBind (.challenge round.Challenge) (fun _ => protocol rounds))

/-- Salted keys encode their round by their depth, and retain each message and salt through that
round. No verifier challenge is part of a key. -/
@[reducible] def Key (Input Salt : Type) : List Round → Type
  | [] => Empty
  | round :: rounds => (Input × round.Message × Salt) ⊕
      (round.Message × Salt × Key Input Salt rounds)

namespace Key

variable {Input Salt : Type}

/-- The first-round key for this input, prover message and salt. -/
@[match_pattern, reducible] def here {round : Round} {rounds : List Round}
    (z : Input) (message : round.Message) (salt : Salt) : Key Input Salt (round :: rounds) :=
  Sum.inl ⟨z, message, salt⟩

/-- A later-round key, retaining this first prover message and salt. -/
@[match_pattern, reducible] def later {round : Round} {rounds : List Round}
    (message : round.Message) (salt : Salt) (key : Key Input Salt rounds) :
    Key Input Salt (round :: rounds) := Sum.inr ⟨message, salt, key⟩

/-- The input recorded in a key. -/
def input : {rounds : List Round} → Key Input Salt rounds → Input
  | [], key => nomatch key
  | _ :: _, .inl (z, _, _) => z
  | _ :: _, .inr (_, _, key) => key.input

/-- The challenge alphabet of the key's round. -/
@[reducible] def Challenge : {rounds : List Round} → Key Input Salt rounds → Type
  | [], key => nomatch key
  | round :: _, .inl _ => round.Challenge
  | _ :: _, .inr (_, _, key) => key.Challenge

/-- The rounds after the key's round. -/
@[reducible] def remaining : {rounds : List Round} → Key Input Salt rounds → List Round
  | [], key => nomatch key
  | _ :: rounds, .inl _ => rounds
  | _ :: _, .inr (_, _, key) => key.remaining

instance instSampleableType {rounds : List Round} (key : Key Input Salt rounds) :
    SampleableType key.Challenge := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl _ => exact round.sampleChallenge
      | inr data => exact ih data.2.2

end Key

/-- A complete answer table of the restoration oracle. -/
abbrev Table (Input Salt : Type) (rounds : List Round) :=
  (key : Key Input Salt rounds) → key.Challenge

/-- The prover messages and salts selected by a restoration adversary. -/
def Messages (Salt : Type) : List Round → Type
  | [] => PUnit
  | round :: rounds => round.Message × Salt × Messages Salt rounds

/-- The restoration oracle answers each salted key with a challenge of its round. -/
abbrev oracleSpec (Input Salt : Type) (rounds : List Round) :
    OracleSpec (Key Input Salt rounds) :=
  OracleSpec.ofFn Key.Challenge

variable {Input Salt W : Type}

/-- Route a key of the remaining rounds through the retained first message and salt. -/
def prependQuery {round : Round} {rounds : List Round} (message : round.Message) (salt : Salt) :
    QueryImpl (oracleSpec Input Salt rounds)
      (OracleComp (oracleSpec Input Salt (round :: rounds))) :=
  fun key => liftM ((oracleSpec Input Salt (round :: rounds)).query (Key.later message salt key))

/-- Complete the selected messages to a transcript, reading every challenge from the oracle. -/
def complete : (rounds : List Round) → Input → Messages Salt rounds →
    OracleComp (oracleSpec Input Salt rounds) (PathAlong oracleSig (protocol rounds))
  | [], _, _ => pure ⟨⟩
  | round :: rounds, z, (message, salt, messages) => do
      let challenge ← liftM ((oracleSpec Input Salt (round :: rounds)).query
        (Key.here z message salt))
      let tr ← simulateQ (prependQuery message salt) (complete rounds z messages)
      pure ⟨message, ⟨challenge, tr⟩⟩

/-- Completion makes one query per round. -/
theorem complete_queryBound (rounds : List Round) (z : Input) (messages : Messages Salt rounds) :
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
      have hb := isTotalQueryBound_bind h (fun tr => show IsTotalQueryBound
        (pure (⟨message, ⟨challenge, tr⟩⟩ : PathAlong oracleSig (protocol (round :: rounds))) :
          OracleComp (oracleSpec Input Salt (round :: rounds)) _) 0 from trivial)
      simp only [Nat.mul_one, Nat.add_zero] at hb
      exact hb

/-- The transcript completed from a complete answer table. -/
def completedPath : (rounds : List Round) → Input → Messages Salt rounds →
    Table Input Salt rounds → PathAlong oracleSig (protocol rounds)
  | [], _, _, _ => ⟨⟩
  | _ :: rounds, z, (message, salt, messages), table =>
      ⟨message, ⟨table (Key.here z message salt),
        completedPath rounds z messages (fun q => table (Key.later message salt q))⟩⟩

/-- The keys completion queries, in order. -/
def completionKeys : (rounds : List Round) → Input → Messages Salt rounds →
    List (Key Input Salt rounds)
  | [], _, _ => []
  | _ :: rounds, z, (message, salt, messages) =>
      Key.here z message salt :: (completionKeys rounds z messages).map (Key.later message salt)

/-- Completion against a complete answer table returns the completed path. -/
theorem complete_eval (rounds : List Round) (z : Input) (messages : Messages Salt rounds)
    (table : Table Input Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (complete rounds z messages) =
      completedPath rounds z messages table := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, evalWithAnswerFn_simulateQ, prependQuery, completedPath]
      exact congrArg (fun tr => (⟨message, ⟨table (Key.here z message salt), tr⟩⟩ :
          PathAlong oracleSig (protocol (round :: rounds))))
        (ih messages (fun q => table (Key.later message salt q)))

/-- The keys of completion's query log against a table are `completionKeys`. -/
theorem complete_log_keys (rounds : List Round) (z : Input) (messages : Messages Salt rounds)
    (table : Table Input Salt rounds) :
    (tableQueryLog (complete rounds z messages) table).map Sigma.fst =
      completionKeys rounds z messages := by
  induction rounds with
  | nil => exact congrArg (List.map Sigma.fst) (tableQueryLog_pure _ table)
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete, tableQueryLog_bind, tableQueryLog_simulateQ, prependQuery,
        evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, tableQueryLog_query,
        List.singleton_append, List.map_cons, ← List.map_eq_flatMap, completionKeys]
      erw [tableQueryLog_pure, List.append_nil]
      congr 1
      simpa only [List.flatMap_singleton, List.map_map, Function.comp_def] using
        congrArg (List.map (Key.later message salt))
          (ih messages (fun q => table (Key.later message salt q)))

/-- Every key completion queries records the selected input. -/
theorem completionKeys_input (rounds : List Round) (z : Input) (messages : Messages Salt rounds)
    (key : Key Input Salt rounds) (hkey : key ∈ completionKeys rounds z messages) :
    key.input = z := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      rcases List.mem_cons.mp hkey with h | h
      · subst key; rfl
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
        exact ih messages q hq

/-- Run the adaptive adversary, then complete its selection with the same oracle. -/
def restoredExecution (rounds : List Round)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W)) :
    OracleComp (oracleSpec Input Salt rounds)
      (Input × PathAlong oracleSig (protocol rounds) × W) := do
  let (z, messages, witness) ← adversary
  let tr ← complete rounds z messages
  pure (z, tr, witness)

/-- The adversary's `Q` queries and completion together make at most `Q + rounds.length`. -/
theorem restoredExecution_queryBound (rounds : List Round)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : ℕ) (bounded : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (restoredExecution rounds adversary) (Q + rounds.length) := by
  apply isTotalQueryBound_bind bounded
  rintro ⟨z, messages, witness⟩
  have h := isTotalQueryBound_bind (complete_queryBound rounds z messages)
    (fun tr => show IsTotalQueryBound
      (pure (z, tr, witness) : OracleComp (oracleSpec Input Salt rounds) _) 0 from trivial)
  simpa only [Nat.add_zero] using h

/-- Against a table, the restored execution returns the adversary's selection, completed. -/
theorem restoredExecution_eval (rounds : List Round)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (table : Table Input Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution rounds adversary) =
      let r := evalWithAnswerFn (QueryImpl.ofFn table) adversary
      (r.1, completedPath rounds r.1 r.2.1 table, r.2.2) := by
  simp only [restoredExecution, evalWithAnswerFn_bind, evalWithAnswerFn_pure, complete_eval]

/-! ### Keys as receiver prefixes -/

/-- The receiver cursor at the challenge of a key's round. -/
def keySpine : {rounds : List Round} → (key : Key Input Salt rounds) →
    Cursor.Spine (protocol rounds)
      (.liftBind (OraclePos.challenge key.Challenge) (fun _ => protocol key.remaining))
  | [], key => nomatch key
  | _ :: _, .inl _ => .down ⟨⟩ (.root _)
  | _ :: _, .inr (_, _, key) => .down ⟨⟩ (.down ⟨⟩ (keySpine key))

/-- The full moves reaching a key's challenge: the key's messages and the table's answers at the
key's strict ancestors. -/
def keyHistory : {rounds : List Round} → (key : Key Input Salt rounds) →
    Table Input Salt rounds → PrefixMoves oracleSig (keySpine key)
  | [], key, _ => nomatch key
  | _ :: _, .inl (_, message, _), _ => ⟨⟨message, rfl⟩, ⟨⟩⟩
  | _ :: _, .inr (message, salt, key), table =>
      ⟨⟨message, rfl⟩, ⟨⟨table (Key.here key.input message salt), rfl⟩,
        keyHistory key (fun q => table (Key.later message salt q))⟩⟩

/-- Changing the answer at a key leaves the prefix reaching that key unchanged. -/
theorem keyHistory_update : {rounds : List Round} → [DecidableEq (Key Input Salt rounds)] →
    (key : Key Input Salt rounds) → (table : Table Input Salt rounds) → (value : key.Challenge) →
    keyHistory key (Function.update table key value) = keyHistory key table
  | [], _, key, _, _ => key.elim
  | _ :: _, _, .inl _, _, _ => rfl
  | round :: rounds, _, .inr (message, salt, key), table, value => by
    let : DecidableEq (Key Input Salt rounds) := Classical.decEq _
    have hhere : Function.update table (Key.later message salt key) value
        (Key.here key.input message salt) = table (Key.here key.input message salt) :=
      Function.update_of_ne (by simp [Key.here, Key.later]) _ _
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
    change (⟨⟨message, rfl⟩, ⟨⟨Function.update table (Key.later message salt key) value
        (Key.here key.input message salt), rfl⟩,
        keyHistory key (fun q => Function.update table (Key.later message salt key) value
          (Key.later message salt q))⟩⟩ :
        PrefixMoves oracleSig (keySpine (rounds := round :: rounds)
          (Key.later message salt key))) =
      ⟨⟨message, rfl⟩, ⟨⟨table (Key.here key.input message salt), rfl⟩,
        keyHistory key (fun q => table (Key.later message salt q))⟩⟩
    rw [hhere, htable, keyHistory_update key]

/-! ### Uniform challenges -/

/-- Every challenge node of the protocol has its round's uniform sampler. -/
@[instance_reducible]
def sampleableChallenge : (rounds : List Round) →
    (c : ChallengeNode oracleSig (protocol rounds)) →
      SampleableType (challengeSpec oracleSig (protocol rounds) c)
  | [], ⟨n, _⟩ => n.elim
  | _ :: _, ⟨.inl _, h⟩ => nomatch h
  | round :: _, ⟨.inr ⟨_, .inl _⟩, _⟩ => round.sampleChallenge
  | _ :: rounds, ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, h⟩ => sampleableChallenge rounds ⟨n, h⟩

/-- The uniform challenge implementation of the protocol. -/
def uniformDraw (rounds : List Round) :
    QueryImpl (challengeSpec oracleSig (protocol rounds)) ProbComp :=
  @challengeQueryImpl _ oracleSig (protocol rounds) (sampleableChallenge rounds)

/-- The same local error at every challenge node. -/
def uniformEps (rounds : List Round) (error : ENNReal) :
    ChallengeNode oracleSig (protocol rounds) → ENNReal := fun _ => error

/-- The challenge node of a key's round. -/
def keyNode {rounds : List Round} (key : Key Input Salt rounds) :
    ChallengeNode oracleSig (protocol rounds) :=
  spineChallenge oracleSig (keySpine key) rfl

/-- At a key's cursor the uniform draw samples the key's challenge alphabet uniformly. -/
theorem sampleAt_keySpine : {rounds : List Round} → (key : Key Input Salt rounds) →
    sampleAt oracleSig (uniformDraw rounds) (keySpine key) rfl = ($ᵗ key.Challenge)
  | [], key => key.elim
  | _ :: _, .inl _ => LawfulFunctor.id_map _
  | _ :: _, .inr (_, _, key) => sampleAt_keySpine key

/-! ### The verifier on the completed transcript -/

section Verifier

variable {rounds : List Round} {I J S T : Type} {A : I → Type} {B : J → Type}
  {inputs : OracleFamily I A} {outputs : OracleFamily J B}

/-- The decision of a verifier with no ambient oracle on a completed transcript. Resource queries
are answered from the input data and the transcript's oracle payloads. -/
def terminalObservation (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig (protocol rounds)) : Option T :=
  evalWithAnswerFn (fun q => PEmpty.elim q)
    (V.decideWith stmt.1 (projectPathAlong oracleSig _ tr) (toView _ tr)
      (sumData stmt.2 (payloads _ tr)))

/-- The accepted statement with the output oracle data computed from the same transcript. -/
def closedTerminalObservation (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig (protocol rounds)) :
    Option (T × (∀ j, B j)) :=
  (terminalObservation V stmt tr).map fun t =>
    (t, (V.outputMap stmt.1 (projectPathAlong oracleSig _ tr) (toView _ tr)).f
      (sumData stmt.2 (payloads _ tr)))

/-- The state-restoration game: the adversary queries the oracle and selects a statement, messages
and salts and an output witness; completion reads the challenges from the same oracle; the
verifier decides on the completed transcript. -/
def verificationGame (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W)) :
    OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × PathAlong oracleSig (protocol rounds) × Option T × W) := do
  let (stmt, messages, witness) ← adversary
  let tr ← complete rounds stmt messages
  pure (stmt, tr, terminalObservation V stmt tr, witness)

/-- The game with the output oracle data of the accepted statement. -/
def closedVerificationGame (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W)) :
    OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × PathAlong oracleSig (protocol rounds) × Option (T × (∀ j, B j)) × W) :=
  do
  let (stmt, messages, witness) ← adversary
  let tr ← complete rounds stmt messages
  pure (stmt, tr, closedTerminalObservation V stmt tr, witness)

/-- The game is the verifier's observation of the restored execution. -/
theorem verificationGame_eq (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W)) :
    verificationGame V adversary =
      (fun r => (r.1, r.2.1, terminalObservation V r.1 r.2.1, r.2.2)) <$>
        restoredExecution rounds adversary := by
  simp only [verificationGame, restoredExecution, _root_.map_bind, LawfulApplicative.map_pure]

/-- The closed game is the verifier's closed observation of the restored execution. -/
theorem closedVerificationGame_eq (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W)) :
    closedVerificationGame V adversary =
      (fun r => (r.1, r.2.1, closedTerminalObservation V r.1 r.2.1, r.2.2)) <$>
        restoredExecution rounds adversary := by
  simp only [closedVerificationGame, restoredExecution, _root_.map_bind, LawfulApplicative.map_pure]

end Verifier

end Interaction.Core.StateRestoration
