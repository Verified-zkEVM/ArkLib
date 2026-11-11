/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.KnowledgeComposition
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
(`verificationGame_eq`, `closedVerificationGame_eq`). It is also the result of running the parties
through `OracleVerifier.run`: the prover sends the selected messages (`scriptedProver`), and each
challenge query is answered from the completed transcript (`recordedAnswers`). That run returns
the game's transcript and observation (`run_scriptedProver`, `closedVerificationGame_eval_run`).

Each key determines a receiver cursor of the protocol (`keySpine`) and the full prefix of moves
reaching it (`keyHistory`), read from an answer table. Changing the answer at the key itself does
not change that prefix (`keyHistory_update`).
-/

@[expose] public section

universe uK uW uO u wI wJ uS uI uJ

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

/-- A key's challenge alphabet has its round's uniform sampler. -/
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

section Observation

variable {s : OracleProtocol.{u}} {I : Type uI} {S : Type uS} {A : I → Type u}
  {T : Path s → Type u} {J : Path s → Type uJ}
  {B : (p : Path s) → J p → Type u}
  {inputs : OracleFamily.{uI, u, wI} I A}
  {outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)}

/-- The decision of a verifier with no ambient oracle on a completed transcript. Resource queries
are answered from the input data and the transcript's oracle payloads. -/
def terminalObservation (V : OracleVerifier []ₒ s S T inputs outputs)
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig s) : Option (T (projectPathAlong
    oracleSig _ tr)) :=
  evalWithAnswerFn (fun q => PEmpty.elim q)
    (V.decideWith stmt.1 (projectPathAlong oracleSig _ tr) (toView _ tr)
      (stmt.2, payloads _ tr))

/-- The accepted statement with the output oracle data computed from the same transcript. -/
def closedTerminalObservation (V : OracleVerifier []ₒ s S T inputs outputs)
    (stmt : S × (∀ i, A i)) (tr : PathAlong oracleSig s) :
    Option (T (projectPathAlong oracleSig _ tr) ×
      (∀ j, B (projectPathAlong oracleSig _ tr) j)) :=
  (terminalObservation V stmt tr).map fun t =>
    (t, (V.outputMap stmt.1 (projectPathAlong oracleSig _ tr) (toView _ tr)).f
      (stmt.2, payloads _ tr))

end Observation

section Verifier

variable {rounds : List Round} {I S : Type} {A : I → Type}
  {T : Path (protocol rounds) → Type} {J : Path (protocol rounds) → Type}
  {B : (p : Path (protocol rounds)) → J p → Type}
  {inputs : OracleFamily.{0, 0, wI} I A}
  {outputs : (p : Path (protocol rounds)) → OracleFamily.{0, 0, wJ} (J p) (B p)}

/-- The state-restoration game: the adversary queries the oracle and selects a statement, messages
and salts and an output witness; completion reads the challenges from the same oracle; the
verifier decides on the completed transcript. -/
def verificationGame (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W)) :
    OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × (tr : PathAlong oracleSig (protocol rounds)) ×
        Option (T (projectPathAlong oracleSig _ tr)) × W) := do
  let (stmt, messages, witness) ← adversary
  let tr ← complete rounds stmt messages
  pure ⟨stmt, tr, terminalObservation V stmt tr, witness⟩

/-- The game with the output oracle data of the accepted statement. -/
def closedVerificationGame (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W)) :
    OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × (tr : PathAlong oracleSig (protocol rounds)) ×
        Option (OracleVerifier.Output T B (projectPathAlong oracleSig _ tr)) × W) :=
  do
  let (stmt, messages, witness) ← adversary
  let tr ← complete rounds stmt messages
  pure ⟨stmt, tr, closedTerminalObservation V stmt tr, witness⟩

/-- The game is the verifier's observation of the restored execution. -/
theorem verificationGame_eq (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W)) :
    verificationGame V adversary =
      (fun r => (⟨r.1, r.2.1, terminalObservation V r.1 r.2.1, r.2.2⟩ :
        (S × (∀ i, A i)) × (tr : PathAlong oracleSig (protocol rounds)) ×
          Option (T (projectPathAlong oracleSig _ tr)) × W)) <$>
        restoredExecution rounds adversary := by
  simp only [verificationGame, restoredExecution, _root_.map_bind, LawfulApplicative.map_pure]

/-- The closed game is the verifier's closed observation of the restored execution. -/
theorem closedVerificationGame_eq (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W)) :
    closedVerificationGame V adversary =
      (fun r => (⟨r.1, r.2.1, closedTerminalObservation V r.1 r.2.1, r.2.2⟩ :
        (S × (∀ i, A i)) × (tr : PathAlong oracleSig (protocol rounds)) ×
          Option (OracleVerifier.Output T B (projectPathAlong oracleSig _ tr)) × W)) <$>
        restoredExecution rounds adversary := by
  simp only [closedVerificationGame, restoredExecution, _root_.map_bind, LawfulApplicative.map_pure]

/-- Against a complete table, the plain game completes the adversary's selected transcript. -/
theorem verificationGame_eval (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (table : Table (S × (∀ i, A i)) Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (verificationGame V adversary) =
      let selection := evalWithAnswerFn (QueryImpl.ofFn table) adversary
      let tr := completedPath rounds selection.1 selection.2.1 table
      ⟨selection.1, tr, terminalObservation V selection.1 tr, selection.2.2⟩ := by
  rw [verificationGame_eq, evalWithAnswerFn_map, restoredExecution_eval]

/-- Against a complete table, the closed game keeps the dependent claim at the completed path. -/
theorem closedVerificationGame_eval
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (table : Table (S × (∀ i, A i)) Salt rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (closedVerificationGame V adversary) =
      let selection := evalWithAnswerFn (QueryImpl.ofFn table) adversary
      let tr := completedPath rounds selection.1 selection.2.1 table
      ⟨selection.1, tr, closedTerminalObservation V selection.1 tr, selection.2.2⟩ := by
  rw [closedVerificationGame_eq, evalWithAnswerFn_map, restoredExecution_eval]

end Verifier

/-! ### Running the scripted prover against recorded challenges

The game evaluates the verifier's observation on a completed transcript; it runs no parties. The
correspondence below runs the parties through `OracleVerifier.run`: the prover sends the selected
messages, and every challenge query is answered from a recorded transcript. When that transcript
carries the selected messages, the run returns it together with the closed observation
(`run_scriptedProver`). Instantiated with the transcript completed against an answer table, the
run returns the game's transcript and observation (`closedVerificationGame_eval_run`). -/

section Replay

/-- The prover that sends the selected messages and makes no query. Salts are not sent. -/
def scriptedProver {ι : Type} {ambient : OracleSpec ι} :
    (rounds : List Round) → Messages Salt rounds →
      Prover oracleSig ambient (protocol rounds) (fun _ => PUnit)
  | [], _ => (pure ⟨⟩ : OracleComp ambient PUnit)
  | _ :: rounds, (message, _, messages) =>
      pure ⟨message, pure fun _ => scriptedProver rounds messages⟩

/-- Each challenge node is answered with the recorded challenge of the node's round. The protocol
shape does not depend on moves, so the round is the node's depth. -/
def recordedChallenges : (rounds : List Round) → PathAlong oracleSig (protocol rounds) →
    QueryImpl (challengeSpec oracleSig (protocol rounds)) Id
  | [], _, ⟨n, _⟩ => n.elim
  | _ :: _, _, ⟨.inl _, h⟩ => nomatch h
  | _ :: _, ⟨_, ⟨c, _⟩⟩, ⟨.inr ⟨_, .inl _⟩, _⟩ => c
  | _ :: rounds, ⟨_, ⟨_, tr⟩⟩, ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, h⟩ => recordedChallenges rounds tr ⟨n, h⟩

/-- The answers of a run without ambient oracle: every challenge is read from the recorded
transcript. -/
def recordedAnswers (rounds : List Round) (tr : PathAlong oracleSig (protocol rounds)) :
    QueryImpl ([]ₒ + challengeSpec oracleSig (protocol rounds)) Id
  | .inl q => PEmpty.elim q
  | .inr c => recordedChallenges rounds tr c

/-- A transcript carries the selected messages. -/
def MatchesMessages : (rounds : List Round) → Messages Salt rounds →
    PathAlong oracleSig (protocol rounds) → Prop
  | [], _, _ => True
  | _ :: rounds, (message, _, messages), ⟨sent, ⟨_, tr⟩⟩ =>
      message = sent ∧ MatchesMessages rounds messages tr

/-- The transcript completed from a selection carries its messages. -/
theorem completedPath_matchesMessages : (rounds : List Round) → (z : Input) →
    (messages : Messages Salt rounds) → (table : Table Input Salt rounds) →
    MatchesMessages rounds messages (completedPath rounds z messages table)
  | [], _, _, _ => trivial
  | _ :: rounds, z, (_, _, messages), _ =>
      ⟨rfl, completedPath_matchesMessages rounds z messages _⟩

/-- Every transcript in the open completion program's support carries the selected messages.
The statement requires no consistent answer table. -/
theorem complete_support_matches (rounds : List Round) (z : Input)
    (messages : Messages Salt rounds) (tr : PathAlong oracleSig (protocol rounds))
    (supported : tr ∈ support (complete rounds z messages)) :
    MatchesMessages rounds messages tr := by
  induction rounds with
  | nil => trivial
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete] at supported
      obtain ⟨challenge, _, hs⟩ := OracleComp.mem_support_bind_peel _ _ supported
      obtain ⟨tail, htail, hpure⟩ := OracleComp.mem_support_bind_peel _ _ hs
      have same := OracleComp.eq_of_mem_support_pure _ hpure
      subst tr
      exact ⟨rfl, ih messages tail (support_simulateQ_subset _ _ htail)⟩

/-- Interpreting the scripted prover's first slot leaves a pure send of its first message. -/
private theorem simulate_scriptedProver_cons {ι κ : Type} {ambient : OracleSpec ι}
    {spec : OracleSpec κ} (impl : QueryImpl ambient (OracleComp spec)) (round : Round)
    (rounds : List Round) (message : round.Message) (salt : Salt)
    (messages : Messages Salt rounds) :
    Prover.simulate impl (scriptedProver (ambient := ambient) (round :: rounds)
      (message, salt, messages)) =
      (pure ⟨message, pure fun _ => Prover.simulate impl
        (scriptedProver (ambient := ambient) rounds messages)⟩ : OracleComp spec _) := rfl

/-- Interpreting the scripted prover's slots leaves it the scripted prover. -/
theorem simulate_scriptedProver {ι κ : Type} {ambient : OracleSpec ι} {spec : OracleSpec κ}
    (impl : QueryImpl ambient (OracleComp spec)) : (rounds : List Round) →
    (messages : Messages Salt rounds) →
    Prover.simulate impl (scriptedProver (ambient := ambient) rounds messages) =
      scriptedProver rounds messages
  | [], _ => rfl
  | round :: rounds, (message, salt, messages) => by
    rw [simulate_scriptedProver_cons]
    exact congrArg (fun next : Prover oracleSig spec (protocol rounds) (fun _ => PUnit) =>
      (pure ⟨message, pure fun _ => next⟩ : OracleComp spec
        ((_ : round.Message) × OracleComp spec (round.Challenge →
          Prover oracleSig spec (protocol rounds) (fun _ => PUnit)))))
      (simulate_scriptedProver impl rounds messages)

/-- The runner at a challenge node: the focal observation slot, then the counterpart draw. -/
private theorem run_challengeNode {m : Type → Type} [Monad m] [LawfulMonad m] (C : Type)
    (rest : OraclePoly.B (OraclePos.challenge C) → OracleProtocol)
    {OutP OutC : PathAlong oracleSig (.liftBind (OraclePos.challenge C) rest) → Type}
    (p : Focal oracleSig m (.liftBind (OraclePos.challenge C) rest) OutP)
    (c : Counterpart oracleSig m (.liftBind (OraclePos.challenge C) rest) OutC) :
    TwoParty.Lens.run (l := oracleSig) (.liftBind (OraclePos.challenge C) rest) p c = (do
      let f ← (p : m ((x : Move oracleSig (OraclePos.challenge C)) →
        Focal oracleSig m (rest (oracleSig.toFunB _ x)) (fun tr => OutP ⟨x, tr⟩)))
      let v ← (c : m ((x : Move oracleSig (OraclePos.challenge C)) ×
        Counterpart oracleSig m (rest (oracleSig.toFunB _ x)) (fun tr => OutC ⟨x, tr⟩)))
      let r ← TwoParty.Lens.run (l := oracleSig) (rest (oracleSig.toFunB _ v.1)) (f v.1) v.2
      pure (⟨⟨v.1, r.1⟩, r.2.1, r.2.2⟩ : (tr : PathAlong oracleSig
        (.liftBind (OraclePos.challenge C) rest)) × OutP tr × OutC tr)) := by
  rw [run_node]
  rfl

/-- One round of the scripted run: the prover sends its message, the sampler draws at the first
challenge node, and the run continues on the remaining rounds with the shifted draws. -/
private theorem evalWithAnswerFn_run_scriptedProver_cons {κ : Type} {spec : OracleSpec κ}
    (answers : QueryImpl spec Id) (round : Round) (rounds : List Round)
    (message : round.Message) (salt : Salt) (messages : Messages Salt rounds)
    (draw : (c : ChallengeNode oracleSig (protocol (round :: rounds))) →
      OracleComp spec (challengeSpec oracleSig (protocol (round :: rounds)) c)) :
    evalWithAnswerFn answers (TwoParty.Lens.run (protocol (round :: rounds))
      (scriptedProver (ambient := spec) (round :: rounds) (message, salt, messages))
      (sampler oracleSig (protocol (round :: rounds)) draw)) =
      let x := evalWithAnswerFn answers
        (draw ⟨.inr ⟨oracleSig.toFunB (.oracle round.Message round.interface) message, .inl ⟨⟩⟩,
          rfl⟩)
      let r := evalWithAnswerFn answers (TwoParty.Lens.run (protocol rounds)
        (scriptedProver (ambient := spec) rounds messages)
        (sampler oracleSig (protocol rounds) (fun c =>
          draw ⟨.inr ⟨oracleSig.toFunB (.oracle round.Message round.interface) message,
            .inr ⟨oracleSig.toFunB (.challenge round.Challenge) x, c.val⟩⟩, c.property⟩)))
      ⟨⟨message, ⟨x, r.1⟩⟩, r.2⟩ := by
  refine (congrArg (evalWithAnswerFn answers)
    (run_node (l := oracleSig) (.oracle round.Message round.interface) _ _ _)).trans ?_
  change evalWithAnswerFn answers (step .sender _ _ _ _) = _
  simp only [step, Schedule.seq]
  have prover : scriptedProver (ambient := spec) (round :: rounds) (message, salt, messages) =
      pure ⟨message, pure fun _ => scriptedProver rounds messages⟩ := rfl
  have afterMessage : sampler oracleSig (protocol (round :: rounds)) draw =
      pure (fun x => sampler oracleSig
        (FreeM.liftBind (OraclePos.challenge round.Challenge) fun _ => protocol rounds :
          OracleProtocol)
        (fun c => draw ⟨.inr ⟨oracleSig.toFunB (.oracle round.Message round.interface) x,
          c.val⟩, c.property⟩)) := rfl
  rw [prover, afterMessage]
  change evalWithAnswerFn answers (do
      let x ← TwoParty.Lens.run (l := oracleSig) (OutP := fun _ => PUnit) (OutC := fun _ => PUnit)
        (FreeM.liftBind (OraclePos.challenge round.Challenge) fun _ => protocol rounds :
          OracleProtocol)
        (pure fun _ => scriptedProver (ambient := spec) rounds messages)
        (sampler oracleSig
          (FreeM.liftBind (OraclePos.challenge round.Challenge) fun _ => protocol rounds :
            OracleProtocol)
          (fun c => draw ⟨.inr ⟨oracleSig.toFunB (.oracle round.Message round.interface) message,
            c.val⟩, c.property⟩))
      pure (⟨⟨message, x.1⟩, x.2.1, x.2.2⟩ :
        (_ : PathAlong oracleSig (protocol (round :: rounds))) × PUnit × PUnit)) = _
  have atChallenge : sampler oracleSig
      (FreeM.liftBind (OraclePos.challenge round.Challenge) fun _ => protocol rounds :
        OracleProtocol)
      (fun c => draw ⟨.inr ⟨oracleSig.toFunB (.oracle round.Message round.interface) message,
        c.val⟩, c.property⟩) =
      (fun x => ⟨x, sampler oracleSig (protocol rounds) (fun c =>
        draw ⟨.inr ⟨oracleSig.toFunB (.oracle round.Message round.interface) message,
          .inr ⟨oracleSig.toFunB (.challenge round.Challenge) x, c.val⟩⟩, c.property⟩)⟩) <$>
        draw ⟨.inr ⟨oracleSig.toFunB (.oracle round.Message round.interface) message, .inl ⟨⟩⟩,
          rfl⟩ :=
    Functor.map_map _ _ _
  rw [run_challengeNode, atChallenge]
  simp only [evalWithAnswerFn_bind]
  erw [evalWithAnswerFn_map]
  rfl

/-- The scripted prover against draws whose answers are the recorded challenges of a transcript
carrying its messages returns that transcript. -/
theorem evalWithAnswerFn_run_scriptedProver {κ : Type} {spec : OracleSpec κ}
    (answers : QueryImpl spec Id) :
    (rounds : List Round) → (messages : Messages Salt rounds) →
    (tr : PathAlong oracleSig (protocol rounds)) → MatchesMessages rounds messages tr →
    (draw : (c : ChallengeNode oracleSig (protocol rounds)) →
      OracleComp spec (challengeSpec oracleSig (protocol rounds) c)) →
    (∀ c, evalWithAnswerFn answers (draw c) = recordedChallenges rounds tr c) →
    evalWithAnswerFn answers (TwoParty.Lens.run (protocol rounds)
      (scriptedProver (ambient := spec) rounds messages)
      (sampler oracleSig (protocol rounds) draw)) = ⟨tr, ⟨⟩, ⟨⟩⟩
  | [], _, ⟨⟩, _, _, _ => rfl
  | round :: rounds, (message, salt, messages), ⟨_, ⟨_, tr⟩⟩, ⟨rfl, carried⟩, draw, answered => by
    rw [evalWithAnswerFn_run_scriptedProver_cons]
    dsimp only
    rw [answered]
    erw [evalWithAnswerFn_run_scriptedProver answers rounds messages tr carried _
      (fun _ => answered _)]
    rfl

section Verifier

variable {rounds : List Round} {I : Type uI} {S : Type uS} {A : I → Type}
  {T : Path (protocol rounds) → Type} {J : Path (protocol rounds) → Type}
  {B : (p : Path (protocol rounds)) → J p → Type}
  {inputs : OracleFamily.{uI, 0, wI} I A}
  {outputs : (p : Path (protocol rounds)) → OracleFamily.{0, 0, wJ} (J p) (B p)}

/-- Running the scripted prover with the passive verifier, every challenge read from a transcript
that carries the prover's messages, returns that transcript and the closed observation on it. -/
theorem run_scriptedProver (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (stmt : S × (∀ i, A i)) (messages : Messages Salt rounds)
    (tr : PathAlong oracleSig (protocol rounds)) (carried : MatchesMessages rounds messages tr) :
    evalWithAnswerFn (recordedAnswers rounds tr)
      (V.run stmt.1 stmt.2 (scriptedProver rounds messages)) =
      ⟨tr, ⟨⟩, closedTerminalObservation V stmt tr⟩ := by
  simp only [OracleVerifier.run_eq, evalWithAnswerFn_bind, simulate_scriptedProver]
  rw [evalWithAnswerFn_run_scriptedProver (recordedAnswers rounds tr) rounds messages tr carried _
    (fun _ => rfl)]
  simp only [evalWithAnswerFn_simulateQ, evalWithAnswerFn_pure, closedTerminalObservation,
    terminalObservation, OracleVerifier.decideWith]
  congr 4
  funext q
  rcases q with q | q
  · exact q.elim
  · rfl

end Verifier

section Verifier

variable {rounds : List Round} {I S : Type} {A : I → Type}
  {T : Path (protocol rounds) → Type} {J : Path (protocol rounds) → Type}
  {B : (p : Path (protocol rounds)) → J p → Type}
  {inputs : OracleFamily.{0, 0, wI} I A}
  {outputs : (p : Path (protocol rounds)) → OracleFamily.{0, 0, wJ} (J p) (B p)}

/-- Every supported completion can be replayed by the actual parties with its recorded
challenges, returning the completed transcript and its closed terminal observation. -/
theorem run_scriptedProver_of_mem_support
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (stmt : S × (∀ i, A i)) (messages : Messages Salt rounds)
    (tr : PathAlong oracleSig (protocol rounds))
    (supported : tr ∈ support (complete rounds stmt messages)) :
    evalWithAnswerFn (recordedAnswers rounds tr)
      (V.run stmt.1 stmt.2 (scriptedProver rounds messages)) =
      ⟨tr, ⟨⟩, closedTerminalObservation V stmt tr⟩ :=
  run_scriptedProver V stmt messages tr (complete_support_matches rounds stmt messages tr supported)

/-- Against every answer table, running the scripted prover of the adversary's selection, every
challenge read from the game's completed transcript, returns the closed game's transcript and
observation. -/
theorem closedVerificationGame_eval_run
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (table : Table (S × (∀ i, A i)) Salt rounds) :
    let selection := evalWithAnswerFn (QueryImpl.ofFn table) adversary
    let game := evalWithAnswerFn (QueryImpl.ofFn table) (closedVerificationGame V adversary)
    evalWithAnswerFn (recordedAnswers rounds game.2.1)
      (V.run selection.1.1 selection.1.2 (scriptedProver rounds selection.2.1)) =
      ⟨game.2.1, ⟨⟩, game.2.2.1⟩ := by
  dsimp only
  rw [closedVerificationGame_eval]
  exact run_scriptedProver V _ _ _ (completedPath_matchesMessages rounds _ _ table)

/-- The plain game's transcript and decision are those of the same run. -/
theorem verificationGame_eval_run
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (table : Table (S × (∀ i, A i)) Salt rounds) :
    let selection := evalWithAnswerFn (QueryImpl.ofFn table) adversary
    let game := evalWithAnswerFn (QueryImpl.ofFn table) (verificationGame V adversary)
    let run := evalWithAnswerFn (recordedAnswers rounds game.2.1)
      (V.run selection.1.1 selection.1.2 (scriptedProver rounds selection.2.1))
    (⟨run.1, run.2.2.map Prod.fst⟩ :
      (tr : PathAlong oracleSig (protocol rounds)) ×
        Option (T (projectPathAlong oracleSig _ tr))) = ⟨game.2.1, game.2.2.1⟩ := by
  dsimp only
  rw [verificationGame_eval]
  rw [run_scriptedProver V _ _ _ (completedPath_matchesMessages rounds _ _ table)]
  simp [closedTerminalObservation, Option.map_map, Function.comp_def]

end Verifier

end Replay

/-! ### Knowledge soundness -/

section Knowledge

variable {S W : Type} {Win : S → Type uW} {admissible : S → Prop}
  {relIn : (stmt : S) → Win stmt → Prop}

/-- A completion key whose challenge fails preservation on the witness extracted from the
actual remaining transcript and the supplied output witness. Later keys restrict the same state
function below the earlier recorded moves, preserving the suffix extraction. -/
def badChallengeOnCompletionAux {Salt : Type} :
    {rounds : List Round} → {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO} →
    {Win : S → Type uK} → {admissible : S → Prop} →
    {relIn : (stmt : S) → Win stmt → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) →
      Wout stmt tr → Prop} →
    (F : KnowledgeStateFunction.{0, uK, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput) →
    (z : S) → (messages : Messages Salt rounds) → (table : Table S Salt rounds) →
    Wout z (completedPath rounds z messages table) → Key S Salt rounds → Prop
  | [], _, _, _, _, _, _, _, _, _, _, key => key.elim
  | _ :: rounds, Wout, _, _, _, _, F, z, (message, salt, messages), table, w, .inl data =>
    data = (z, message, salt) ∧
      let challenge := table (Key.here z message salt)
      let rest := completedPath rounds z messages (fun q => table (Key.later message salt q))
      let G := F.child message
      let after := (G.child challenge).extractFrom z (.root _) ⟨⟩ rest
        (cast (congrArg (fun tr => Wout z ⟨message, ⟨challenge, tr⟩⟩)
          (PrefixMoves.completeWith_root oracleSig rest).symm) w)
      ¬ G.toFun z (.root _) ⟨⟩ (G.extractStep z (.root _) ⟨⟩ challenge after) ∧
        (G.child challenge).toFun z (.root _) ⟨⟩ after
  | _ :: _, _, _, _, _, _, F, z, (message, salt, messages), table, w, .inr (m, s, key) =>
    m = message ∧ s = salt ∧
      badChallengeOnCompletionAux ((F.child message).child (table (Key.here z message salt))) z
        messages (fun q => table (Key.later message salt q)) w key

/-- The witness-preserving completion law at an independent input-witness universe. -/
def BadChallengeOnCompletion {Salt : Type} :
    {rounds : List Round} → {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO} →
    {Win : S → Type uW} → {admissible : S → Prop} →
    {relIn : (stmt : S) → Win stmt → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) →
      Wout stmt tr → Prop} →
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput) →
    (z : S) → (messages : Messages Salt rounds) → (table : Table S Salt rounds) →
    Wout z (completedPath rounds z messages table) → Key S Salt rounds → Prop := by
  intro rounds Wout Win admissible relIn validOutput F
  exact badChallengeOnCompletionAux F.withRootWitness

/-- A witness-preserving bad transition on a completed transcript belongs to one of the actual
completion keys. This only locates the generic bad transition; it does not repeat extraction. -/
theorem badChallengeAlong_completionAux {Salt : Type} :
    {rounds : List Round} → {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO} →
    {Win : S → Type uK} → {admissible : S → Prop} →
    {relIn : (stmt : S) → Win stmt → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) →
      Wout stmt tr → Prop} →
    (F : KnowledgeStateFunction.{0, uK, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput) →
    (z : S) → (messages : Messages Salt rounds) → (table : Table S Salt rounds) →
    (w : Wout z (completedPath rounds z messages table)) →
    F.BadChallengeAlong z (completedPath rounds z messages table) w →
    ∃ key ∈ completionKeys rounds z messages, BadChallengeOnCompletion F z messages table w key
  | [], _, _, _, _, _, _, _, _, _, _, bad => bad.elim
  | _ :: rounds, _, _, _, _, _, F, z, (message, salt, messages), table, w, bad => by
    rcases (F.badChallengeAlong_liftBind z message _ w).mp bad with bad | bad
    · cases bad.1
    rcases ((F.child message).badChallengeAlong_liftBind z
      (table (Key.here z message salt)) _ w).mp bad with bad | bad
    · exact ⟨Key.here z message salt, List.mem_cons_self, rfl, bad.2⟩
    · obtain ⟨key, hkey, hb⟩ := badChallengeAlong_completionAux
        ((F.child message).child (table (Key.here z message salt))) z messages
        (fun q => table (Key.later message salt q)) w bad
      exact ⟨Key.later message salt key,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨key, hkey, rfl⟩), rfl, rfl, hb⟩

/-- The witness-preserving completion law at an independent input-witness universe. -/
theorem badChallengeAlong_completion {Salt : Type} :
    {rounds : List Round} → {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO} →
    {Win : S → Type uW} → {admissible : S → Prop} →
    {relIn : (stmt : S) → Win stmt → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) →
      Wout stmt tr → Prop} →
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput) →
    (z : S) → (messages : Messages Salt rounds) → (table : Table S Salt rounds) →
    (w : Wout z (completedPath rounds z messages table)) →
    F.BadChallengeAlong z (completedPath rounds z messages table) w →
    ∃ key ∈ completionKeys rounds z messages, BadChallengeOnCompletion F z messages table w
    key := by
  intro rounds Wout Win admissible relIn validOutput F
  exact badChallengeAlong_completionAux F.withRootWitness

/-- Extraction failure on a valid completed transcript identifies a completion key together with
the failing transition on the actual suffix-extracted witness. The arbitrary-protocol extraction
result is `KnowledgeStateFunction.extraction_failure_implies_badChallengeAlong`. -/
theorem exists_badChallenge_of_extraction_failure {Salt : Type} {rounds : List Round}
    {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO}
    {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) →
      Wout stmt tr → Prop}
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput)
    (z : S) (messages : Messages Salt rounds) (table : Table S Salt rounds)
    (w : Wout z (completedPath rounds z messages table))
    (valid : validOutput z (completedPath rounds z messages table) w)
    (failure : ¬ F.toFun z (.root _) ⟨⟩
      (F.extractFrom z (.root _) ⟨⟩ (completedPath rounds z messages table)
        (cast (congrArg (Wout z)
          (PrefixMoves.completeWith_root oracleSig (completedPath rounds z messages table)).symm)
          w))) :
    ∃ key ∈ completionKeys rounds z messages, BadChallengeOnCompletion F z messages table w key :=
  badChallengeAlong_completion F z messages table w
    (F.extraction_failure_implies_badChallengeAlong_of_root z _ w valid failure)

/-- Forgetting the named suffix witness of a bad completion key gives the bad-challenge event
used by the local probability bound. -/
theorem BadChallengeOnCompletion.mem_badChallengeAux {Salt : Type} :
    {rounds : List Round} → {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO} →
    {Win : S → Type uK} → {admissible : S → Prop} →
    {relIn : (stmt : S) → Win stmt → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) →
      Wout stmt tr → Prop} →
    (F : KnowledgeStateFunction.{0, uK, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput) →
    (z : S) → (messages : Messages Salt rounds) → (table : Table S Salt rounds) →
    (w : Wout z (completedPath rounds z messages table)) → (key : Key S Salt rounds) →
    key ∈ completionKeys rounds z messages → BadChallengeOnCompletion F z messages table w key →
    table key ∈ F.badChallenge (keySpine key) (keyHistory key table) z
  | [], _, _, _, _, _, _, _, _, _, _, key, _, _ => key.elim
  | _ :: _, _, _, _, _, _, _, _, (_, _, _), _, _, .inl _, _, ⟨rfl, hb⟩ =>
    ⟨_, hb.1, hb.2⟩
  | _ :: rounds, _, _, _, _, _, F, z, (message, salt, messages), table, w,
      .inr (_, _, key), hkey, ⟨rfl, rfl, hb⟩ => by
    have hk : key ∈ completionKeys rounds z messages := by
      simpa [completionKeys, Key.here, Key.later] using hkey
    have ih := BadChallengeOnCompletion.mem_badChallengeAux
      ((F.child message).child (table (Key.here z message salt))) z messages
      (fun q => table (Key.later message salt q)) w key hk hb
    have hz := completionKeys_input rounds z messages key hk
    change table (Key.later message salt key) ∈ F.badChallenge
      (.down ⟨⟩ (.down ⟨⟩ (keySpine key)))
      ⟨⟨message, rfl⟩, ⟨⟨table (Key.here key.input message salt), rfl⟩,
        keyHistory key (fun q => table (Key.later message salt q))⟩⟩ z
    rw [hz]
    exact ih

variable {Salt : Type} {rounds : List Round}
  {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO}
  {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) →
    Wout stmt tr → Prop}

/-- The witness-preserving completion law at an independent input-witness universe. -/
theorem BadChallengeOnCompletion.mem_badChallenge {Salt : Type} :
    {rounds : List Round} → {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO} →
    {Win : S → Type uW} → {admissible : S → Prop} →
    {relIn : (stmt : S) → Win stmt → Prop} →
    {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) →
      Wout stmt tr → Prop} →
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput) →
    (z : S) → (messages : Messages Salt rounds) → (table : Table S Salt rounds) →
    (w : Wout z (completedPath rounds z messages table)) → (key : Key S Salt rounds) →
    key ∈ completionKeys rounds z messages → BadChallengeOnCompletion F z messages table w key →
    table key ∈ F.badChallenge (keySpine key) (keyHistory key table) z := by
  intro rounds Wout Win admissible relIn validOutput F
  exact BadChallengeOnCompletion.mem_badChallengeAux F.withRootWitness

/-- An admissible key whose answer is a bad challenge at the key's prefix. -/
def badKey
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput)
    (key : Key S Salt rounds) (table : Table S Salt rounds) : Prop :=
  admissible key.input ∧ table key ∈ F.badChallenge (keySpine key) (keyHistory key table) key.input

/-- Resampling the answer at a key makes it bad with probability at most the error of the key's
challenge node, for every background table. -/
theorem badKey_resample_bound [DecidableEq (Key S Salt rounds)]
    {F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput}
    {ε : ChallengeNode oracleSig (protocol rounds) → ENNReal}
    (bounded : F.LocallyBounded (uniformDraw rounds) ε)
    (key : Key S Salt rounds) (table : Table S Salt rounds) :
    Pr{let u ← $ᵗ key.Challenge}[badKey F key (Function.update table key u)] ≤
      ε (keyNode key) := by
  have event : ∀ u, badKey F key (Function.update table key u) ↔
      admissible key.input ∧
        u ∈ F.badChallenge (keySpine key) (keyHistory key table) key.input := by
    intro u
    unfold badKey
    rw [keyHistory_update, Function.update_self]
  simp_rw [event]
  by_cases hz : admissible key.input
  · simp only [hz, true_and]
    let : MeasurableSpace key.Challenge := ⊤
    rw [prEvent_eq_evalDist_of_discrete]
    have h := bounded key.input hz _ _ (keySpine key) rfl (keyHistory key table)
    rw [sampleAt_keySpine] at h
    exact h
  · simp [hz]

/-- On every answer table, a run of the restored execution whose output is valid and whose
extraction fails queries a bad key. The adversary's witness is read at the completed transcript by
`readOut`. -/
theorem restored_bad_trace
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput)
    (readOut : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) → W → Wout stmt tr)
    (adversary : OracleComp (oracleSpec S Salt rounds) (S × Messages Salt rounds × W))
    (table : Table S Salt rounds)
    (bad : let result :=
        evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution rounds adversary)
      admissible result.1 ∧
        validOutput result.1 result.2.1 (readOut result.1 result.2.1 result.2.2) ∧
        ¬ relIn result.1
          (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2))) :
    ∃ q ∈ tableQueryLog (restoredExecution rounds adversary) table, badKey F q.1 table := by
  let result := evalWithAnswerFn (QueryImpl.ofFn table) adversary
  rcases hresult : result with ⟨z, messages, w⟩
  have heval : evalWithAnswerFn (QueryImpl.ofFn table) (restoredExecution rounds adversary) =
      (z, completedPath rounds z messages table, w) := by
    rw [restoredExecution_eval]
    change (result.1, completedPath rounds result.1 result.2.1 table, result.2.2) = _
    rw [hresult]
  dsimp only at bad
  rw [heval] at bad
  obtain ⟨hadm, hvalid, hfail⟩ := bad
  obtain ⟨key, hkey, hb⟩ := exists_badChallenge_of_extraction_failure F z messages table
    (readOut z _ w) hvalid (fun holds => hfail (F.root z hadm _ holds))
  have hb := BadChallengeOnCompletion.mem_badChallenge F z messages table (readOut z _ w)
    key hkey hb
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
  · rw [heq]
    refine ⟨hz ▸ hadm, ?_⟩
    rw [hz]
    exact hb

/-- Knowledge soundness of the restored execution: for every adversary with at most `Q` queries,
the probability that the selected input is admissible, the output read at the completed transcript
is valid and extraction fails is at most `(Q + rounds.length) * error`. -/
theorem restoredExecution_knowledge_soundness [DecidableEq (Key S Salt rounds)]
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput)
    (error : ENNReal) (bounded : F.LocallyBounded (uniformDraw rounds) (uniformEps rounds error))
    (readOut : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) → W → Wout stmt tr)
    (adversary : OracleComp (oracleSpec S Salt rounds) (S × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (restoredExecution rounds adversary)).run' ∅}[
      admissible result.1 ∧
        validOutput result.1 result.2.1 (readOut result.1 result.2.1 result.2.2) ∧
        ¬ relIn result.1
          (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2))] ≤
      (Q + rounds.length) * error := by
  rw [← Nat.cast_add]
  exact prEvent_randomOracle_le_of_bad_queries _ (Q + rounds.length)
    (restoredExecution_queryBound rounds adversary Q queryBound) _ (badKey F) error
    (badKey_resample_bound bounded) (restored_bad_trace F readOut adversary)

end Knowledge

/-! ### Knowledge soundness of the verification games -/

section Games

variable {rounds : List Round} {I S Salt W : Type} {A : I → Type}
  {T : Path (protocol rounds) → Type} {J : Path (protocol rounds) → Type}
  {B : (p : Path (protocol rounds)) → J p → Type}
  {Win : S × (∀ i, A i) → Type uW}
  {inputs : OracleFamily.{0, 0, wI} I A}
  {outputs : (p : Path (protocol rounds)) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {admissible : S × (∀ i, A i) → Prop} {relIn : (stmt : S × (∀ i, A i)) → Win stmt → Prop}
  {Wout : (S × (∀ i, A i)) → PathAlong oracleSig (protocol rounds) → Type uO}
  {validOutput : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) →
    Wout stmt tr → Prop}

/-- State-restoration knowledge soundness of a verifier. The knowledge state function's output
witnesses are indexed by the transcript, and `readOut` reads the adversary's witness at the
completed transcript. The output relation may read the transcript; every accepted statement it
relates to a witness is a valid output of the knowledge state function at the read witness. For
every adversary with at most `Q` queries, the probability that the selected input is admissible,
the verifier accepts a statement related to the output witness, and backward extraction fails, is
at most `(Q + rounds.length) * error`. -/
theorem stateRestoration_knowledge_soundness [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : PathAlong oracleSig (protocol rounds)) →
      T (projectPathAlong oracleSig _ tr) → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
    (S × (∀ i, A i)) Wout Win admissible
      relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr t w, terminalObservation V stmt tr = some t → relOut stmt tr t w →
      validOutput stmt tr (readOut stmt tr w))
    (error : ENNReal) (bounded : F.LocallyBounded (uniformDraw rounds) (uniformEps rounds error))
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (verificationGame V adversary)).run' ∅}[
      admissible result.1 ∧
      (∃ t, result.2.2.1 = some t ∧ relOut result.1 result.2.1 t result.2.2.2) ∧
      ¬ relIn result.1
        (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      (Q + rounds.length) * error := by
  rw [verificationGame_eq, simulateQ_map, StateT.run'_map', prEvent_map]
  refine le_trans (prEvent_mono _ _ _ ?_)
    (restoredExecution_knowledge_soundness F error bounded readOut adversary Q queryBound)
  rintro ⟨stmt, tr, w⟩ ⟨hadm, ⟨t, ht, hrel⟩, hfail⟩
  exact ⟨hadm, outputLaw stmt tr t w ht hrel, hfail⟩

/-- State-restoration knowledge soundness with the accepted statement's output oracle data. The
output relation reads the closed claim: the accepted statement together with the data of its
output oracles, computed from the same transcript. -/
theorem stateRestoration_oracle_knowledge_soundness
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : PathAlong oracleSig (protocol rounds)) →
      OracleVerifier.Output T B (projectPathAlong oracleSig _ tr) → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
    (S × (∀ i, A i)) Wout Win admissible
      relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr claim w, closedTerminalObservation V stmt tr = some claim →
      relOut stmt tr claim w → validOutput stmt tr (readOut stmt tr w))
    (error : ENNReal) (bounded : F.LocallyBounded (uniformDraw rounds) (uniformEps rounds error))
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame V adversary)).run' ∅}[
      admissible result.1 ∧
      (∃ claim, result.2.2.1 = some claim ∧ relOut result.1 result.2.1 claim result.2.2.2) ∧
      ¬ relIn result.1
        (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      (Q + rounds.length) * error := by
  rw [closedVerificationGame_eq, simulateQ_map, StateT.run'_map', prEvent_map]
  refine le_trans (prEvent_mono _ _ _ ?_)
    (restoredExecution_knowledge_soundness F error bounded readOut adversary Q queryBound)
  rintro ⟨stmt, tr, w⟩ ⟨hadm, ⟨claim, hc, hrel⟩, hfail⟩
  exact ⟨hadm, outputLaw stmt tr claim w hc hrel, hfail⟩

/-- State-restoration knowledge soundness averaged over the adversary's private coins, which may
fail. Every fixed-coin adversary has the same query bound and may adapt to all oracle answers. -/
theorem stateRestoration_knowledge_soundness_privateCoins
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : PathAlong oracleSig (protocol rounds)) →
      T (projectPathAlong oracleSig _ tr) → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
    (S × (∀ i, A i)) Wout Win admissible
      relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr t w, terminalObservation V stmt tr = some t → relOut stmt tr t w →
      validOutput stmt tr (readOut stmt tr w))
    (error : ENNReal) (bounded : F.LocallyBounded (uniformDraw rounds) (uniformEps rounds error))
    {Coins : Type} (coins : OptionT ProbComp Coins)
    (adversary : Coins → OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : ∀ c, IsTotalQueryBound (adversary c) Q) :
    Pr{let result ← (coins >>= fun c => OptionT.lift
        ((simulateQ randomOracle (verificationGame V (adversary c))).run' ∅))}[
      admissible result.1 ∧
      (∃ t, result.2.2.1 = some t ∧ relOut result.1 result.2.1 t result.2.2.2) ∧
      ¬ relIn result.1
        (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      (Q + rounds.length) * error := by
  apply prEvent_bind_le_of_forall_le
  intro c
  rw [OptionT.prEvent_lift]
  exact stateRestoration_knowledge_soundness V relOut F readOut outputLaw error bounded
    (adversary c) Q (queryBound c)

/-- The private-coins form of `stateRestoration_oracle_knowledge_soundness`. Coin failure
contributes missing mass. -/
theorem stateRestoration_oracle_knowledge_soundness_privateCoins
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : PathAlong oracleSig (protocol rounds)) →
      OracleVerifier.Output T B (projectPathAlong oracleSig _ tr) → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
    (S × (∀ i, A i)) Wout Win admissible
      relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr claim w, closedTerminalObservation V stmt tr = some claim →
      relOut stmt tr claim w → validOutput stmt tr (readOut stmt tr w))
    (error : ENNReal) (bounded : F.LocallyBounded (uniformDraw rounds) (uniformEps rounds error))
    {Coins : Type} (coins : OptionT ProbComp Coins)
    (adversary : Coins → OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : ∀ c, IsTotalQueryBound (adversary c) Q) :
    Pr{let result ← (coins >>= fun c => OptionT.lift
        ((simulateQ randomOracle (closedVerificationGame V (adversary c))).run' ∅))}[
      admissible result.1 ∧
      (∃ claim, result.2.2.1 = some claim ∧ relOut result.1 result.2.1 claim result.2.2.2) ∧
      ¬ relIn result.1
        (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      (Q + rounds.length) * error := by
  apply prEvent_bind_le_of_forall_le
  intro c
  rw [OptionT.prEvent_lift]
  exact stateRestoration_oracle_knowledge_soundness V relOut F readOut outputLaw error
    bounded (adversary c) Q (queryBound c)

end Games

end Interaction.Core.StateRestoration
