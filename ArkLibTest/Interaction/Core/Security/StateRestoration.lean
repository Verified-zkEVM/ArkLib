/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.StateRestoration
import ArkLibTest.Interaction.Core.Oracle
import ArkLibTest.Interaction.Core.Support

/-! A one-round state-restoration client: the prover sends an oracle in `Fin 8`, the verifier draws
a `Bool`. On challenge `true` the verifier reads the sent payload and returns it as the claim, with
the payload as its output oracle; on `false` it rejects. The input domain is `Nat`. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec
open Interaction.Core.StateRestoration
open Interaction.Core.OracleTests (emptyFamily)

namespace Interaction.Core.StateRestorationTests

/-- A sent `Fin 8` answers its single query with itself. -/
@[instance_reducible] def messageInterface : OracleInterface (Fin 8) where
  Query := Unit
  toOC := { spec := fun _ => Fin 8, impl := fun _ => do return (← read) }

/-- One round: a `Fin 8` oracle message, then a uniform `Bool` challenge. -/
def round : Round where
  Message := Fin 8
  Challenge := Bool
  interface := messageInterface
  sampleChallenge := inferInstance

/-- The protocol has the single round `round`. -/
def rounds : List Round := [round]

/-- The output is one `Fin 8` oracle. -/
@[instance_reducible] def outputFamily : OracleFamily PUnit (fun _ => Fin 8) :=
  singletonFamily messageInterface

/-- The input statement: a number with no input oracles. -/
abbrev Stmt : Type := Nat × (∀ i : PEmpty.{1}, (PEmpty.elim i : Type))

/-- The statement `z` with no input oracles. -/
def stmt (z : Nat) : Stmt := (z, fun i => PEmpty.elim i)

/-- Statements are equal when their numbers are; there are no input oracles. -/
instance : DecidableEq Stmt := fun a b =>
  decidable_of_iff (a.1 = b.1) ⟨fun h => Prod.ext h (funext fun i => i.elim), congrArg Prod.fst⟩

/-- Keys have decidable equality: a key is a first-round triple, and no later round exists. -/
instance : DecidableEq (Key Stmt Unit rounds) :=
  inferInstanceAs (DecidableEq ((Stmt × Fin 8 × Unit) ⊕ (Fin 8 × Unit × Empty)))

/-- On challenge `true` read the payload and return it, on `false` reject. The output oracle is
the sent payload. -/
def verifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ (protocol rounds) Nat (fun _ => Fin 8)
    emptyFamily
    (fun _ => outputFamily) where
  decide _ p v := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact if (show Bool from v.1.2.1) then
      liftM (([]ₒ + (pathResources emptyFamily (protocol rounds) ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩).spec).query
    (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
    else failure
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact (OracleMap.embedding (pathFamily (protocol rounds)
      ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩) (fun _ => .inl ⟨⟩)).comp (OracleMap.snd _ _)

/-- The transcript with message `m` and challenge `c`. -/
def path (m : Fin 8) (c : Bool) : PathAlong oracleSig (protocol rounds) := ⟨m, ⟨c, ⟨⟩⟩⟩

/-- The selected message 7 with salt `()`. -/
def messages : Messages Unit rounds := ⟨(7 : Fin 8), (), PUnit.unit⟩

/-- The adversary selects input 0, message 7, salt `()` and witness 6 without querying. -/
def adversary : OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat) :=
  pure ⟨stmt 0, messages, 6⟩

/-- The single first-round key of the adversary's selection. -/
def key : Key Stmt Unit rounds := Key.here (stmt 0) (7 : Fin 8) ()

-- Row 7 (StateRestoration L150, uniformVerifier_fresh): the game's challenge draw at a key's
-- receiver prefix is the uniform sample of that round's alphabet.
example : sampleAt oracleSig (uniformDraw rounds) (keySpine key) rfl = ($ᵗ Bool) :=
  sampleAt_keySpine key

-- Row 13 (StateRestoration L215, oracleObservation_true).
/-- On `true` the closed observation returns the message as the claim and as its output oracle. -/
theorem oracleObservation_true (z : Nat) (m : Fin 8) :
    closedTerminalObservation verifier (stmt z) (path m true) = some (m, fun _ => m) := rfl

-- Row 14 (StateRestoration L219, oracleObservation_false).
/-- On `false` the closed observation is `none`. -/
theorem oracleObservation_false (z : Nat) (m : Fin 8) :
    closedTerminalObservation verifier (stmt z) (path m false) = none := rfl

-- Row 17 (StateRestoration L258): the `false` branch returns no claim in the fixed `Option`
-- output, so no output relation can hold there.
example (z : Nat) (m : Fin 8) (rel : Fin 8 × (PUnit.{1} → Fin 8) → Prop) :
    ¬ ∃ claim, closedTerminalObservation verifier (stmt z) (path m false) = some claim ∧
      rel claim := by
  rw [oracleObservation_false]
  simp

/-- Against any answer table, the game completes the adversary's selection with the table's
challenge, and the verifier decides on that path. This checks completion; `scriptedRun_eq` below
runs the parties. -/
theorem game_eval (table : Table Stmt Unit rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (closedVerificationGame verifier adversary) =
      ⟨stmt 0, path 7 (table key), closedTerminalObservation verifier (stmt 0) (path 7 (table key)),
        6⟩ := by
  rfl

/-- The game's output against the constant table `c`, as plain numbers. -/
def gameResult (c : Bool) : Nat × Bool × Option (Nat × Nat) × Nat :=
  let table : Table Stmt Unit rounds
    | .inl _ => c
    | .inr (_, _, key) => key.elim
  let r := evalWithAnswerFn (QueryImpl.ofFn table) (closedVerificationGame verifier adversary)
  (r.1.1, r.2.1.2.1, r.2.2.1.map (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat))), r.2.2.2)

-- The game on challenge `true`, a completion check beside row 10.
/-- info: (0, true, some (7, 7), 6) -/
#guard_msgs in
#eval gameResult true

-- The game on challenge `false`, a completion check beside row 11.
/-- info: (0, false, none, 6) -/
#guard_msgs in
#eval gameResult false

/-! ### Running the parties

The scripted prover sends the selected message through `OracleVerifier.run`; each challenge query
is answered from the recorded transcript. -/

/-- On every challenge `c`, running the scripted prover of the selection with the verifier, the
challenge read from `path 7 c`, returns that transcript and the closed observation on it. -/
theorem scriptedRun_eq (c : Bool) :
    evalWithAnswerFn (recordedAnswers rounds (path 7 c))
      (verifier.run 0 (stmt 0).2 (scriptedProver rounds messages)) =
      ⟨path 7 c, ⟨⟩, closedTerminalObservation verifier (stmt 0) (path 7 c)⟩ :=
  run_scriptedProver verifier (stmt 0) messages (path 7 c) ⟨rfl, trivial⟩

/-- The sent message, the challenge and the closed claim of the run on challenge `c`, as plain
numbers. -/
def constantOracleReplayResult (c : Bool) : Nat × Bool × Option (Nat × Nat) :=
  let r := evalWithAnswerFn (recordedAnswers rounds (path 7 c))
    (verifier.run 0 (stmt 0).2 (scriptedProver rounds messages))
  ((show Fin 8 from r.1.1 : Nat), (show Bool from r.1.2.1),
    r.2.2.map (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat))))

-- The rejecting oracle verifier is a separate replay from the plain terminal.
/-- On every challenge the run sends message 7 and records the challenge; it returns claim 7 with
output oracle 7 on `true` and rejects on `false`. -/
theorem constantOracleReplayResult_eq (c : Bool) :
    constantOracleReplayResult c = (7, c, if c then some (7, 7) else none) := by
  unfold constantOracleReplayResult
  rw [scriptedRun_eq]
  cases c <;> rfl

-- The oracle verifier accepts on the true challenge.
/-- info: (7, true, some (7, 7)) -/
#guard_msgs in
#eval constantOracleReplayResult true

-- The oracle verifier rejects on the false challenge.
/-- info: (7, false, none) -/
#guard_msgs in
#eval constantOracleReplayResult false

/-- The plain terminal always reads and returns the sent payload, on either challenge. -/
def constantPlainVerifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ (protocol rounds) Nat (fun
    _ => Fin 8) emptyFamily
    (fun _ => outputFamily) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact liftM (([]ₒ + (pathResources emptyFamily (protocol rounds) ⟨⟨⟩, ⟨⟨⟩,
    ⟨⟩⟩⟩).spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
  outputMap := verifier.outputMap

/-- Replaying the plain terminal returns its payload for every challenge. -/
theorem constantPlainScriptedRun_eq (c : Bool) :
    evalWithAnswerFn (recordedAnswers rounds (path 7 c))
      (constantPlainVerifier.run 0 (stmt 0).2 (scriptedProver rounds messages)) =
      ⟨path 7 c, ⟨⟩, some (7, fun _ => 7)⟩ := by
  exact (run_scriptedProver constantPlainVerifier (stmt 0) messages (path 7 c) ⟨rfl,
    trivial⟩).trans rfl

/-- The message, challenge and returned payload of the plain replay. The replay equation
certifies that the returned verdict contains a payload on both challenges. -/
def constantReplayResult (c : Bool) : OracleComp []ₒ (Nat × Bool × Nat) :=
  let r := evalWithAnswerFn (recordedAnswers rounds (path 7 c))
    (constantPlainVerifier.run 0 (stmt 0).2 (scriptedProver rounds messages))
  have accepted : r.2.2.isSome := by
    dsimp only [r]
    rw [constantPlainScriptedRun_eq]
    trivial
  pure ((show Fin 8 from r.1.1).val, (show Bool from r.1.2.1), (r.2.2.get accepted).1.val)

-- Row 9 (StateRestoration L175): the plain replay returns its payload on both challenges.
/-- Both challenges return the selected message and payload 7. -/
theorem constantReplayResult_eq (c : Bool) : constantReplayResult c = pure (7, c, 7) := by
  unfold constantReplayResult
  simp only [constantPlainScriptedRun_eq]
  rfl

-- Row 10 (StateRestoration L182): the plain replay on true.
/-- info: (7, true, 7) -/
#guard_msgs in
#eval evalWithAnswerFn (fun q : PEmpty.{1} => q.elim) (constantReplayResult true)

-- Row 11 (StateRestoration L183): the plain replay on false.
/-- info: (7, false, 7) -/
#guard_msgs in
#eval evalWithAnswerFn (fun q : PEmpty.{1} => q.elim) (constantReplayResult false)

/-- Against every answer table, the run with the challenge of the game's transcript returns the
game's transcript and observation: the game's challenge is the table's answer at `key`. -/
theorem gameRun_eq (table : Table Stmt Unit rounds) :
    evalWithAnswerFn (recordedAnswers rounds (path 7 (table key)))
      (verifier.run 0 (stmt 0).2 (scriptedProver rounds messages)) =
      ⟨path 7 (table key), ⟨⟩,
        closedTerminalObservation verifier (stmt 0) (path 7 (table key))⟩ := by
  exact closedVerificationGame_eval_run verifier adversary table

-- Row 18 (StateRestoration L264): the closed observation on the `true` branch.
/-- info: some (7, 7) -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (path 7 true)).map
  (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat)))

-- Row 19 (StateRestoration L266): the closed observation on the `false` branch.
/-- info: none -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (path 7 false)).map
  (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat)))

/-- The adversary's private coin selects one of two selections. -/
def coinAdversary (coin : Bool) :
    OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat) :=
  if coin then adversary else pure ⟨stmt 0, ⟨(3 : Fin 8), (), PUnit.unit⟩, 2⟩

-- Row 21 (StateRestoration L291): coins that fail give the game probability 0.
example : Pr{let _result ← ((failure : OptionT ProbComp Bool) >>= fun coin => OptionT.lift
    ((simulateQ randomOracle (closedVerificationGame verifier (coinAdversary coin))).run' ∅))}[
      True] = 0 := by
  simp [failure_bind]

/-! ### The knowledge state function -/

/-- The input relation: the witness is at most the input number. -/
def Rin (z : Stmt) (w : Nat) : Prop := w ≤ z.1

/-- A valid output: the challenge is `true` and the witness is at most the sent message. -/
def valid (_ : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) : Prop :=
  (show Bool from tr.2.1) = true ∧ w ≤ (show Fin 8 from tr.1).val

/-- Before any move a witness is at most the input; after the message no witness is known; after
the challenge `c` a witness is known when `c` is `true` and it is at most the message. Extraction
adds the message at the message step and copies the witness otherwise. -/
def knowledge : KnowledgeStateFunction oracleSig (protocol rounds) Stmt
    (fun _ _ => Nat) (fun _ => Nat) (fun _ => True) Rin valid where
  Witness _ {_} _ _ := Nat
  toFun z {_} sp history w := match sp, history with
    | .root _, _ => w ≤ z.1
    | .down _ (.root _), _ => False
    | .down _ (.down _ _), history =>
      (show Bool from history.2.1.1) = true ∧ w ≤ (show Fin 8 from history.1.1).val
  extractRoot _ w := w
  extractStep _ {_ _} sp _ x w := by
    cases sp with
    | root => exact w + (show Fin 8 from x).val
    | down _ tail =>
      cases tail with
      | root => exact w
      | down _ tail => cases tail
  extractLeaf _ _ _ w := w
  root _ _ _ h := h
  send sp _ _ h x w hw := by
    cases sp with
    | root => exact hw.elim
    | down _ tail =>
      cases tail with
      | root => cases h
      | down _ tail => cases tail
  leaf sp history _ _ hvalid := by
    cases sp with
    | down _ tail =>
      cases tail with
      | down _ tail =>
        cases tail
        rcases history with ⟨⟨m, ⟨⟩⟩, ⟨⟨c, ⟨⟩⟩, ⟨⟩⟩⟩
        exact hvalid

-- Row 1 (StateRestoration L87, inputLaw).
/-- The root state is the input relation. -/
theorem inputLaw (z : Stmt) (w : Nat) : knowledge.toFun z (.root _) ⟨⟩ w ↔ Rin z w := Iff.rfl

-- Row 2 (StateRestoration L89, outputLaw).
/-- The terminal state on the terminal witness is the valid-output relation, on every transcript. -/
theorem outputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    knowledge.toFun z (completeSpine oracleSig tr) (completeMoves oracleSig tr)
      (knowledge.terminalWitness z tr w) ↔ valid z tr w := by
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  rfl

-- Row 3 (StateRestoration L96, preserving).
/-- The send law at the message, the only prover move. No witness is known after the message, so
preservation is vacuous there. -/
theorem preserving (z : Stmt) (m : Fin 8) (w : Nat) :
    ¬ knowledge.toFun z (.down ⟨⟩ (.root _)) ⟨⟨m, rfl⟩, ⟨⟩⟩ w := id

/-- The receiver cursor at the challenge, below message `m`. -/
abbrev challengeSpine : Cursor.Spine (protocol rounds)
    (.liftBind (OraclePos.challenge Bool) (fun _ => protocol [])) :=
  .down ⟨⟩ (.root _)

-- Row 4 (StateRestoration L105, badChallenge_iff).
/-- Below every message the bad challenges are exactly `true`. -/
theorem badChallenge_iff (z : Stmt) (m : Fin 8) (c : Bool) :
    c ∈ knowledge.badChallenge challengeSpine ⟨⟨m, rfl⟩, ⟨⟩⟩ z ↔ c = true := by
  constructor
  · rintro ⟨_, _, known, _⟩
    exact known
  · intro isTrue
    exact ⟨(0 : Nat), id, isTrue, Nat.zero_le _⟩

/-- The uniform `Bool` is `true` with probability `1/2`. -/
theorem uniform_true : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 1 / 2 := by
  rw [SampleableType.evalDist_uniformSample_singleton, one_div]
  simp

-- Row 5 (StateRestoration L113, bounded).
/-- The state function is locally bounded by `1/2` at the uniform draw, hence round-by-round
knowledge sound. -/
theorem bounded : knowledge.LocallyBounded (uniformDraw rounds) (uniformEps rounds (1 / 2)) := by
  intro z _ a next sp h history
  cases sp with
  | root => cases h
  | down _ tail =>
    cases tail with
    | root =>
      rcases history with ⟨⟨m, ⟨⟩⟩, ⟨⟩⟩
      have hset : knowledge.badChallenge challengeSpine ⟨⟨m, rfl⟩, ⟨⟩⟩ z = {true} :=
        Set.ext fun c => badChallenge_iff z m c
      have hsample : sampleAt oracleSig (uniformDraw rounds) challengeSpine rfl = ($ᵗ Bool) :=
        sampleAt_keySpine (Key.here (Salt := Unit) z m ())
      have half : (letI : MeasurableSpace (Move oracleSig (OraclePos.challenge Bool)) := ⊤
          𝒟[sampleAt oracleSig (uniformDraw rounds) challengeSpine rfl]
            (knowledge.badChallenge challengeSpine ⟨⟨m, rfl⟩, ⟨⟩⟩ z)) = 1 / 2 := by
        simp only
        rw [hsample, hset]
        exact uniform_true
      exact half.le
    | down _ tail => cases tail

example : rbrKnowledgeSoundness.{0, 0, 0} oracleSig (protocol rounds) (fun _ => True) Rin valid
    (uniformDraw rounds) (uniformEps rounds (1 / 2)) :=
  ⟨knowledge, bounded⟩

-- Row 6 (StateRestoration L146): extraction along the path from output witness 6 is `6 + 7`.
example (c : Bool) : knowledge.extractAlong (stmt 0) (path 7 c) 6 = 13 := rfl

-- Row 12 (StateRestoration L184): the extracted input witness.
/-- info: 13 -/
#guard_msgs in
#eval knowledge.extractAlong (stmt 0) (path 7 true) 6

-- The bad-key lemma on the adversary's selection: extraction fails on the `true` branch from
-- input 0, and the bad key is the selection's first-round key.
example (table : Table Stmt Unit rounds) (htrue : table key = true) :
    ∃ k ∈ completionKeys rounds (stmt 0) messages,
      BadChallengeOnCompletion knowledge (stmt 0) messages table 6 k := by
  apply exists_badChallenge_of_extraction_failure knowledge (stmt 0) messages table 6
  · exact ⟨htrue, show 6 ≤ 7 by omega⟩
  · change ¬ (6 + 7 ≤ 0)
    omega

/-- The plain output relation: the witness is at most the accepted statement. -/
def Rout (_ : Stmt) (_ : PathAlong oracleSig (protocol rounds)) (t : Fin 8) (w : Nat) : Prop :=
  w ≤ t.val

/-- An accepted statement related to the witness is a valid output. -/
theorem plainOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (t : Fin 8)
    (w : Nat) (accepted : terminalObservation verifier z tr = some t) (related : Rout z tr t w) :
    valid z tr w := by
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  cases c
  · cases accepted
  · cases accepted
    exact ⟨rfl, related⟩

-- Row 8 (StateRestoration L156, actual_game_bound).
/-- The plain game has knowledge error at most `1/2` for an adversary without queries. -/
theorem actual_game_bound :
    Pr{let result ← (simulateQ randomOracle (verificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ t, result.2.2.1 = some t ∧ Rout result.1 result.2.1 t result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_knowledge_soundness verifier Rout knowledge (fun _ _ w => w)
    plainOutputLaw (1 / 2) bounded adversary 0 trivial
  simpa [rounds] using general

/-- The oracle output relation: the witness is at most the output oracle's data. -/
def oracleRout (_ : Stmt) (_ : PathAlong oracleSig (protocol rounds))
    (claim : Fin 8 × (PUnit.{1} → Fin 8)) (w : Nat) : Prop :=
  w ≤ (claim.2 ⟨⟩).val

-- Row 15 (StateRestoration L223, oracleOutputLaw).
/-- The terminal state on the terminal witness is an accepted closed claim related to the
witness. -/
theorem oracleOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    knowledge.toFun z (completeSpine oracleSig tr) (completeMoves oracleSig tr)
      (knowledge.terminalWitness z tr w) ↔
      ∃ claim, closedTerminalObservation verifier z tr = some claim ∧ oracleRout z tr claim w := by
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  cases c
  · change (false = true ∧ _) ↔ ∃ claim, none = some claim ∧ _
    simp
  · change (true = true ∧ w ≤ m.val) ↔ ∃ claim, some (m, fun _ => m) = some claim ∧ _
    simp [oracleRout]

/-- An accepted closed claim related to the witness is a valid output. -/
theorem closedOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (claim : Fin 8 × (PUnit.{1} → Fin 8)) (w : Nat)
    (accepted : closedTerminalObservation verifier z tr = some claim)
    (related : oracleRout z tr claim w) : valid z tr w :=
  (outputLaw z tr w).mp ((oracleOutputLaw z tr w).mpr ⟨claim, accepted, related⟩)

-- Row 16 (StateRestoration L245, actual_oracle_game_bound).
/-- The closed game has knowledge error at most `1/2`. -/
theorem actual_oracle_game_bound :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ claim, result.2.2.1 = some claim ∧ oracleRout result.1 result.2.1 claim
        result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_oracle_knowledge_soundness verifier oracleRout knowledge
    (fun _ _ w => w) closedOutputLaw (1 / 2) bounded adversary 0 trivial
  simpa [rounds] using general

-- Row 20 (StateRestoration L274, actual_coin_oracle_game_bound).
/-- The same bound with uniform private coins choosing between two adversaries. -/
theorem actual_coin_oracle_game_bound :
    Pr{let result ← ((OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool) >>= fun coin =>
      OptionT.lift ((simulateQ randomOracle
        (closedVerificationGame verifier (coinAdversary coin))).run' ∅))}[
      True ∧ (∃ claim, result.2.2.1 = some claim ∧ oracleRout result.1 result.2.1 claim
        result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_oracle_knowledge_soundness_privateCoins verifier oracleRout
    knowledge (fun _ _ w => w) closedOutputLaw (1 / 2) bounded
    (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool) coinAdversary 0
    (fun coin => by cases coin <;> trivial)
  simpa [rounds] using general

-- The plain private-coins form.
example :
    Pr{let result ← ((OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool) >>= fun coin =>
      OptionT.lift ((simulateQ randomOracle
        (verificationGame verifier (coinAdversary coin))).run' ∅))}[
      True ∧ (∃ t, result.2.2.1 = some t ∧ Rout result.1 result.2.1 t result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_knowledge_soundness_privateCoins verifier Rout knowledge
    (fun _ _ w => w) plainOutputLaw (1 / 2) bounded (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool)
    coinAdversary 0 (fun coin => by cases coin <;> trivial)
  simpa [rounds] using general

/-! ### A transcript-indexed output witness

The output witness of `knowledgeFin` has type `Fin (m + 1)` for the sent message `m`, so every
output witness is at most the message by its type. The adversary still outputs a number, and
`clampOut` reads it at the completed transcript. -/

/-- The output witness family: an index bounded by the sent message. -/
abbrev FinOut (tr : PathAlong oracleSig (protocol rounds)) : Type :=
  Fin ((show Fin 8 from tr.1).val + 1)

/-- A valid indexed output: the challenge is `true`. The bound is in the type. -/
def validFin (_ : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (_ : FinOut tr) : Prop :=
  (show Bool from tr.2.1) = true

/-- The state function `knowledge` with the indexed output witness; the leaf map forgets the
bound. -/
def knowledgeFin : KnowledgeStateFunction oracleSig (protocol rounds) Stmt
    (fun _ => FinOut) (fun _ => Nat) (fun _ => True) Rin validFin where
  Witness := knowledge.Witness
  toFun := knowledge.toFun
  extractRoot := knowledge.extractRoot
  extractStep := knowledge.extractStep
  extractLeaf _ _ _ w := w.val
  root := knowledge.root
  send := knowledge.send
  leaf sp history z w hvalid :=
    knowledge.leaf sp history z w.val ⟨hvalid, Nat.lt_succ_iff.mp w.isLt⟩

/-- `knowledgeFin` has the same bad challenges as `knowledge`, so the same local bound. -/
theorem boundedFin :
    knowledgeFin.LocallyBounded (uniformDraw rounds) (uniformEps rounds (1 / 2)) :=
  bounded

/-- Reads a number as an index bounded by the sent message, clamping it to the message. -/
def clampOut (_ : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (n : Nat) : FinOut tr :=
  ⟨min n (show Fin 8 from tr.1).val, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

-- Extraction along the path from the indexed output witness 6 below message 7 is `6 + 7`.
example (c : Bool) :
    knowledgeFin.extractAlong (stmt 0) (path 7 c) ⟨6, Nat.lt_succ_of_le (show 6 ≤ 7 by decide)⟩ =
      13 := rfl

-- The bad-key lemma with an output witness typed at the completed transcript.
example (table : Table Stmt Unit rounds) (htrue : table key = true) :
    ∃ k ∈ completionKeys rounds (stmt 0) messages,
      BadChallengeOnCompletion knowledgeFin (stmt 0) messages table
        ⟨6, Nat.lt_succ_of_le (show 6 ≤ 7 by decide)⟩ k := by
  apply exists_badChallenge_of_extraction_failure knowledgeFin (stmt 0) messages table
    ⟨6, Nat.lt_succ_of_le (show 6 ≤ 7 by decide)⟩ htrue
  change ¬ (6 + 7 ≤ 0)
  omega

/-- Every accepted statement related to a number is a valid indexed output of the clamped
number. -/
theorem finOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (t : Fin 8)
    (w : Nat) (accepted : terminalObservation verifier z tr = some t) (related : Rout z tr t w) :
    validFin z tr (clampOut z tr w) :=
  (plainOutputLaw z tr t w accepted related).1

-- The plain game bound with the indexed output witness, read from the adversary's number.
example :
    Pr{let result ← (simulateQ randomOracle (verificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ t, result.2.2.1 = some t ∧ Rout result.1 result.2.1 t result.2.2.2) ∧
      ¬ Rin result.1 (knowledgeFin.extractAlong result.1 result.2.1
        (clampOut result.1 result.2.1 result.2.2.2))] ≤ 1 / 2 := by
  have general := stateRestoration_knowledge_soundness verifier Rout knowledgeFin clampOut
    finOutputLaw (1 / 2) boundedFin adversary 0 trivial
  simpa [rounds] using general

/-! ### Statement-indexed witness carriers -/

/-- The witness includes an index bounded by the input statement. -/
abbrev IndexedWitness (z : Stmt) : Type := Nat × Fin (z.1 + 1)

/-- The indexed input relation bounds the numeric part of the witness. -/
def indexedRin (z : Stmt) (w : IndexedWitness z) : Prop := Rin z w.1

/-- The indexed output relation checks the same numeric witness on the completed transcript. -/
def indexedValid (z : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (w : IndexedWitness z) : Prop := valid z tr w.1

/-- Backward extraction retains the statement-indexed component through every cursor. -/
def indexedKnowledge : KnowledgeStateFunction oracleSig (protocol rounds) Stmt
    (fun z _ => IndexedWitness z) IndexedWitness (fun _ => True) indexedRin indexedValid where
  Witness z {_} _ _ := IndexedWitness z
  toFun z {_} sp history w := knowledge.toFun z sp history w.1
  extractRoot _ w := w
  extractStep z {_ _} sp history x w := (knowledge.extractStep z sp history x w.1, w.2)
  extractLeaf _ _ _ w := w
  root _ _ _ h := h
  send sp history z h x w hw := knowledge.send sp history z h x w.1 hw
  leaf sp history z w hv := knowledge.leaf sp history z w.1 hv

/-- The statement-indexed state function has the same bad-challenge events. -/
theorem indexedBadChallenge_eq (z : Stmt) {a : OraclePos}
    {next : OraclePoly.B a → OracleProtocol}
    (sp : Cursor.Spine (protocol rounds) (.liftBind a next))
    (history : PrefixMoves oracleSig sp) :
    indexedKnowledge.badChallenge sp history z = knowledge.badChallenge sp history z := by
  ext x
  constructor
  · rintro ⟨w, hbefore, hafter⟩
    exact ⟨w.1, hbefore, hafter⟩
  · rintro ⟨w, hbefore, hafter⟩
    exact ⟨(w, ⟨0, Nat.zero_lt_succ _⟩), hbefore, hafter⟩

/-- Statement-indexed extraction has the same uniform local error. -/
theorem indexedBounded :
    indexedKnowledge.LocallyBounded (uniformDraw rounds) (uniformEps rounds (1 / 2)) := by
  intro z hz a next sp h history
  simpa only [indexedBadChallenge_eq] using bounded z hz a next sp h history

/-- Reading the adversary's number retains a well-typed statement index. -/
def indexedReadOut (z : Stmt) (_ : PathAlong oracleSig (protocol rounds))
    (w : Nat) : IndexedWitness z := (w, ⟨0, Nat.zero_lt_succ _⟩)

/-- The accepted observation provides a valid statement-indexed output witness. -/
theorem indexedOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (t : Fin 8)
    (w : Nat) (accepted : terminalObservation verifier z tr = some t) (related : Rout z tr t w) :
    indexedValid z tr (indexedReadOut z tr w) := plainOutputLaw z tr t w accepted related

/-- The restoration bound returns witnesses in the selected statement's own carrier. -/
theorem indexed_game_bound :
    Pr{let result ← (simulateQ randomOracle (verificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ t, result.2.2.1 = some t ∧ Rout result.1 result.2.1 t result.2.2.2) ∧
      ¬ indexedRin result.1 (indexedKnowledge.extractAlong result.1 result.2.1
        (indexedReadOut result.1 result.2.1 result.2.2.2))] ≤ 1 / 2 := by
  have general := stateRestoration_knowledge_soundness verifier Rout indexedKnowledge
    indexedReadOut indexedOutputLaw (1 / 2) indexedBounded adversary 0 trivial
  simpa [rounds] using general

/-- Indexed extraction preserves the input-dependent index while adding the message. -/
example (z : Stmt) (c : Bool) (i : Fin (z.1 + 1)) :
    indexedKnowledge.extractAlong z (path 7 c) (6, i) = (13, i) := rfl

/-- Keyed failure localization keeps the supplied witness at a larger certificate universe. -/
example (table : Table Stmt Unit rounds) (htrue : table key = true) :
    ∃ k ∈ completionKeys rounds (stmt 0) messages,
      BadChallengeOnCompletion (knowledge.lift.{0, 0, 0, 1}) (stmt 0) messages table 6 k := by
  apply exists_badChallenge_of_extraction_failure (knowledge.lift.{0, 0, 0, 1})
    (stmt 0) messages table 6
  · exact ⟨htrue, show 6 ≤ 7 by omega⟩
  · change ¬ (6 + 7 ≤ 0)
    omega

/-! ### Public selection of dependent output carriers -/

/-- An authored Boolean selects the output carrier before the original oracle round. -/
abbrev selectedProtocol : OracleProtocol :=
  .liftBind (.message Bool) fun _ => protocol rounds

/-- The selected finite carrier has eight or nine elements. -/
def SelectedValue : Bool → Type
  | true => Fin 8
  | false => Fin 9

/-- The output carrier depends on the authored message in the shape path. -/
abbrev SelectedOutput (p : Path selectedProtocol) : Type := SelectedValue p.1

/-- Read the numerical value without changing either selected carrier. -/
def selectedValue : (b : Bool) → SelectedValue b → Nat
  | true, x => x.val
  | false, x => x.val

/-- The same payload belongs to either finite carrier, as in the frozen terminal. -/
def selectedPayload : (b : Bool) → Fin 8 → SelectedValue b
  | true, x => x
  | false, x => ⟨x.val, Nat.lt_trans x.isLt (by decide : 8 < 9)⟩

/-- A payload in the nine-element carrier answers its unit query with itself. -/
@[instance_reducible] def wideInterface : OracleInterface (Fin 9) where
  Query := Unit
  toOC := { spec := fun _ => Fin 9, impl := fun _ => do return (← read) }

/-- The output oracle carrier and interface follow the authored Boolean too. -/
@[instance_reducible] def varyingFamily :
    (b : Bool) → OracleFamily PUnit (fun _ => SelectedValue b)
  | true => outputFamily
  | false => singletonFamily wideInterface

/-- The frozen output oracle always has its original eight-element carrier. -/
@[instance_reducible] def selectedFamily (_b : Bool) :
    OracleFamily PUnit.{1} (fun _ => Fin 8) := outputFamily

/-- Read the original payload and return it in the selected carrier. -/
def readSelected (b : Bool) (p : Path (protocol rounds)) :
    OptionT (OracleComp ([]ₒ + (pathResources emptyFamily (protocol rounds) p).spec))
      (SelectedValue b) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  exact do
    let m ← liftM (([]ₒ + (pathResources emptyFamily (protocol rounds)
      ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩).spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
    pure (selectedPayload b m)

/-- The selected output oracle answers from the actual sent payload. -/
def varyingMap (b : Bool) (p : Path (protocol rounds)) :
    OracleMap (pathResources emptyFamily (protocol rounds) p) (varyingFamily b) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  cases b
  · exact
      { f := fun x _ => selectedPayload false (x.2 (.inl ⟨⟩))
        impl := fun _ => do
          let m ← liftM ((pathResources emptyFamily (protocol rounds)
            ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩).spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
          pure (selectedPayload false m)
        law := fun _ _ => rfl }
  · exact (OracleMap.embedding (pathFamily (protocol rounds)
      ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩) (fun _ => .inl ⟨⟩)).comp (OracleMap.snd _ _)

/-- Frozen output-oracle data is routed unchanged from the sent payload. -/
def selectedMap (_b : Bool) (p : Path (protocol rounds)) :
    OracleMap (pathResources emptyFamily (protocol rounds) p) outputFamily := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  exact (OracleMap.embedding (pathFamily (protocol rounds)
    ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩) (fun _ => .inl ⟨⟩)).comp (OracleMap.snd _ _)

/-- The suffix of the plain terminal at a fixed authored selector. -/
def plainSuffixVerifier (b : Bool) : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ (protocol rounds) Nat
    (fun _ => SelectedValue b) emptyFamily (fun _ => selectedFamily b) where
  decide _ p _ := readSelected b p
  outputMap _ p _ := selectedMap b p

/-- The suffix of the rejecting terminal at a fixed authored selector. -/
def oracleSuffixVerifier (b : Bool) : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ (protocol rounds) Nat
    (fun _ => SelectedValue b) emptyFamily (fun _ => selectedFamily b) where
  decide _ p v := if (show Bool from v.1.2.1) then readSelected b p else failure
  outputMap _ p _ := selectedMap b p

/-- The plain terminal has an authored statement carrier and the original output oracle. -/
def plainVerifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ selectedProtocol Nat
    SelectedOutput emptyFamily
    (fun p => selectedFamily p.1) where
  decide _ p _ := readSelected p.1 p.2
  outputMap _ p _ := selectedMap p.1 p.2

/-- The oracle terminal rejects false challenges independently of the authored shape branch. -/
def selectedVerifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ selectedProtocol Nat
    SelectedOutput emptyFamily
    (fun p => selectedFamily p.1) where
  decide _ p v := if (show Bool from v.1.2.2.1) then readSelected p.1 p.2 else failure
  outputMap _ p _ := selectedMap p.1 p.2

/-- The full transcript retains both the authored selector and the independent challenge. -/
def selectedPath (b : Bool) (m : Fin 8) (c : Bool) : PathAlong oracleSig selectedProtocol :=
  ⟨b, path m c⟩

/-- The prover authors the selector and then sends the original selected message. -/
def selectedProver (b : Bool) : Prover oracleSig []ₒ selectedProtocol (fun _ => PUnit) :=
  pure ⟨b, scriptedProver rounds messages⟩

/-- Replay the recorded challenge after the authored selector. -/
def selectedAnswers (c : Bool) : QueryImpl ([]ₒ + challengeSpec oracleSig selectedProtocol) Id
  | .inl q => q.elim
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, n⟩, h⟩ => recordedChallenges rounds (path 7 c) ⟨n, h⟩

/-- Every selector and challenge returns the sent payload in its exact selected carrier. -/
theorem plainScriptedRun_eq (b c : Bool) :
    evalWithAnswerFn (selectedAnswers c) (plainVerifier.run 0 (stmt 0).2 (selectedProver b)) =
      ⟨selectedPath b 7 c, ⟨⟩, some (selectedPayload b 7, fun _ => (7 : Fin 8))⟩ := by
  cases b <;> cases c <;> kernel_rfl

/-- Replaying the rejecting terminal preserves its dependent claim on true and rejects false. -/
theorem selectedScriptedRun_eq (b c : Bool) :
    evalWithAnswerFn (selectedAnswers c) (selectedVerifier.run 0 (stmt 0).2 (selectedProver b)) =
      ⟨selectedPath b 7 c, ⟨⟩,
        if c then some (selectedPayload b 7, fun _ => (7 : Fin 8)) else none⟩ := by
  cases b <;> cases c <;> kernel_rfl

/-- The exact dependent result type of a selected party run. -/
abbrev SelectedRunResult := Observation oracleSig selectedProtocol (fun _ => PUnit.{1})
  (OracleVerifier.Output SelectedOutput (fun _ (_ : PUnit.{1}) => Fin 8))

/-- The plain replay keeps the frozen payload and challenge values, with a real dependent output. -/
def replayResult (b c : Bool) : OracleComp []ₒ (Nat × Bool × Nat) :=
  let r : SelectedRunResult := evalWithAnswerFn (selectedAnswers c)
    (plainVerifier.run 0 (stmt 0).2 (selectedProver b))
  have accepted : r.2.2.isSome := by
    dsimp only [r]
    erw [plainScriptedRun_eq]
    trivial
  pure ((show Fin 8 from r.1.2.1).val, (show Bool from r.1.2.2.1),
    selectedValue r.1.1 (r.2.2.get accepted).1)

/-- Both independently selected carriers return payload seven on both challenges. -/
theorem replayResult_eq (b c : Bool) : replayResult b c = pure (7, c, 7) := by
  unfold replayResult
  simp only [plainScriptedRun_eq]
  cases b <;> rfl

/-- Decode an already computed dependent run, reading its actual returned oracle payload. -/
def selectedRunSummary (r : SelectedRunResult) : Nat × Bool × Option (Nat × Nat) :=
  ((show Fin 8 from r.1.2.1).val, (show Bool from r.1.2.2.1),
    r.2.2.map (fun claim => (selectedValue r.1.1 claim.1, (claim.2 ⟨⟩).val)))

/-- The rejecting replay observes the same numerical statement and output-oracle payload. -/
def oracleReplayResult (b c : Bool) : Nat × Bool × Option (Nat × Nat) :=
  selectedRunSummary (evalWithAnswerFn (selectedAnswers c)
    (selectedVerifier.run 0 (stmt 0).2 (selectedProver b)))

/-- Rejection depends on the challenge while carrier selection remains prover-authored. -/
theorem oracleReplayResult_eq (b c : Bool) :
    oracleReplayResult b c = (7, c, if c then some (7, 7) else none) := by
  unfold oracleReplayResult
  erw [selectedScriptedRun_eq]
  cases b <;> cases c <;> rfl

/-- info: (7, true, 7) -/
#guard_msgs in
#eval evalWithAnswerFn (fun q : PEmpty.{1} => q.elim) (replayResult true true)

/-- info: (7, false, 7) -/
#guard_msgs in
#eval evalWithAnswerFn (fun q : PEmpty.{1} => q.elim) (replayResult false false)

/-- info: (7, true, some (7, 7)) -/
#guard_msgs in
#eval oracleReplayResult false true

/-- info: (7, false, none) -/
#guard_msgs in
#eval oracleReplayResult true false

/-- The selected suffix's accepted statement and output oracle data. -/
def selectedClaim (b : Bool) (m : Fin 8) : SelectedValue b × (PUnit.{1} → Fin 8) :=
  (selectedPayload b m, fun _ => m)

/-- The full selected observation and the suffix game use exactly the same accepted claim. -/
theorem selectedObservation (b c : Bool) (z : Stmt) (m : Fin 8) :
    closedTerminalObservation selectedVerifier z (selectedPath b m c) =
      if (show Bool from c) then some (selectedClaim b m) else none := by
  cases b <;> cases c <;> rfl

/-- Removing the authored prefix preserves the exact plain terminal observation. -/
theorem plainObservation_prepend (b : Bool) (z : Stmt)
    (tr : PathAlong oracleSig (protocol rounds)) :
    terminalObservation plainVerifier z ⟨b, tr⟩ =
      terminalObservation (plainSuffixVerifier b) z tr := by
  cases b <;> kernel_rfl

/-- Removing the authored prefix preserves the exact closed terminal observation. -/
theorem oracleObservation_prepend (b : Bool) (z : Stmt)
    (tr : PathAlong oracleSig (protocol rounds)) :
    closedTerminalObservation selectedVerifier z ⟨b, tr⟩ =
      closedTerminalObservation (oracleSuffixVerifier b) z tr := by
  cases b <;> kernel_rfl

/-- The closed relation reads the output oracle without encoding its selected carrier. -/
def selectedRelation (b : Bool) (_ : Stmt) (_ : PathAlong oracleSig (protocol rounds))
    (claim : SelectedValue b × (PUnit.{1} → Fin 8)) (w : Nat) : Prop :=
  w ≤ (claim.2 ⟨⟩).val

/-- The original terminal-state equivalence holds in both authored finite carriers. -/
theorem selectedOracleOutputLaw (b : Bool) (z : Stmt)
    (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    knowledge.toFun z (completeSpine oracleSig tr) (completeMoves oracleSig tr)
      (knowledge.terminalWitness z tr w) ↔
      ∃ claim, closedTerminalObservation (oracleSuffixVerifier b) z tr = some claim ∧
        selectedRelation b z tr claim w := by
  erw [outputLaw]
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  have obs : closedTerminalObservation (oracleSuffixVerifier b) z (path m c) =
      if (show Bool from c) then some (selectedClaim b m) else none := by
    cases b <;> cases c <;> rfl
  erw [obs]
  cases b <;> cases c <;>
    simp [valid, selectedRelation, selectedClaim, selectedPayload]

/-- An accepted selected claim satisfies the original terminal knowledge state. -/
theorem selectedOutputLaw (b : Bool) (z : Stmt)
    (tr : PathAlong oracleSig (protocol rounds))
    (claim : SelectedValue b × (PUnit.{1} → Fin 8)) (w : Nat)
    (accepted : closedTerminalObservation (oracleSuffixVerifier b) z tr = some claim)
    (related : selectedRelation b z tr claim w) : valid z tr w :=
  (outputLaw z tr w).mp ((selectedOracleOutputLaw b z tr w).mpr ⟨claim, accepted, related⟩)

/-- A restoration game with the authored selector retained in the returned public transcript. -/
def selectedClosedGame (b : Bool)
    (adv : OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat)) :
    OracleComp (oracleSpec Stmt Unit rounds)
      (Stmt × (tr : PathAlong oracleSig selectedProtocol) ×
        Option (SelectedValue tr.1 × (PUnit.{1} → Fin 8)) × Nat) :=
  (fun r => ⟨r.1, ⟨b, r.2.1⟩,
    closedTerminalObservation selectedVerifier r.1 ⟨b, r.2.1⟩, r.2.2⟩) <$>
    restoredExecution rounds adv

/-- Every bounded adaptive adversary retains the original one-round knowledge-error bound. -/
theorem selectedGame_bound (b : Bool)
    (adv : OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat))
    (Q : Nat) (hQ : IsTotalQueryBound adv Q) :
    Pr{let r ← (simulateQ randomOracle (selectedClosedGame b adv)).run' ∅}[
      True ∧ (∃ claim, r.2.2.1 = some claim ∧
        r.2.2.2 ≤ (claim.2 ⟨⟩).val) ∧
      ¬ Rin r.1 (knowledge.extractAlong r.1 r.2.1.2 r.2.2.2)] ≤
      (Q + rounds.length) * (1 / 2) := by
  have h := stateRestoration_oracle_knowledge_soundness (oracleSuffixVerifier b)
    (selectedRelation b) knowledge (fun _ _ w => w) (selectedOutputLaw b) (1 / 2) bounded adv Q hQ
  erw [closedVerificationGame_eq, simulateQ_map, StateT.run'_map', prEvent_map] at h
  erw [selectedClosedGame, simulateQ_map, StateT.run'_map', prEvent_map]
  simpa only [oracleObservation_prepend, selectedRelation] using h

/-- The full dependent observation agrees with the game for every possible table. -/
theorem selectedGame_eval (b : Bool) (table : Table Stmt Unit rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (selectedClosedGame b adversary) =
      ⟨stmt 0, selectedPath b 7 (table key),
        closedTerminalObservation selectedVerifier (stmt 0) (selectedPath b 7 (table key)), 6⟩ := by
  erw [selectedClosedGame, evalWithAnswerFn_map, restoredExecution_eval]
  rfl

/-- The dependent-output game is the same observation returned by replaying the real parties. -/
theorem selectedGame_eval_run (b : Bool) (table : Table Stmt Unit rounds) :
    let game := evalWithAnswerFn (QueryImpl.ofFn table) (selectedClosedGame b adversary)
    evalWithAnswerFn (selectedAnswers (table key))
      (selectedVerifier.run 0 (stmt 0).2 (selectedProver b)) =
        ⟨game.2.1, ⟨⟩, game.2.2.1⟩ := by
  erw [selectedGame_eval, selectedObservation]
  exact selectedScriptedRun_eq b (table key)

/-- The plain relation keeps challenge-based acceptance while its carrier is authored. -/
def selectedPlainRelation (b : Bool) (_ : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (out : SelectedValue b) (w : Nat) : Prop :=
  (show Bool from tr.2.1) = true ∧ w ≤ selectedValue b out

/-- The always-returning plain terminal satisfies the original terminal-state relation. -/
theorem selectedPlainOutputLaw (b : Bool) (z : Stmt)
    (tr : PathAlong oracleSig (protocol rounds)) (out : SelectedValue b) (w : Nat)
    (accepted : terminalObservation (plainSuffixVerifier b) z tr = some out)
    (related : selectedPlainRelation b z tr out w) : valid z tr w := by
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  cases b <;> cases accepted <;> exact related

/-- The plain restoration game returns the full path and the always-returning terminal. -/
def selectedPlainGame (b : Bool)
    (adv : OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat)) :
    OracleComp (oracleSpec Stmt Unit rounds)
      (Stmt × (tr : PathAlong oracleSig selectedProtocol) × Option (SelectedValue tr.1) × Nat) :=
  (fun r => ⟨r.1, ⟨b, r.2.1⟩, terminalObservation plainVerifier r.1 ⟨b, r.2.1⟩, r.2.2⟩) <$>
    restoredExecution rounds adv

/-- The frozen plain-game bound holds in each selected output carrier. -/
theorem selected_actual_game_bound (b : Bool) :
    Pr{let r ← (simulateQ randomOracle (selectedPlainGame b adversary)).run' ∅}[
      True ∧ (∃ out, r.2.2.1 = some out ∧ (show Bool from r.2.1.2.2.1) = true ∧
        r.2.2.2 ≤ selectedValue r.2.1.1 out) ∧
      ¬ Rin r.1 (knowledge.extractAlong r.1 r.2.1.2 r.2.2.2)] ≤ 1 / 2 := by
  let experiment : ProbComp (Stmt × PathAlong oracleSig (protocol rounds) × Nat) :=
    (simulateQ randomOracle (restoredExecution rounds adversary)).run' ∅
  let bad : Stmt × PathAlong oracleSig (protocol rounds) × Nat → Prop := fun r =>
    True ∧ valid r.1 r.2.1 r.2.2 ∧
      ¬ Rin r.1 (knowledge.extractAlong r.1 r.2.1 r.2.2)
  have h : Pr{let r ← experiment}[bad r] ≤ ((0 : Nat) + rounds.length) * (1 / 2 : ENNReal) :=
    restoredExecution_knowledge_soundness knowledge (1 / 2) bounded
      (fun _ _ w => w) adversary 0 trivial
  have coefficient : ((0 : Nat) + rounds.length) * (1 / 2 : ENNReal) = 1 / 2 := by
    norm_num [rounds]
  have h0 : Pr{let r ← experiment}[bad r] ≤ 1 / 2 := h.trans_eq coefficient
  erw [selectedPlainGame, simulateQ_map, StateT.run'_map', prEvent_map]
  refine le_trans (prEvent_mono experiment _ bad ?_) h0
  rintro ⟨z, tr, w⟩ ⟨ha, ⟨out, accepted, hc, related⟩, failure⟩
  have accepted' : terminalObservation (plainSuffixVerifier b) z tr = some out :=
    (plainObservation_prepend b z tr).symm.trans accepted
  exact ⟨ha, selectedPlainOutputLaw b z tr out w accepted' ⟨hc, related⟩, failure⟩

/-- The plain frozen output-state equivalence holds at every authored branch and transcript. -/
theorem selectedPlainOutputLaw_iff (b : Bool) (z : Stmt)
    (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    knowledge.toFun z (completeSpine oracleSig tr) (completeMoves oracleSig tr)
      (knowledge.terminalWitness z tr w) ↔
      ∃ out, terminalObservation (plainSuffixVerifier b) z tr = some out ∧
        selectedPlainRelation b z tr out w := by
  erw [outputLaw]
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  have obs : terminalObservation (plainSuffixVerifier b) z (path m c) =
      some (selectedPayload b m) := by cases b <;> rfl
  erw [obs]
  cases b <;> constructor
  · intro h
    exact ⟨_, rfl, h⟩
  · rintro ⟨out, h, related⟩
    cases h
    exact related
  · intro h
    exact ⟨_, rfl, h⟩
  · rintro ⟨out, h, related⟩
    cases h
    exact related

/-- Each selected protocol draws the original uniform challenge after its authored prefix. -/
def selectedDraw : QueryImpl (challengeSpec oracleSig selectedProtocol) ProbComp
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, n⟩, h⟩ => uniformDraw rounds ⟨n, h⟩

/-- The prover authors its selector and payload before receiving the sampled challenge. -/
def selectedProbProver (b : Bool) (m : Fin 8) :
    Focal oracleSig ProbComp selectedProtocol (fun _ => PUnit.{1}) :=
  pure ⟨b, pure ⟨m, pure fun _ => pure ⟨⟩⟩⟩

/-- The full interaction's challenge marginal is uniform for every input, selector and payload. -/
theorem selected_fresh (_z : Nat) (b : Bool) (m : Fin 8) :
    (fun r => (show Bool from r.1.2.2.1)) <$>
      TwoParty.Lens.run selectedProtocol (selectedProbProver b m)
        (sampler oracleSig selectedProtocol selectedDraw) = ($ᵗ Bool) := by
  change (fun c : Bool => c) <$> ($ᵗ Bool) = ($ᵗ Bool)
  exact LawfulFunctor.id_map _

/-- The frozen zero-query closed-game row holds in both authored branches. -/
theorem selected_actual_oracle_game_bound (b : Bool) :
    Pr{let r ← (simulateQ randomOracle (selectedClosedGame b adversary)).run' ∅}[
      True ∧ (∃ claim, r.2.2.1 = some claim ∧
        r.2.2.2 ≤ (claim.2 ⟨⟩).val) ∧
      ¬ Rin r.1 (knowledge.extractAlong r.1 r.2.1.2 r.2.2.2)] ≤ 1 / 2 := by
  simpa [rounds] using selectedGame_bound b adversary 0 trivial

/-- Both uniformly coin-selected adversaries retain the dependent-output bound. -/
theorem selected_actual_coin_game_bound (b : Bool) :
    Pr{let r ← ((OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool) >>= fun coin =>
      OptionT.lift ((simulateQ randomOracle
        (selectedClosedGame b (coinAdversary coin))).run' ∅))}[
      True ∧ (∃ claim, r.2.2.1 = some claim ∧
        r.2.2.2 ≤ (claim.2 ⟨⟩).val) ∧
      ¬ Rin r.1 (knowledge.extractAlong r.1 r.2.1.2 r.2.2.2)] ≤ 1 / 2 := by
  apply prEvent_bind_le_of_forall_le
  intro coin
  erw [OptionT.prEvent_lift]
  apply le_trans (selectedGame_bound b (coinAdversary coin) 0 (by cases coin <;> trivial))
  simp [rounds]

/-- Failed private coins give zero mass for the dependent-output game as well. -/
example (b : Bool) :
    Pr{let _r ← ((failure : OptionT ProbComp Bool) >>= fun coin => OptionT.lift
      ((simulateQ randomOracle (selectedClosedGame b (coinAdversary coin))).run' ∅))}[True] =
    0 := by
  simp [failure_bind]

/-- Additional coverage allows the output oracle's carrier and interface to vary by public path. -/
def varyingVerifier : OracleVerifier.{0, 0, 0, 0, 0, 0, 0} []ₒ selectedProtocol Nat SelectedOutput
    emptyFamily (fun p => varyingFamily p.1) where
  decide _ p _ := readSelected p.1 p.2
  outputMap _ p _ := varyingMap p.1 p.2

/-- Both path-selected oracle families answer with the original payload's numerical value. -/
example (b c : Bool) (z : Stmt) (m : Fin 8) :
    closedTerminalObservation varyingVerifier z (selectedPath b m c) =
      some (selectedPayload b m, fun _ => selectedPayload b m) := by
  cases b <;> rfl

/-- A full restoration game whose returned output oracle family actually varies by shape path. -/
def varyingGame (b : Bool) : OracleComp (oracleSpec Stmt Unit rounds)
    (Stmt × (tr : PathAlong oracleSig selectedProtocol) ×
      Option (SelectedValue tr.1 × (PUnit.{1} → SelectedValue tr.1)) × Nat) :=
  (fun r => ⟨r.1, ⟨b, r.2.1⟩, closedTerminalObservation varyingVerifier r.1 ⟨b, r.2.1⟩,
    r.2.2⟩) <$> restoredExecution rounds adversary

/-- The varying-family game retains every table's challenge and the original payload seven. -/
example (b : Bool) (table : Table Stmt Unit rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (varyingGame b) =
      ⟨stmt 0, selectedPath b 7 (table key),
        some (selectedPayload b 7, fun _ => selectedPayload b 7), 6⟩ := by
  erw [varyingGame, evalWithAnswerFn_map, restoredExecution_eval]
  cases b <;> rfl

/-- Rejection on false has no related claim in either authored output carrier. -/
example (b : Bool) (z : Stmt) (m : Fin 8)
    (relation : SelectedValue b × (PUnit.{1} → Fin 8) → Prop) :
    ¬ ∃ claim, closedTerminalObservation selectedVerifier z (selectedPath b m false) = some claim ∧
      relation claim := by
  erw [selectedObservation]
  simp

end Interaction.Core.StateRestorationTests

run_cmd do
  for decl in [``Interaction.Core.StateRestorationTests.plainScriptedRun_eq,
      ``Interaction.Core.StateRestorationTests.selectedScriptedRun_eq,
      ``Interaction.Core.StateRestorationTests.replayResult_eq,
      ``Interaction.Core.StateRestorationTests.oracleReplayResult_eq,
      ``Interaction.Core.StateRestorationTests.selectedOracleOutputLaw,
      ``Interaction.Core.StateRestorationTests.selectedPlainOutputLaw_iff,
      ``Interaction.Core.StateRestorationTests.selected_fresh,
      ``Interaction.Core.StateRestorationTests.selectedGame_bound,
      ``Interaction.Core.StateRestorationTests.selected_actual_game_bound,
      ``Interaction.Core.StateRestorationTests.selected_actual_oracle_game_bound,
      ``Interaction.Core.StateRestorationTests.selected_actual_coin_game_bound,
      ``Interaction.Core.StateRestorationTests.selectedGame_eval_run] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
