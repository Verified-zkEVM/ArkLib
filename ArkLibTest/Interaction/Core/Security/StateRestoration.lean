/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.StateRestoration
import ArkLibTest.Interaction.Core.Oracle

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
@[implicit_reducible] def round : Round where
  Message := Fin 8
  Challenge := Bool
  interface := messageInterface
  sampleChallenge := inferInstance

@[implicit_reducible] def rounds : List Round := [round]

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

instance : DecidableEq (Key Stmt Unit rounds) :=
  inferInstanceAs (DecidableEq ((Stmt × Fin 8 × Unit) ⊕ (Fin 8 × Unit × Empty)))

/-- On challenge `true` read the payload and return it, on `false` reject. The output oracle is
the sent payload. -/
def verifier : OracleVerifier []ₒ (protocol rounds) Nat (Fin 8) emptyFamily outputFamily where
  decide _ p v := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact if (show Bool from v.1.2.1) then
      liftM (([]ₒ + (sumFamily emptyFamily
        (pathFamily (protocol rounds) ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩)).spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
    else failure
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact OracleMap.embedding (sumFamily emptyFamily (pathFamily (protocol rounds)
      ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩)) (fun _ => .inr (.inl ⟨⟩))

/-- The transcript with message `m` and challenge `c`. -/
def path (m : Fin 8) (c : Bool) : PathAlong oracleSig (protocol rounds) := ⟨m, ⟨c, ⟨⟩⟩⟩

/-- The adversary selects input 0, message 7, salt `()` and witness 6 without querying. -/
def messages : Messages Unit rounds := ⟨(7 : Fin 8), (), PUnit.unit⟩

def adversary : OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat) :=
  pure ⟨stmt 0, messages, 6⟩

/-- The single first-round key of the adversary's selection. -/
def key : Key Stmt Unit rounds := Key.here (stmt 0) (7 : Fin 8) ()

-- Row 7 (StateRestoration L150, uniformVerifier_fresh): the game's challenge draw at a key's
-- receiver prefix is the uniform sample of that round's alphabet.
example : sampleAt oracleSig (uniformDraw rounds) (keySpine key) rfl = ($ᵗ Bool) :=
  sampleAt_keySpine key

-- Row 13 (StateRestoration L215, oracleObservation_true): on `true` the closed observation returns
-- the message as the claim and as its output oracle.
theorem oracleObservation_true (z : Nat) (m : Fin 8) :
    closedTerminalObservation verifier (stmt z) (path m true) = some (m, fun _ => m) := rfl

-- Row 14 (StateRestoration L219, oracleObservation_false): on `false` the closed observation is
-- `none`.
theorem oracleObservation_false (z : Nat) (m : Fin 8) :
    closedTerminalObservation verifier (stmt z) (path m false) = none := rfl

-- Row 17 (StateRestoration L258): the `false` branch returns no claim in the fixed `Option`
-- output, so no output relation can hold there.
example (z : Nat) (m : Fin 8) (rel : Fin 8 × (PUnit → Fin 8) → Prop) :
    ¬ ∃ claim, closedTerminalObservation verifier (stmt z) (path m false) = some claim ∧
      rel claim := by
  rw [oracleObservation_false]
  simp

-- Row 9 (StateRestoration L175, nativeResult_eq): against any answer table, the game completes
-- the adversary's selection with the table's challenge, and the verifier decides on that path.
theorem game_eval (table : Table Stmt Unit rounds) :
    evalWithAnswerFn (QueryImpl.ofFn table) (closedVerificationGame verifier adversary) =
      (stmt 0, path 7 (table key), closedTerminalObservation verifier (stmt 0) (path 7 (table key)),
        6) := by
  rw [closedVerificationGame_eq, evalWithAnswerFn_map, restoredExecution_eval]
  rfl

/-- The game's output against the constant table `c`, as plain numbers. -/
def gameResult (c : Bool) : Nat × Bool × Option (Nat × Nat) × Nat :=
  let table : Table Stmt Unit rounds
    | .inl _ => c
    | .inr (_, _, key) => key.elim
  let r := evalWithAnswerFn (QueryImpl.ofFn table) (closedVerificationGame verifier adversary)
  (r.1.1, r.2.1.2.1, r.2.2.1.map (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat))), r.2.2.2)

-- Row 10 (StateRestoration L182): the game run on challenge `true`.
/-- info: (0, true, some (7, 7), 6) -/
#guard_msgs in
#eval gameResult true

-- Row 11 (StateRestoration L183): the game run on challenge `false`.
/-- info: (0, false, none, 6) -/
#guard_msgs in
#eval gameResult false

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
def knowledge : KnowledgeStateFunction oracleSig (protocol rounds) Stmt Nat Nat (fun _ => True)
    Rin valid where
  Witness _ _ := Nat
  toFun sp history z w := match sp, history with
    | .root _, _ => w ≤ z.1
    | .down _ (.root _), _ => False
    | .down _ (.down _ _), history =>
      (show Bool from history.2.1.1) = true ∧ w ≤ (show Fin 8 from history.1.1).val
  extractRoot _ w := w
  extractStep sp _ _ x w := by
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

-- Row 1 (StateRestoration L87, inputLaw): the root state is the input relation.
theorem inputLaw (z : Stmt) (w : Nat) : knowledge.toFun (.root _) ⟨⟩ z w ↔ Rin z w := Iff.rfl

-- Row 2 (StateRestoration L89, outputLaw): the terminal state on the terminal witness is the
-- valid-output relation, on every transcript.
theorem outputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    knowledge.toFun (completeSpine oracleSig tr) (completeMoves oracleSig tr) z
      (knowledge.terminalWitness z tr w) ↔ valid z tr w := by
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  rfl

-- Row 3 (StateRestoration L96, preserving): the send law at the message, the only prover move.
-- No witness is known after the message, so preservation is vacuous there.
theorem preserving (z : Stmt) (m : Fin 8) (w : Nat) :
    ¬ knowledge.toFun (.down ⟨⟩ (.root _)) ⟨⟨m, rfl⟩, ⟨⟩⟩ z w := id

/-- The receiver cursor at the challenge, below message `m`. -/
abbrev challengeSpine : Cursor.Spine (protocol rounds)
    (.liftBind (OraclePos.challenge Bool) (fun _ => protocol [])) :=
  .down ⟨⟩ (.root _)

-- Row 4 (StateRestoration L105, badChallenge_iff): below every message the bad challenges are
-- exactly `true`.
theorem badChallenge_iff (z : Stmt) (m : Fin 8) (c : Bool) :
    c ∈ knowledge.badChallenge challengeSpine ⟨⟨m, rfl⟩, ⟨⟩⟩ z ↔ c = true := by
  constructor
  · rintro ⟨_, _, known, _⟩
    exact known
  · intro isTrue
    exact ⟨(0 : Nat), id, isTrue, Nat.zero_le _⟩

theorem uniform_true : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 1 / 2 := by
  rw [SampleableType.evalDist_uniformSample_singleton, one_div]
  simp

-- Row 5 (StateRestoration L113, bounded): the state function is locally bounded by `1/2` at the
-- uniform draw, hence round-by-round knowledge sound.
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

example : rbrKnowledgeSoundness oracleSig (protocol rounds) (fun _ => True) Rin valid
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
      table k ∈ knowledge.badChallenge (keySpine k) (keyHistory k table) (stmt 0) := by
  apply exists_badChallenge_of_extraction_failure knowledge (stmt 0) messages table 6
  · exact ⟨htrue, show 6 ≤ 7 by omega⟩
  · change ¬ (6 + 7 ≤ 0)
    omega

/-- The plain output relation: the witness is at most the accepted statement. -/
def Rout (_ : Stmt) (_ : PathAlong oracleSig (protocol rounds)) (t : Fin 8) (w : Nat) : Prop :=
  w ≤ t.val

theorem plainOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (t : Fin 8)
    (w : Nat) (accepted : terminalObservation verifier z tr = some t) (related : Rout z tr t w) :
    valid z tr w := by
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  cases c
  · cases accepted
  · cases accepted
    exact ⟨rfl, related⟩

-- Row 8 (StateRestoration L156, actual_game_bound): the plain game has knowledge error at most
-- `1/2` for an adversary without queries.
theorem actual_game_bound :
    Pr{let result ← (simulateQ randomOracle (verificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ t, result.2.2.1 = some t ∧ Rout result.1 result.2.1 t result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_knowledge_soundness verifier Rout knowledge plainOutputLaw
    (1 / 2) bounded adversary 0 trivial
  simpa [rounds] using general

/-- The oracle output relation: the witness is at most the output oracle's data. -/
def oracleRout (_ : Stmt) (_ : PathAlong oracleSig (protocol rounds))
    (claim : Fin 8 × (PUnit.{1} → Fin 8)) (w : Nat) : Prop :=
  w ≤ (claim.2 ⟨⟩).val

-- Row 15 (StateRestoration L223, oracleOutputLaw): the terminal state on the terminal witness is
-- an accepted closed claim related to the witness.
theorem oracleOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds)) (w : Nat) :
    knowledge.toFun (completeSpine oracleSig tr) (completeMoves oracleSig tr) z
      (knowledge.terminalWitness z tr w) ↔
      ∃ claim, closedTerminalObservation verifier z tr = some claim ∧ oracleRout z tr claim w := by
  rcases tr with ⟨m, ⟨c, ⟨⟩⟩⟩
  cases c
  · change (false = true ∧ _) ↔ ∃ claim, none = some claim ∧ _
    simp
  · change (true = true ∧ w ≤ m.val) ↔ ∃ claim, some (m, fun _ => m) = some claim ∧ _
    simp [oracleRout]

theorem closedOutputLaw (z : Stmt) (tr : PathAlong oracleSig (protocol rounds))
    (claim : Fin 8 × (PUnit.{1} → Fin 8)) (w : Nat)
    (accepted : closedTerminalObservation verifier z tr = some claim)
    (related : oracleRout z tr claim w) : valid z tr w :=
  (outputLaw z tr w).mp ((oracleOutputLaw z tr w).mpr ⟨claim, accepted, related⟩)

-- Row 16 (StateRestoration L245, actual_oracle_game_bound): the closed game has knowledge error at
-- most `1/2`.
theorem actual_oracle_game_bound :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame verifier adversary)).run' ∅}[
      True ∧ (∃ claim, result.2.2.1 = some claim ∧ oracleRout result.1 result.2.1 claim
        result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_oracle_knowledge_soundness verifier oracleRout knowledge
    closedOutputLaw (1 / 2) bounded adversary 0 trivial
  simpa [rounds] using general

-- Row 20 (StateRestoration L274, actual_coin_oracle_game_bound): the same bound with uniform
-- private coins choosing between two adversaries.
theorem actual_coin_oracle_game_bound :
    Pr{let result ← ((OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool) >>= fun coin =>
      OptionT.lift ((simulateQ randomOracle
        (closedVerificationGame verifier (coinAdversary coin))).run' ∅))}[
      True ∧ (∃ claim, result.2.2.1 = some claim ∧ oracleRout result.1 result.2.1 claim
        result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_oracle_knowledge_soundness_privateCoins verifier oracleRout
    knowledge closedOutputLaw (1 / 2) bounded (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool)
    coinAdversary 0 (fun coin => by cases coin <;> trivial)
  simpa [rounds] using general

-- The plain private-coins form.
example :
    Pr{let result ← ((OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool) >>= fun coin =>
      OptionT.lift ((simulateQ randomOracle
        (verificationGame verifier (coinAdversary coin))).run' ∅))}[
      True ∧ (∃ t, result.2.2.1 = some t ∧ Rout result.1 result.2.1 t result.2.2.2) ∧
      ¬ Rin result.1 (knowledge.extractAlong result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_knowledge_soundness_privateCoins verifier Rout knowledge
    plainOutputLaw (1 / 2) bounded (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool)
    coinAdversary 0 (fun coin => by cases coin <;> trivial)
  simpa [rounds] using general

end Interaction.Core.StateRestorationTests
