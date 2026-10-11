/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.StateRestorationCoins

/-!
An ordinary-import native state-restoration client. Verification queries the actual sent payload,
its output type depends on the public challenge, and backward extraction uses both that payload
and the supplied witness. The input domain is Nat, so this does not assume a finite statement set.
-/

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security.StateRestorationTest

@[instance_reducible] def messageInterface : OracleInterface (Fin 8) where
  Query := Unit
  toOC := { spec := fun _ => Fin 8, impl := fun _ message => message }

@[implicit_reducible] def round : Round where
  Message := Fin 8
  Challenge := Bool
  interface := messageInterface
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

@[implicit_reducible] def rounds : List Round := [round]
abbrev tree := (protocol rounds).tree
abbrev roles := (protocol rounds).roles
abbrev oracles := (protocol rounds).oracles
abbrev initial := emptySpec.toPFunctor

def inputImpl : Nat → QueryImpl (ofPFunctor initial) Id := fun _ q => nomatch q

def inputState (z : Nat) : KnowledgeState := ⟨Nat, fun witness => witness ≤ z⟩
def messageState : KnowledgeState := ⟨Nat × Unit, fun _ => False⟩
def challengeState (message : Fin 8) (challenge : Bool) : KnowledgeState :=
  ⟨Nat × Unit, fun witness => challenge = true ∧ witness.1 ≤ message.val⟩

def extractor (z : Nat) : RoundExtractor tree (inputState z) :=
  fun message => ⟨messageState, (fun witness => witness.1 + message.val),
    fun challenge => ⟨challengeState message challenge, id, PUnit.unit⟩⟩

def witnessEquiv : Nat ≃ Nat × Unit where
  toFun := fun witness => ⟨witness, ()⟩
  invFun := Prod.fst
  left_inv := fun _ => rfl
  right_inv := by rintro ⟨witness, token⟩; cases token; rfl

def terminalWitness (z : Nat) (path : tree.ExecutionPath) :
    Nat ≃ ((extractor z).terminalState path).Witness := by
  rcases path with ⟨message, challenge, terminal⟩
  exact witnessEquiv

def Out (_ : Nat) (p : tree.BranchPath) : Type :=
  if (show Bool from p.2.1) = true then Fin 8 else Fin 9

def outputValue (z : Nat) (p : tree.BranchPath) : Out z p → Nat := by
  rcases p with ⟨marker, challenge, terminal⟩
  unfold Out
  cases challenge <;> exact Fin.val

def terminal (z : Nat) (p : tree.BranchPath) :
    OracleComp (ofPFunctor (accessAfter tree oracles initial p)) (Out z p) := by
  rcases p with ⟨marker, challenge, terminal⟩
  cases challenge
  · change OracleComp (emptySpec + @OracleInterface.spec (Fin 8) messageInterface) (Fin 9)
    exact do
      let message ← liftM ((emptySpec + @OracleInterface.spec (Fin 8) messageInterface).query
        (Sum.inr ()))
      pure ⟨message.val, Nat.lt_trans message.isLt (by decide : 8 < 9)⟩
  · change OracleComp (emptySpec + @OracleInterface.spec (Fin 8) messageInterface) (Fin 8)
    exact liftM ((emptySpec + @OracleInterface.spec (Fin 8) messageInterface).query (Sum.inr ()))

def Rin (z witness : Nat) : Prop := witness ≤ z

def Rout (z : Nat) (p : tree.BranchPath) (output : Out z p) (witness : Nat) : Prop :=
  p.2.1 = true ∧ witness ≤ outputValue z p output

theorem inputLaw (z witness : Nat) : (inputState z).holds witness ↔ Rin z witness := Iff.rfl

theorem outputLaw (z : Nat) (path : tree.ExecutionPath) (witness : Nat) :
    ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
      Rout z path.toBranchPath
        (terminalObservation initial inputImpl Out terminal z path) witness := by
  rcases path with ⟨message, challenge, terminal⟩
  cases challenge <;> rfl

theorem preserving (z : Nat) : (extractor z).IsProverPreserving roles := by
  refine ⟨?_, ?_⟩
  · intro message witness impossible
    exact impossible.elim
  · intro message
    refine ⟨?_, fun _ => trivial⟩
    intro challenge sender
    cases sender

theorem badChallenge_iff (z : Nat) (message : Fin 8) (challenge : Bool) :
    RoundExtractor.badChallenge (extractor z message).2.2 challenge ↔ challenge = true := by
  constructor
  · rintro ⟨witness, _, known⟩
    exact known.1
  · intro isTrue
    exact ⟨⟨0, ()⟩, (fun impossible => impossible), ⟨isTrue, Nat.zero_le _⟩⟩

theorem bounded (z : Nat) : RoundExtractor.IsLocallyBounded (extractor z) roles
    (uniformSchedule (1 / 2) rounds) := by
  intro message
  refine ⟨?_, fun _ => trivial⟩
  apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
  intro round context
  change Pr{let challenge ← $ᵗ Bool}[
    RoundExtractor.badChallenge (extractor z message).2.2 challenge] ≤ 1 / 2
  have half : Pr{let challenge ← $ᵗ Bool}[challenge = true] = (1 / 2 : ENNReal) := by
    rw [SampleableType.prEvent_uniformSample_eq_singleton]
    simp only [Fintype.card_bool, Nat.cast_ofNat, one_div]
  change Pr{let challenge ← $ᵗ Bool}[
    ∃ witness : Nat × Unit, ¬ False ∧
      challenge = true ∧ witness.1 ≤ message.val] ≤ 1 / 2
  have event : (fun challenge : Bool =>
      ∃ witness : Nat × Unit, ¬ False ∧ challenge = true ∧ witness.1 ≤ message.val) =
      (fun challenge => challenge = true) := by
    funext challenge
    apply propext
    constructor
    · rintro ⟨witness, _, known, _⟩
      exact known
    · intro known
      exact ⟨⟨0, ()⟩, not_false, known, Nat.zero_le _⟩
  simp only [← map_eq_pure_bind]
  rw [event]
  exact half.le

def messages : Messages Unit rounds := ⟨(7 : Fin 8), (), PUnit.unit⟩
def path (challenge : Bool) : tree.ExecutionPath := ⟨(7 : Fin 8), challenge, PUnit.unit⟩

def adversary : OracleComp (oracleSpec Nat Unit rounds) (Nat × Messages Unit rounds × Nat) :=
  pure ⟨0, messages, 6⟩

example (challenge : Bool) :
    extractInputWitness inputState extractor terminalWitness 0 (path challenge) 6 =
      (13 : Nat) := rfl

example (z : Nat) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) tree roles oracles initial (inputImpl z) _
      (challengeVerifier unifSpec rounds initial (uniformPrograms rounds) (Out z) (terminal z))
      (uniformSchedule (1 / 2) rounds) :=
  uniformVerifier_fresh (1 / 2) rounds initial (inputImpl z) (Out z) (terminal z)

theorem actual_game_bound :
    Pr{let result ← (simulateQ randomOracle
      (verificationGame initial inputImpl Out terminal adversary)).run' ∅}[
      result.1 ∈ Set.univ ∧ Rout result.1 result.2.1.toBranchPath result.2.2.1 result.2.2.2 ∧
      ¬ Rin result.1 (extractInputWitness inputState extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_knowledge_soundness inputState extractor Set.univ (1 / 2)
    (fun z _ => preserving z) (fun z _ => bounded z) initial inputImpl Out terminal Rin Rout
    terminalWitness inputLaw outputLaw adversary 0 (by trivial)
  simpa [rounds] using general

def nativeResult (challenge : Bool) : OracleComp emptySpec (Nat × Bool × Nat) :=
  (fun result => ⟨result.1.1.val, result.2.1.2.1,
    outputValue 0 result.1.toBranchPath result.2.2⟩) <$>
  executeStrategies emptySpec tree roles oracles initial (inputImpl 0)
    (scriptedProver emptySpec rounds messages)
    (challengeVerifier emptySpec rounds initial (pathPrograms emptySpec rounds (path challenge))
      (Out 0) (terminal 0))

theorem nativeResult_eq (challenge : Bool) :
    nativeResult challenge = pure ⟨7, challenge, 7⟩ := by
  unfold nativeResult
  rw [execute_pathReplay emptySpec rounds initial (inputImpl 0) messages (path challenge)
    (show MatchesMessages rounds messages (path challenge) from ⟨rfl, trivial⟩)]
  cases challenge <;> rfl

#eval evalWithAnswerFn (fun q => nomatch q) (nativeResult true)
#eval evalWithAnswerFn (fun q => nomatch q) (nativeResult false)
#eval extractInputWitness inputState extractor terminalWitness 0 (path true) 6

@[implicit_reducible] def outputFamily : OracleFamily Unit (fun _ => Fin 8) :=
  ⟨fun _ => messageInterface⟩

def family (_ : Nat) (_ : tree.BranchPath) := outputFamily

def oracleTerminal (z : Nat) (p : tree.BranchPath) :
    OracleComp (ofPFunctor (accessAfter tree oracles initial p))
      (OracleOutput initial Out family z p) := by
  rcases p with ⟨marker, challenge, terminal⟩
  cases challenge
  · exact pure none
  · change OracleComp (emptySpec + @OracleInterface.spec (Fin 8) messageInterface)
      (Option (OpenClaim (emptySpec + @OracleInterface.spec (Fin 8) messageInterface)
        (Fin 8) outputFamily))
    let readPayload : OracleComp
        (emptySpec + @OracleInterface.spec (Fin 8) messageInterface) (Fin 8) :=
      liftM ((emptySpec + @OracleInterface.spec (Fin 8) messageInterface).query (Sum.inr ()))
    exact do
      let statement ← readPayload
      pure (some ⟨statement, ⟨fun _ => readPayload⟩⟩)

def oracleRout (z : Nat) (p : tree.BranchPath)
    (claim : ClosedClaim (Out z p) (family z p)) (witness : Nat) : Prop :=
  witness ≤ (claim.oracles ⟨(), ()⟩).val

def returnedClaim (z : Nat) (message : Fin 8) :
    ClosedClaim (Out z ⟨PUnit.unit, true, PUnit.unit⟩) outputFamily :=
  ⟨message, fun _ => message⟩

theorem oracleObservation_true (z : Nat) (message : Fin 8) :
    closedTerminalObservation initial inputImpl Out family oracleTerminal z
      ⟨message, true, PUnit.unit⟩ = some (returnedClaim z message) := rfl

theorem oracleObservation_false (z : Nat) (message : Fin 8) :
    closedTerminalObservation initial inputImpl Out family oracleTerminal z
      ⟨message, false, PUnit.unit⟩ = none := rfl

theorem oracleOutputLaw (z : Nat) (path : tree.ExecutionPath) (witness : Nat) :
    ((extractor z).terminalState path).holds (terminalWitness z path witness) ↔
      ∃ claim, closedTerminalObservation initial inputImpl Out family oracleTerminal z path =
        some claim ∧ oracleRout z path.toBranchPath claim witness := by
  rcases path with ⟨message, challenge, done⟩
  cases done
  cases challenge
  · rw [oracleObservation_false z message]
    change (false = true ∧ witness ≤ message.val) ↔ ∃ claim, none = some claim ∧ _
    simp
  · rw [oracleObservation_true z message]
    change (true = true ∧ witness ≤ message.val) ↔
      ∃ claim, some (returnedClaim z message) = some claim ∧
        witness ≤ (claim.oracles ⟨(), ()⟩).val
    simp only [Option.some.injEq, true_and]
    constructor
    · intro valid
      exact ⟨returnedClaim z message, rfl, valid⟩
    · rintro ⟨claim, same, valid⟩
      subst claim
      exact valid

theorem actual_oracle_game_bound :
    Pr{let result ← (simulateQ randomOracle
      (closedVerificationGame initial inputImpl Out family oracleTerminal adversary)).run' ∅}[
      result.1 ∈ Set.univ ∧
      (∃ claim, result.2.2.1 = some claim ∧
        oracleRout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness inputState extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_oracle_knowledge_soundness inputState extractor Set.univ
    (1 / 2) (fun z _ => preserving z) (fun z _ => bounded z) initial inputImpl Out family
    oracleTerminal Rin oracleRout terminalWitness inputLaw oracleOutputLaw adversary 0 (by trivial)
  simpa [rounds] using general

example (z : Nat) (message : Fin 8) (witness : Nat) :
    ¬ ∃ claim, closedTerminalObservation initial inputImpl Out family oracleTerminal z
      ⟨message, false, PUnit.unit⟩ = some claim ∧ oracleRout z _ claim witness := by
  rw [oracleObservation_false]
  simp

#eval ((closedTerminalObservation initial inputImpl Out family oracleTerminal 0 (path true)).map
  (fun claim => (claim.stmt.val, (claim.oracles ⟨(), ()⟩).val)))
#eval ((closedTerminalObservation initial inputImpl Out family oracleTerminal 0 (path false)).map
  (fun claim => (outputValue 0 (path false).toBranchPath claim.stmt,
    (claim.oracles ⟨(), ()⟩).val)))

def coinAdversary (coin : Bool) :
    OracleComp (oracleSpec Nat Unit rounds) (Nat × Messages Unit rounds × Nat) :=
  if coin then adversary else pure ⟨0, ⟨(3 : Fin 8), (), PUnit.unit⟩, 2⟩

theorem actual_coin_oracle_game_bound :
    Pr{let result ← ((OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool) >>= fun coin =>
      OptionT.lift ((simulateQ randomOracle
        (closedVerificationGame initial inputImpl Out family oracleTerminal
          (coinAdversary coin))).run' ∅))}[
      result.1 ∈ Set.univ ∧
      (∃ claim, result.2.2.1 = some claim ∧
        oracleRout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness inputState extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ 1 / 2 := by
  have general := stateRestoration_oracle_knowledge_soundness_privateCoins
    inputState extractor Set.univ (1 / 2) (fun z _ => preserving z) (fun z _ => bounded z)
    initial inputImpl Out family oracleTerminal Rin oracleRout terminalWitness inputLaw
    oracleOutputLaw (OptionT.lift ($ᵗ Bool) : OptionT ProbComp Bool) coinAdversary 0
    (fun coin => by cases coin <;> trivial)
  simpa [rounds] using general

example : Pr{let _result ← ((failure : OptionT ProbComp Bool) >>= fun coin => OptionT.lift
    ((simulateQ randomOracle
      (closedVerificationGame initial inputImpl Out family oracleTerminal
        (coinAdversary coin))).run' ∅))}[True] = 0 := by
  simp [failure_bind]

end Interaction.Oracle.Security.StateRestorationTest
