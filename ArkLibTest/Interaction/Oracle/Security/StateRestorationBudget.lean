/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.StateRestorationBudget

/-!
A two-round native closed-oracle client with distinct challenge alphabets and local errors 1/8
and 1/16. Input statements range over Nat. The actual terminal output reads the second oracle
message; named backward extraction adds both actual payloads to the supplied witness.
-/

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security.StateRestorationBudgetTest

set_option backward.isDefEq.respectTransparency false

@[instance_reducible] def messageInterface : OracleInterface (Fin 8) where
  Query := Unit
  toOC := { spec := fun _ => Fin 8, impl := fun _ message => message }

@[implicit_reducible] def firstRound : Round where
  Message := Fin 8
  Challenge := Fin 8
  interface := messageInterface
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

@[implicit_reducible] def secondRound : Round where
  Message := Fin 8
  Challenge := Fin 16
  interface := messageInterface
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

@[implicit_reducible] def rounds : List Round := [firstRound, secondRound]
abbrev tree := (protocol rounds).tree
abbrev roles := (protocol rounds).roles
abbrev oracles := (protocol rounds).oracles
abbrev initial := emptySpec.toPFunctor

noncomputable def errors : Fin 2 → ENNReal := fun j => if j = 0 then 1 / 8 else 1 / 16

def inputImpl : Nat → QueryImpl (ofPFunctor initial) Id := fun _ q => nomatch q

def inputState (z : Nat) : KnowledgeState := ⟨Nat, fun w => w ≤ z⟩
def messageState : KnowledgeState := ⟨Nat, fun _ => False⟩
def middleState (first : Fin 8) : KnowledgeState := ⟨Nat, fun _ => first = 0⟩
def finalState (message : Fin 8) (first : Fin 8) (second : Fin 16) : KnowledgeState :=
  ⟨Nat × Unit, fun w => (first = 0 ∨ second = 0) ∧ w.1 ≤ message.val⟩

def extractor (z : Nat) : RoundExtractor tree (inputState z) :=
  fun (firstMessage : Fin 8) => ⟨messageState, (fun w : Nat => w + firstMessage.val),
    fun (first : Fin 8) => ⟨middleState first, id,
      fun (secondMessage : Fin 8) => ⟨middleState first, (fun w : Nat => w + secondMessage.val),
        fun (second : Fin 16) => ⟨finalState secondMessage first second, Prod.fst, PUnit.unit⟩⟩⟩⟩

def witnessEquiv : Nat ≃ Nat × Unit where
  toFun := fun w => ⟨w, ()⟩
  invFun := Prod.fst
  left_inv := fun _ => rfl
  right_inv := by rintro ⟨w, token⟩; cases token; rfl

def terminalWitness (z : Nat) (path : tree.ExecutionPath) :
    Nat ≃ ((extractor z).terminalState path).Witness := by
  rcases path with ⟨_, _, _, _, _⟩
  exact witnessEquiv

theorem preserving (z : Nat) : (extractor z).IsProverPreserving roles := by
  refine ⟨fun _ _ impossible => impossible.elim, ?_⟩
  intro firstMessage
  refine ⟨?_, ?_⟩
  · intro first sender
    cases sender
  · intro first
    refine ⟨fun _ _ known => known, ?_⟩
    intro secondMessage
    refine ⟨?_, fun _ => trivial⟩
    intro second sender
    cases sender

theorem bounded (z : Nat) : RoundExtractor.IsLocallyBounded (extractor z) roles
    (roundErrorSchedule rounds errors) := by
  intro firstMessage
  refine ⟨?_, ?_⟩
  · apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
    intro round context
    change Pr{let first ← $ᵗ Fin 8}[∃ w : Nat, ¬ False ∧ first = 0] ≤ 1 / 8
    have event : (fun first : Fin 8 => ∃ w : Nat, ¬ False ∧ first = 0) =
        (fun first => first = 0) := by
      funext first
      apply propext
      simp
    simp only [← map_eq_pure_bind]
    rw [event]
    have oneEighth : Pr{let first ← $ᵗ Fin 8}[first = 0] = (1 / 8 : ENNReal) := by
      rw [SampleableType.prEvent_uniformSample_eq_singleton]
      simp
    exact oneEighth.le
  · intro first secondMessage
    change Fin 8 at first
    refine ⟨?_, fun _ => trivial⟩
    apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
    intro round context
    change Pr{let second ← $ᵗ Fin 16}[
      ∃ w : Nat × Unit, ¬ first = 0 ∧
        (first = 0 ∨ second = 0) ∧ w.1 ≤ secondMessage.val] ≤ 1 / 16
    calc
      _ ≤ Pr{let second ← $ᵗ Fin 16}[second = 0] := by
        apply prEvent_mono
        rintro second ⟨w, notZero, known | known, _⟩
        · exact (notZero known).elim
        · exact known
      _ = 1 / 16 := by rw [SampleableType.prEvent_uniformSample_eq_singleton]; simp

@[instance_reducible] def outputFamily : OracleFamily Unit (fun _ => Fin 8) where
  interface := fun _ => messageInterface

def family (_ : Nat) (_ : tree.BranchPath) := outputFamily

def Out (_ : Nat) (p : tree.BranchPath) : Type :=
  if (show Fin 8 from p.2.1) = 0 then Fin 8 else Fin 9

def outputValue (z : Nat) (p : tree.BranchPath) : Out z p → Nat := by
  unfold Out
  split <;> exact Fin.val

def returnedStmt (z : Nat) (p : tree.BranchPath) (message : Fin 8) : Out z p := by
  unfold Out
  split
  · exact message
  · exact ⟨message.val, Nat.lt_trans message.isLt (by decide : 8 < 9)⟩

def oracleTerminal (z : Nat) (p : tree.BranchPath) :
    OracleComp (ofPFunctor (accessAfter tree oracles initial p))
      (OracleOutput initial Out family z p) := by
  rcases p with ⟨_, first, _, second, _⟩
  let readPayload : OracleComp
      ((emptySpec + @OracleInterface.spec (Fin 8) messageInterface) +
        @OracleInterface.spec (Fin 8) messageInterface) (Fin 8) :=
    liftM (((emptySpec + @OracleInterface.spec (Fin 8) messageInterface) +
      @OracleInterface.spec (Fin 8) messageInterface).query (Sum.inr ()))
  exact if (show Fin 8 from first) = 0 ∨ (show Fin 16 from second) = 0 then do
    let message ← readPayload
    pure (some ⟨returnedStmt z ⟨PUnit.unit, first, PUnit.unit, second, PUnit.unit⟩ message,
      ⟨fun _ => readPayload⟩⟩)
    else pure none

def Rin (z w : Nat) : Prop := w ≤ z

def Rout (z : Nat) (p : tree.BranchPath)
    (claim : ClosedClaim (Out z p) (family z p)) (w : Nat) : Prop :=
  w ≤ (claim.oracles ⟨(), ()⟩).val

theorem inputLaw (z w : Nat) : (inputState z).holds w ↔ Rin z w := Iff.rfl


def returnedClaim (z : Nat) (p : tree.BranchPath) (message : Fin 8) :
    ClosedClaim (Out z p) (family z p) := ⟨returnedStmt z p message, fun _ => message⟩

theorem observation (z : Nat) (firstMessage secondMessage : Fin 8)
    (first : Fin 8) (second : Fin 16) :
    closedTerminalObservation initial inputImpl Out family oracleTerminal z
      ⟨firstMessage, first, secondMessage, second, PUnit.unit⟩ =
      if first = 0 ∨ second = 0 then
        some (returnedClaim z ⟨PUnit.unit, first, PUnit.unit, second, PUnit.unit⟩ secondMessage)
      else none := by
  dsimp only [closedTerminalObservation, terminalObservation, ExecutionPath.toBranchPath,
    PFunctor.FreeM.projectPathAlong, PFunctor.FreeM.projectPathAlongLocalMap,
    PFunctor.FreeM.Displayed.LocalMap.toHom, PFunctor.FreeM.Displayed.LocalMap.toHomFun,
    tree, rounds, protocol, Protocol.oracleWith, Protocol.public, Protocol.done,
    TypeTree.oracle, TypeTree.public, TypeTree.done, runtimeLens, oracleTerminal]
  by_cases accepted : first = 0 ∨ second = 0
  all_goals simp only [accepted, ↓reduceIte, evalWithAnswerFn_pure, Option.map_none]
  rfl

theorem outputLaw (z : Nat) (path : tree.ExecutionPath) (w : Nat) :
    ((extractor z).terminalState path).holds (terminalWitness z path w) ↔
      ∃ claim, closedTerminalObservation initial inputImpl Out family oracleTerminal z path =
        some claim ∧ Rout z path.toBranchPath claim w := by
  rcases path with ⟨firstMessage, first, secondMessage, second, done⟩
  cases done
  change Fin 8 at first
  change Fin 16 at second
  change Fin 8 at secondMessage
  rw [observation]
  change ((first = 0 ∨ second = 0) ∧ w ≤ secondMessage.val) ↔
    ∃ claim, (if first = 0 ∨ second = 0 then
      some (returnedClaim z ⟨PUnit.unit, first, PUnit.unit, second, PUnit.unit⟩ secondMessage)
      else none) = some claim ∧ _
  by_cases accepted : first = 0 ∨ second = 0
  · simp only [accepted, ↓reduceIte, true_and, Option.some.injEq]
    constructor
    · intro valid
      exact ⟨_, rfl, valid⟩
    · rintro ⟨claim, same, valid⟩
      subst claim
      exact valid
  · simp [accepted]

def messages : Messages Unit rounds := ⟨(5 : Fin 8), (), (7 : Fin 8), (), PUnit.unit⟩
def path (first : Fin 8) (second : Fin 16) : tree.ExecutionPath :=
  ⟨(5 : Fin 8), first, (7 : Fin 8), second, PUnit.unit⟩

def lateKey : Key Nat Unit rounds :=
  Key.later (5 : Fin 8) () (Key.here 0 (7 : Fin 8) ())

/-- Query the later round first, twice, before completing the selected transcript. -/
def adversary : OracleComp (oracleSpec Nat Unit rounds) (Nat × Messages Unit rounds × Nat) := do
  let _ ← liftM ((oracleSpec Nat Unit rounds).query lateKey)
  let _ ← liftM ((oracleSpec Nat Unit rounds).query lateKey)
  pure ⟨0, messages, 6⟩

theorem queryBound : IsTotalQueryBound adversary 2 := by
  unfold adversary
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun _ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => trivial⟩

example (first : Fin 8) (second : Fin 16) :
    extractInputWitness inputState extractor terminalWitness 0 (path first second) 6 =
      (18 : Nat) := rfl

theorem max_errors : Finset.univ.sup errors = (1 / 8 : ENNReal) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    fin_cases j <;> norm_num [errors]
  · exact Finset.le_sup (f := errors) (Finset.mem_univ (0 : Fin 2))

theorem sum_errors : (∑ j, errors j) = (3 / 16 : ENNReal) := by
  rw [Fin.sum_univ_two]
  change (1 / 8 : ENNReal) + 1 / 16 = 3 / 16
  have equality : (1 / 8 : NNReal) + 1 / 16 = 3 / 16 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
    congrArg (fun x : NNReal => (x : ENNReal)) equality

theorem actual_nonuniform_game_bound :
    Pr{let result ← (simulateQ randomOracle
      (closedVerificationGame initial inputImpl Out family oracleTerminal adversary)).run' ∅}[
      result.1 ∈ Set.univ ∧
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness inputState extractor terminalWitness
        result.1 result.2.1 result.2.2.2)] ≤ 7 / 16 := by
  have general := stateRestoration_oracle_knowledge_soundness_nonuniform
    inputState extractor Set.univ errors (fun z _ => preserving z) (fun z _ => bounded z)
    initial inputImpl Out family oracleTerminal Rin Rout terminalWitness inputLaw outputLaw
    adversary 2 queryBound
  calc
    _ ≤ 2 * Finset.univ.sup errors + ∑ j, errors j := general
    _ = 7 / 16 := by
      rw [max_errors, sum_errors]
      have equality : (2 : NNReal) * (1 / 8) + 3 / 16 = 7 / 16 := by norm_num
      simpa only [ENNReal.coe_add, ENNReal.coe_mul,
        ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
        ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0),
        ENNReal.coe_ofNat, ENNReal.coe_one] using
        congrArg (fun x : NNReal => (x : ENNReal)) equality

example : (7 / 16 : ENNReal) < (2 + rounds.length) * (1 / 8) := by
  have better : (7 / 16 : NNReal) < 4 * (1 / 8) := by norm_num
  have coefficient : (2 : ENNReal) + rounds.length = 4 := by norm_num [rounds]
  rw [coefficient]
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one]
    using ENNReal.coe_lt_coe.mpr better

example : ∃ claim, closedTerminalObservation initial inputImpl Out family oracleTerminal 0
      (path 0 1) = some claim ∧ Rout 0 (path 0 1).toBranchPath claim 6 ∧
      ¬ Rin 0 (extractInputWitness inputState extractor terminalWitness 0 (path 0 1) 6) := by
  refine ⟨returnedClaim 0 (path 0 1).toBranchPath 7, ?_, ?_, ?_⟩
  · change closedTerminalObservation initial inputImpl Out family oracleTerminal 0
      (path 0 1) = some (returnedClaim 0
        ⟨PUnit.unit, (0 : Fin 8), PUnit.unit, (1 : Fin 16), PUnit.unit⟩ 7)
    simpa [path] using observation 0 5 7 0 1
  · change 6 ≤ (7 : Nat)
    omega
  · change ¬ (18 : Nat) ≤ 0
    omega

#eval (closedTerminalObservation initial inputImpl Out family oracleTerminal 0 (path 0 1)).map
  (fun claim => (outputValue 0 (path 0 1).toBranchPath claim.stmt,
    (claim.oracles ⟨(), ()⟩).val))
#eval (closedTerminalObservation initial inputImpl Out family oracleTerminal 0 (path 1 1)).map
  (fun claim => (outputValue 0 (path 1 1).toBranchPath claim.stmt,
    (claim.oracles ⟨(), ()⟩).val))

end Interaction.Oracle.Security.StateRestorationBudgetTest
