/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.StateRestorationResources
import ArkLib.Interaction.Oracle.Security.KnowledgeResources.Composition
import ArkLibTest.Data.OracleComp.AddProgram

/-!
A two-round closed-oracle client with distinct challenge alphabets and local errors 1/8
and 1/16. Input statements range over Nat. The actual terminal output reads the second oracle
message; named backward extraction adds both actual payloads to the supplied witness.

Each stage of that extractor has a named measured program and budget, and every budget is at most
one. The two message stages each perform one charged addition. The two challenge stages return the
later witness or its first component; copying and projection are uncharged under this accounting,
so they request no instruction. The theorem
`MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform` packages the
client's security bound with a derived full-path count bound from the stage budgets and depth.

Composing those instruction programs along an actual path retains both additions and computes
the same input witness used in the game. Path preparation and the terminal witness-carrier
conversion remain uncharged.
-/

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec AddProgramTest
open Interaction.Oracle.TypeTree
open Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security.StateRestorationBudgetTest


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
  all_goals simp only [accepted, ↓reduceIte]
  all_goals rfl

theorem outputLaw (z : Nat) (path : tree.ExecutionPath) (w : Nat) :
    ((extractor z).terminalState path).holds (terminalWitness z path w) ↔
      ∃ claim, closedTerminalObservation initial inputImpl Out family oracleTerminal z path =
        some claim ∧ Rout z path.toBranchPath claim w := by
  rcases path with ⟨firstMessage, first, secondMessage, second, done⟩
  cases done
  change Fin 8 at first
  change Fin 16 at second
  change Fin 8 at secondMessage
  rw [observation z firstMessage secondMessage first second]
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

section Measured

/-- The first stage adds the actual first oracle message to the later witness. -/
def firstMessageStage (z : Nat) : BudgetedProgram (extractor z).stageMap (Unit → Nat) :=
  ⟨addCountProgram fun x => (x.2, x.1.val), 1, addCountProgram_realizes _,
    addCountProgram_costAtMost_one _⟩

/-- The first challenge stage returns the later witness itself; copying is uncharged. -/
def firstChallengeStage (z : Nat) (firstMessage : Fin 8) :
    BudgetedProgram ((extractor z) firstMessage).2.2.stageMap (Unit → Nat) :=
  BudgetedProgram.ofFun _

/-- The second stage adds the actual second oracle message to the later witness. -/
def secondMessageStage (z : Nat) (firstMessage first : Fin 8) :
    BudgetedProgram (((extractor z) firstMessage).2.2 first).2.2.stageMap (Unit → Nat) :=
  ⟨addCountProgram fun x => (x.2, x.1.val), 1, addCountProgram_realizes _,
    addCountProgram_costAtMost_one _⟩

/-- The second challenge stage returns the first component of the later witness; projection is
uncharged. -/
def secondChallengeStage (z : Nat) (firstMessage first secondMessage : Fin 8) :
    BudgetedProgram ((((extractor z) firstMessage).2.2 first).2.2 secondMessage).2.2.stageMap
      (Unit → Nat) :=
  BudgetedProgram.ofFun _

/-- The challenge stages are the identity and the first projection. -/
example (z : Nat) (firstMessage first secondMessage : Fin 8) (w : Nat) (second : Fin 16)
    (w' : Nat × Unit) :
    ((extractor z) firstMessage).2.2.stageMap ⟨first, w⟩ = w ∧
      ((((extractor z) firstMessage).2.2 first).2.2 secondMessage).2.2.stageMap ⟨second, w'⟩ =
        w'.1 :=
  ⟨rfl, rfl⟩

/-- The measured stages of the named extractor. -/
def stages (z : Nat) : (extractor z).MeasuredStages (Unit → Nat) :=
  ⟨firstMessageStage z, fun firstMessage =>
    ⟨firstChallengeStage z firstMessage, fun first =>
      ⟨secondMessageStage z firstMessage first, fun secondMessage =>
        ⟨secondChallengeStage z firstMessage first secondMessage, fun _ => PUnit.unit⟩⟩⟩⟩

/-- The stages have budgets one, zero, one and zero along every path. -/
example (z : Nat) (firstMessage first secondMessage : Fin 8) :
    (stages z).1.budget = 1 ∧ ((stages z).2 firstMessage).1.budget = 0 ∧
      (((stages z).2 firstMessage).2 first).1.budget = 1 ∧
      ((((stages z).2 firstMessage).2 first).2 secondMessage).1.budget = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every stage costs at most one addition. -/
theorem stages_budgetAtMost_one (z : Nat) : (stages z).BudgetAtMost 1 :=
  ⟨le_rfl, fun _ => ⟨(fun _ => Nat.zero_le 1), fun _ =>
    ⟨le_rfl, fun _ => ⟨(fun _ => Nat.zero_le 1), fun _ => trivial⟩⟩⟩⟩

/-- Each round has one charged message stage and an uncharged challenge stage. -/
theorem stages_protocolBudgetAtMost (z : Nat) : (stages z).ProtocolBudgetAtMost 1 0 :=
  ⟨le_rfl, fun _ => ⟨le_rfl, fun _ => ⟨le_rfl, fun _ => ⟨le_rfl, fun _ => trivial⟩⟩⟩⟩

/-- The common stage bound still gives the coarser four-node bound. -/
example (z : Nat) (path : tree.ExecutionPath) :
    ((stages z).programAlong path).program.CostAtMost ((2 * rounds.length) • (1 : Unit → Nat)) :=
  (stages z).programAlong_costAtMost_protocol (stages_budgetAtMost_one z) path

/-- The actual composition of the client's four named stage programs. -/
def extractionProgram (z : Nat) (path : tree.ExecutionPath) :
    BudgetedProgram ((extractor z).extractWitness path) (Unit → Nat) :=
  (stages z).programAlong path

/-- The composed program has declared budget two along every path. -/
theorem extractionProgram_budget (z : Nat) (path : tree.ExecutionPath) :
    (extractionProgram z path).budget = 2 := rfl

/-- Every permitted execution of the composed program has declared cost at most two. -/
theorem extractionProgram_costAtMost (z : Nat) (path : tree.ExecutionPath) :
    (extractionProgram z path).program.CostAtMost 2 := by
  simpa only [extractionProgram_budget] using (extractionProgram z path).costAtMost

/-- The composed instruction program returns exactly the game's named extracted witness. -/
example (z : Nat) (path : tree.ExecutionPath)
    (witness : ((extractor z).terminalState path).Witness) :
    (extractionProgram z path).program.run witness = (extractor z).extractWitness path witness :=
  (stages z).run_programAlong path witness

/-- After the uncharged carrier conversion, the composed run is the game's input witness. -/
theorem extractionProgram_run_inputWitness (z : Nat) (path : tree.ExecutionPath)
    (witness : Nat) :
    (extractionProgram z path).program.run (terminalWitness z path witness) =
      extractInputWitness inputState extractor terminalWitness z path witness :=
  (stages z).run_programAlong path (terminalWitness z path witness)

/-- The deterministic run retains the instruction charges of both message stages. -/
def extractionObservation (z : Nat) (path : tree.ExecutionPath)
    (witness : ((extractor z).terminalState path).Witness) : Nat × Nat :=
  let program := (extractionProgram z path).program
  (simulateQ ((program.answer (program.view witness)).withAddCost program.cost)
    (program.program (program.view witness))).runAdd.run.map id (fun count => count ())

/-- Every typed path and terminal witness records the two actual addition instructions. -/
theorem extractionObservation_cost (z : Nat) (path : tree.ExecutionPath)
    (witness : ((extractor z).terminalState path).Witness) :
    (extractionObservation z path witness).2 = 2 := by
  rcases path with ⟨firstMessage, first, secondMessage, second, done⟩
  rfl

/-- Erasing the recorded cost returns the same extracted witness on every typed path. -/
theorem extractionObservation_result (z : Nat) (path : tree.ExecutionPath)
    (witness : ((extractor z).terminalState path).Witness) :
    (extractionObservation z path witness).1 = (extractor z).extractWitness path witness := by
  rcases path with ⟨firstMessage, first, secondMessage, second, done⟩
  rfl

/-- The actual full-path writer executes its suffix before the root's named stage program. -/
theorem extractionProgram_writer (z : Nat) (path : tree.ExecutionPath) :
    let suffix := ((stages z).2 path.1).programAlong path.2
    let rootProgram := (stages z).1.program.contramap
      (fun witness : ((extractor z) path.1).1.Witness => ⟨path.1, witness⟩)
    ∀ view : suffix.program.View,
      simulateQ (((extractionProgram z path).program.answer view).withAddCost
        (extractionProgram z path).program.cost) ((extractionProgram z path).program.program view) =
      (do
        let witness ← simulateQ ((suffix.program.answer view).withAddCost suffix.program.cost)
          (suffix.program.program view)
        simulateQ ((rootProgram.answer (rootProgram.view witness)).withAddCost rootProgram.cost)
          (rootProgram.program (rootProgram.view witness))) := by
  dsimp only
  intro view
  exact MeasuredProgram.simulateQ_withAddCost_comp
    ((stages z).1.program.contramap
      (fun witness : ((extractor z) path.1).1.Witness => ⟨path.1, witness⟩))
    (((stages z).2 path.1).programAlong path.2).program view

/-- Check the generated extraction run and the charges of both message stages. -/
private def checkExtractionObservation : IO Unit := do
  let observed := extractionObservation 0 (path 0 1) ((6 : Nat), ())
  unless observed == (18, 2) do
    throw (IO.userError s!"Unexpected composed extraction result or instruction count: {observed}")
  IO.println "Composed extraction returns witness 18 with two charged additions."

/-- info: Composed extraction returns witness 18 with two charged additions. -/
#guard_msgs in
#eval checkExtractionObservation

/-- Complete extraction on a path is the composition of the four stage maps. -/
example (z : Nat) (path : tree.ExecutionPath) (w : ((extractor z).terminalState path).Witness) :
    (extractor z).extractWitness path w = (extractor z).stageMap ⟨path.1,
      ((extractor z) path.1).2.2.extractWitness path.2 w⟩ :=
  RoundExtractor.extractWitness_oracle _ path w

/-- The knowledge certificate of the named extractor, with its measured stages. -/
noncomputable def measuredCertificate (z : Nat) :
    MeasuredKnowledgeCertificate Unit tree roles (inputState z) where
  extractor := extractor z
  challenges := roundErrorSchedule rounds errors
  prover_preserving := preserving z
  local_bound := bounded z
  stages := stages z

/-- The measured certificate's extractor is the client's named extractor. -/
example (z : Nat) : (measuredCertificate z).toKnowledgeCertificate.extractor = extractor z := rfl

/-- The library bridge identifies the composed program with the original game's input witness. -/
example (z : Nat) (path : tree.ExecutionPath) (witness : Nat) :
    ((measuredCertificate z).stages.programAlong path).program.run
        (terminalWitness z path witness) =
      extractInputWitness inputState (fun z => (measuredCertificate z).extractor)
        terminalWitness z path witness :=
  MeasuredKnowledgeCertificate.run_programAlong_terminalWitness inputState measuredCertificate
    terminalWitness z path witness

/-- The packaged theorem derives a complete-path instruction bound from local stage budgets. -/
example : Pr{let result ← (simulateQ randomOracle
      (closedVerificationGame initial inputImpl Out family oracleTerminal adversary)).run' ∅}[
      result.1 ∈ Set.univ ∧
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 (extractInputWitness inputState (fun z => (measuredCertificate z).extractor)
        terminalWitness result.1 result.2.1 result.2.2.2)] ≤
      2 * Finset.univ.sup errors + ∑ j, errors j ∧
      ∀ z ∈ Set.univ, ∀ path,
        (∀ witness, ((measuredCertificate z).stages.programAlong path).program.run
            (terminalWitness z path witness) =
          extractInputWitness inputState (fun z => (measuredCertificate z).extractor)
            terminalWitness z path witness) ∧
        ((measuredCertificate z).stages.programAlong path).program.CostAtMost 2 :=
  MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform inputState
    measuredCertificate Set.univ errors (fun _ _ => rfl) (fun _ => 1) (fun _ => 0)
    (fun z _ => stages_protocolBudgetAtMost z) initial inputImpl Out family oracleTerminal
    Rin Rout terminalWitness inputLaw outputLaw adversary 2 queryBound

/-- The same named extractor has the closed-game bound and the composed instruction budget. -/
example : Pr{let result ← (simulateQ randomOracle
      (closedVerificationGame initial inputImpl Out family oracleTerminal adversary)).run' ∅}[
      result.1 ∈ Set.univ ∧
      (∃ claim, result.2.2.1 = some claim ∧
        Rout result.1 result.2.1.toBranchPath claim result.2.2.2) ∧
      ¬ Rin result.1 ((extractionProgram result.1 result.2.1).program.run
        (terminalWitness result.1 result.2.1 result.2.2.2))] ≤ 7 / 16 ∧
      ∀ z path, (extractionProgram z path).program.CostAtMost 2 := by
  constructor
  · simpa only [extractionProgram_run_inputWitness] using actual_nonuniform_game_bound
  · exact extractionProgram_costAtMost

end Measured

end Interaction.Oracle.Security.StateRestorationBudgetTest
