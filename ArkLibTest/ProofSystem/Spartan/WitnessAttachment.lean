/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.WitnessAttachment
import ArkLib.OracleReduction.Security.ChallengePresampling
import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import Mathlib.Algebra.Field.ZMod

/-! Executable witness attachment with separate public and witness padding. -/

namespace SpartanTest.WitnessAttachment

open Spartan Spartan.Realization OracleComp OracleSpec ProtocolSpec

abbrev F := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev size : R1CS.Size := ⟨3, 5, 2, by decide⟩
abbrev params : PublicParams := PublicParams.forSize size

local instance : ∀ i, OracleInterface (R1CS.OracleStatement F size i) :=
  Spartan.WitnessAttachment.sourceOracleInterface size

local instance : OracleInterface (R1CS.Witness F params.toSizeR1CS) :=
  Terminal.witnessInterface params

abbrev emptySpec : OracleSpec.{0, 0} PEmpty := []ₒ

def publicInput : R1CS.Statement F size := ![2, 1, 0]
def witness : R1CS.Witness F size := ![3, 4]

def matrices : ∀ i, R1CS.OracleStatement F size i
  | .A => fun _ j => if j.val = 0 then 1 else 0
  | .B => fun _ j => if j.val = 3 then 1 else 0
  | .C => fun _ j => if j.val = 1 then 1 else 0

example : R1CS.relation F size publicInput matrices witness := by decide

/-- The actual single-message honest prover sends its embedded witness. -/
def honestRun :=
  (simulateQ (fixedChallengeImpl (fun i => isEmptyElim i))
    ((Spartan.WitnessAttachment.oracleProver size emptySpec).run
      (publicInput, matrices) witness)).runEmpty

/-- The actual verifier accepts the honest attachment transcript. -/
def accepts : Bool :=
  ((Spartan.WitnessAttachment.oracleVerifier size emptySpec).toVerifier.run
    (publicInput, matrices) honestRun.1).run.runEmpty.isSome

/-- info: (true, [3, 4, 0, 0], [3, 4], 1, 0, 0) -/
#guard_msgs in
#eval (accepts, (List.finRange 4).map (fun i => (honestRun.1 0 i).val),
  (List.finRange 2).map (fun i =>
    ((Spartan.WitnessAttachment.rbrExtractor size emptySpec).extractIn (publicInput, matrices)
      ((Spartan.WitnessAttachment.rbrExtractor size emptySpec).extractOut
        (publicInput, matrices) honestRun.1 ()) i).val),
  (embedMatrices size matrices .B ⟨0, by decide⟩ ⟨4, by decide⟩).val,
  (embedMatrices size matrices .B ⟨0, by decide⟩ ⟨3, by decide⟩).val,
  (embedMatrices size matrices .A ⟨3, by decide⟩ ⟨0, by decide⟩).val)

/-- Execute both output query branches against the actual source and message handlers. -/
def forwardedQueries : F × F :=
  (simulateQ
    (OracleInterface.simOracle2 emptySpec matrices
      (fun i : (Spartan.WitnessAttachment.pSpec (R := F) size).MessageIdx => honestRun.1 i.val)) (do
      let a ←
        (Spartan.WitnessAttachment.outputSimulation (R := F) size emptySpec).simulateOutputQuery
        (fun i => isEmptyElim i)
        ⟨.inl .B, ((fun _ => 0), fun i => if i.val = 2 then 1 else 0)⟩
      let w ←
        (Spartan.WitnessAttachment.outputSimulation (R := F) size emptySpec).simulateOutputQuery
        (fun i => isEmptyElim i) ⟨.inr 0, fun _ => 0⟩
      pure (a, w))).runEmpty

/-- info: (1, 3) -/
#guard_msgs in
#eval (forwardedQueries.1.val, forwardedQueries.2.val)

/-- The extractor's output changes with the first coordinate of the actually sent table. -/
def sentTranscript (a : F) : (Spartan.WitnessAttachment.pSpec (R := F) size).FullTranscript :=
  fun | ⟨0, _⟩ => ![a, 4, 1, 2]

/-- info: (3, 4) -/
#guard_msgs in
#eval (((Spartan.WitnessAttachment.rbrExtractor size emptySpec).extractIn (publicInput, matrices)
  ((Spartan.WitnessAttachment.rbrExtractor size emptySpec).extractOut
    (publicInput, matrices) (sentTranscript 3) ()) 0).val,
  ((Spartan.WitnessAttachment.rbrExtractor size emptySpec).extractIn (publicInput, matrices)
  ((Spartan.WitnessAttachment.rbrExtractor size emptySpec).extractOut
    (publicInput, matrices) (sentTranscript 4) ()) 0).val)

example : ZeroCheck.inputRelation params (embedStatement size publicInput)
    (Spartan.WitnessAttachment.attachedOracles size matrices ((sentTranscript 3) 0)) := by
  apply (Spartan.WitnessAttachment.attached_relation_iff size publicInput matrices _).mpr
  decide

def emptyImpl : QueryImpl emptySpec (StateT Unit ProbComp) := fun q => isEmptyElim q

example : (Spartan.WitnessAttachment.oracleReduction (R := F) size emptySpec).perfectCompleteness
    (pure ()) emptyImpl (Spartan.WitnessAttachment.relIn size)
    (Spartan.WitnessAttachment.relOut size) :=
  Spartan.WitnessAttachment.perfectCompleteness size emptySpec (pure ()) emptyImpl

example : (Spartan.WitnessAttachment.oracleVerifier (R := F) size
      emptySpec).toVerifier.rbrKnowledgeSoundnessWith (pure ()) emptyImpl
    (Spartan.WitnessAttachment.relIn size) (Spartan.WitnessAttachment.relOut size)
    (fun _ => R1CS.Witness F params.toSizeR1CS)
    (Spartan.WitnessAttachment.rbrExtractor size emptySpec)
    (Spartan.WitnessAttachment.knowledgeStateFunction size emptySpec (pure ()) emptyImpl)
    (fun _ => 0) :=
  Spartan.WitnessAttachment.rbrKnowledgeSoundnessWith size emptySpec (pure ()) emptyImpl

end SpartanTest.WitnessAttachment
