/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.Probability.KoalaBear
import ArkLib.ProofSystem.ToyProblem.Codegen

/-!
# Compiled toy-problem runtime checks

These small tests exercise sextic arithmetic and the executable interleaved-RS launch cone.
They deliberately use `s = 2`; production-sized profiles are established by proof, not evaluation.
-/

namespace ToyProblemRuntime

open OracleSpec ProtocolSpec
open ToyProblem.Impl.IRS

abbrev TestField := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Four distinct test evaluation points in `ZMod 17`. -/
def testDomain : Fin 4 ↪ TestField where
  toFun i := i.val
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simpa [ZMod.val_natCast_of_lt (by omega : i.val < 17),
      ZMod.val_natCast_of_lt (by omega : j.val < 17)] using hv

theorem two_dvd_four : 2 ∣ 4 := by decide

def messageOne : Fin 4 → TestField := ![1, 2, 3, 4]

def messageTwo : Fin 4 → TestField := ![4, 3, 2, 1]

def encodedOne : Fin 4 → Fin 2 → TestField :=
  irsEncoder 4 2 two_dvd_four testDomain messageOne

def encodedTwo : Fin 4 → Fin 2 → TestField :=
  irsEncoder 4 2 two_dvd_four testDomain messageTwo

def inputStatement : ToyProblem.Spec.Statement (F := TestField) 4 ×
    (∀ i, ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField) i) :=
  ((0, 0, 0), ![encodedOne, encodedTwo])

def gamma : TestField := 3

def combinedMessage : Fin 4 → TestField := messageOne + gamma • messageTwo

/-- Execute a computation over the empty oracle interface. -/
def runEmptyOracleComp {α : Type} :
    OracleComp ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) α → α
  | .pure x => x
  | .liftBind q _ => nomatch q

/-- Run the exact straightline extractor named by the public game theorem. -/
def extractStraightline : Option (ToyProblem.Spec.Witness (F := TestField) 4) :=
  let transcript :
      (ToyProblem.Spec.pSpec (ι := Fin 4) (F := TestField) 4 1).FullTranscript :=
    fun i ↦ match i with
      | ⟨0, _⟩ => gamma
      | ⟨1, _⟩ => combinedMessage
      | ⟨2, _⟩ => fun _ ↦ 0
  runEmptyOracleComp <|
    (irsStraightlineExtractor 4 2 1 two_dvd_four testDomain
      inputStatement () transcript
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))).run

/-- The complete one-round C6.9 transcript. -/
def simplifiedTranscript :
    (ToyProblem.SimplifiedIOR.pSpec (F := TestField)).FullTranscript :=
  fun i ↦ match i with
    | ⟨0, _⟩ => gamma

/-- Run the exact C6.9 straightline extractor named by its public game theorem. -/
def extractSimplifiedStraightline :
    Option (ToyProblem.Spec.Witness (F := TestField) 4) :=
  runEmptyOracleComp <|
    (simplifiedIorStraightlineExtractor 4 2 two_dvd_four testDomain
      inputStatement combinedMessage simplifiedTranscript
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))).run

/-- Run the exact C6.9 round-by-round transition extractor. -/
def extractSimplifiedRbr : ToyProblem.Spec.Witness (F := TestField) 4 :=
  let extractor : Extractor.RoundByRound (emptySpec.{0, 0})
      (ToyProblem.Spec.Statement (F := TestField) 4 ×
        (∀ i, ToyProblem.Spec.OracleStatement
          (Fin 4) (Fin 2 → TestField) i))
      (ToyProblem.Spec.Witness (F := TestField) 4)
      (ToyProblem.SimplifiedIOR.OutputWitness (F := TestField) 4)
      (ToyProblem.SimplifiedIOR.pSpec (F := TestField))
      (simplifiedIorRbrWitMid (F := TestField) 4) :=
    simplifiedIorRbrExtractor 4 2 two_dvd_four testDomain
  extractor.extractMid 0 inputStatement simplifiedTranscript combinedMessage

/-- Query the C6.9 derived output through its VCV virtual-oracle implementation. -/
def querySimplifiedOutput (j : Fin 4) : Fin 2 → TestField :=
  let simulation : OracleOutputSimulation.{0, 0} (emptySpec.{0, 0})
      (ToyProblem.Spec.Statement (F := TestField) 4)
      (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
      (ToyProblem.SimplifiedIOR.OutputOracleStatement
        (Fin 4) (Fin 2 → TestField))
      (ToyProblem.SimplifiedIOR.pSpec (F := TestField)) :=
    ToyProblem.SimplifiedIOR.outputSimulation
      (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) 4
  letI := simulation.outputInterface
  runEmptyOracleComp <|
    simulateQ
      (OracleInterface.simOracle2 (emptySpec.{0, 0}) inputStatement.2
        simplifiedTranscript.messages)
      (simulation.simOStmt inputStatement.1 simplifiedTranscript.challenges
        ⟨0, j⟩)

def fieldArithmeticPasses : Bool :=
  let x : KoalaBear.Ext6 := CompPoly.Extension.Ext.ofFn fun i ↦ (i.val + 1 : ℕ)
  let y : KoalaBear.Ext6 := CompPoly.Extension.Ext.ofFn fun i ↦ (2 * i.val + 3 : ℕ)
  (x * y) / x == y

def encodeDecodePasses : Bool :=
  irsErasureDecodeOrZero 4 2 two_dvd_four testDomain Finset.univ encodedOne == messageOne

def rejectedErasurePasses : Bool :=
  ToyProblem.Spec.rsErasureDecoder 2 testDomain ({0} : Finset (Fin 4))
    (fun _ ↦ 0) == none

def transitionPasses : Bool :=
  let extracted := irsTransitionExtractor 4 2 two_dvd_four testDomain
    inputStatement gamma combinedMessage
  extracted 0 == messageOne && extracted 1 == messageTwo

def rejectedTransitionPasses : Bool :=
  let zeroMessage : Fin 4 → TestField := 0
  let nodes := irsGammaAgreementSet 4 2 two_dvd_four testDomain
    encodedOne encodedTwo 0 zeroMessage
  let extracted := irsTransitionExtractor 4 2 two_dvd_four testDomain
    inputStatement 0 zeroMessage
  nodes.card == 0 && extracted 0 == 0 && extracted 1 == 0

def straightlinePasses : Bool :=
  match extractStraightline with
  | some extracted => extracted 0 == messageOne && extracted 1 == messageTwo
  | none => false

def simplifiedStraightlinePasses : Bool :=
  match extractSimplifiedStraightline with
  | some extracted => extracted 0 == messageOne && extracted 1 == messageTwo
  | none => false

def simplifiedRbrPasses : Bool :=
  extractSimplifiedRbr 0 == messageOne && extractSimplifiedRbr 1 == messageTwo

def simplifiedVirtualOutputPasses : Bool :=
  querySimplifiedOutput 0 == encodedOne 0 + gamma • encodedTwo 0 &&
  querySimplifiedOutput 1 == encodedOne 1 + gamma • encodedTwo 1 &&
  querySimplifiedOutput 2 == encodedOne 2 + gamma • encodedTwo 2 &&
  querySimplifiedOutput 3 == encodedOne 3 + gamma • encodedTwo 3

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"toy-problem runtime check failed: {name}"

def run : IO Unit := do
  check "KoalaBear.Ext6 arithmetic" fieldArithmeticPasses
  check "IRS s>1 encode/decode" encodeDecodePasses
  check "rejected erasure pattern" rejectedErasurePasses
  check "dynamic agreement extraction" transitionPasses
  check "rejected dynamic agreement" rejectedTransitionPasses
  check "named straightline extractor" straightlinePasses
  check "C6.9 named straightline extractor" simplifiedStraightlinePasses
  check "C6.9 named RBR extractor" simplifiedRbrPasses
  check "C6.9 virtual output oracle" simplifiedVirtualOutputPasses
  IO.println "toy-problem runtime checks passed"

end ToyProblemRuntime

def main : IO Unit := ToyProblemRuntime.run
