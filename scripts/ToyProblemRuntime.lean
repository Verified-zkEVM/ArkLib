/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.Probability.KoalaBear
import ArkLib.OracleReduction.Cast
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.OracleReduction.Salt
import ArkLib.ProofSystem.ToyProblem.Codegen

/-!
# Compiled toy-problem runtime checks

These small tests exercise sextic arithmetic and the executable interleaved-RS launch cone.
They deliberately use `s = 2`. This is not a coverage gap: the security theorems are parametric
in the code, the radius, and the repetition count, so they already apply at production sizes and
need no evaluation. What *is* missing at production sizes is a numeric error value — that needs
the MCA/CA capacity bounds of `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean`,
which live outside the toy-problem import cone (several proven; the Johnson-range MCA input
is still an external admit).
-/

namespace ToyProblemRuntime

open OracleSpec ProtocolSpec
open ToyProblem.Impl.IRS

abbrev TestField := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/- Pin the codeword interface to coordinate queries.  Without this annotation,
Lean can also view the curried codeword type as a dependent product oracle,
which is a different (and inappropriate) query interface. -/
local instance (priority := 20000) testCodewordInterface : ∀ i, OracleInterface
    (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField) i) :=
  fun _ ↦ OracleInterface.instFunction

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
  encoder 4 2 two_dvd_four testDomain messageOne

def encodedTwo : Fin 4 → Fin 2 → TestField :=
  encoder 4 2 two_dvd_four testDomain messageTwo

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

/-- A complete C6.2 transcript with a caller-supplied prover message. -/
def testTranscript (g : Fin 4 → TestField) :
    (ToyProblem.Spec.pSpec (ι := Fin 4) (F := TestField) 4 1).FullTranscript :=
  fun i ↦ match i with
    | ⟨0, _⟩ => gamma
    | ⟨1, _⟩ => g
    | ⟨2, _⟩ => fun _ ↦ 0

/-- Run the exact straightline extractor named by the public game theorem. -/
def extractStraightline : Option (ToyProblem.Spec.Witness (F := TestField) 4) :=
  runEmptyOracleComp <|
    (straightlineExtractor 4 2 1 two_dvd_four testDomain
      inputStatement () (testTranscript combinedMessage)
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))
        ([] : QueryLog ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}))).run

/-- Execute the actual C6.2 deciding verifier, including both guards and the
spot-check loop, against a complete transcript. -/
def runOracleVerifier (g : Fin 4 → TestField) :
    Option (ToyProblem.Spec.OutputStatement ×
      ∀ i, ToyProblem.Spec.OutputOracleStatement i) :=
  let verifier := ToyProblem.Spec.oracleVerifier
    (k := 4) (t := 1) (encoder 4 2 two_dvd_four testDomain)
  runEmptyOracleComp <| simulateQ
    (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
      (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
      ToyProblem.Spec.instOracleInterfaceOracleStatement _
      (ToyProblem.Spec.pSpec (ι := Fin 4) (F := TestField) 4 1).Message
      (ToyProblem.Spec.instOracleInterfaceMessagePSpec 4 1) inputStatement.2
      (testTranscript g).messages)
    (verifier.toVerifier.run inputStatement (testTranscript g)).run

/-- The complete one-round C6.9 transcript. -/
def simplifiedTranscript :
    (ToyProblem.SimplifiedIOR.pSpec (F := TestField)).FullTranscript :=
  fun i ↦ match i with
    | ⟨0, _⟩ => gamma

/-- Run the exact C6.9 straightline extractor named by its public game theorem. -/
def extractSimplifiedStraightline :
    Option (ToyProblem.Spec.Witness (F := TestField) 4) :=
  runEmptyOracleComp <|
    (simplifiedStraightlineExtractor 4 2 two_dvd_four testDomain
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
      (simplifiedRbrWitMid (F := TestField) 4) :=
    simplifiedRbrExtractor 4 2 two_dvd_four testDomain
  extractor.extractMid 0 inputStatement simplifiedTranscript combinedMessage

/-- Query the C6.9 derived output through its VCV virtual-oracle implementation. -/
def querySimplifiedOutput (j : Fin 4) : Fin 2 → TestField :=
  let verifier := ToyProblem.SimplifiedIOR.oracleVerifier
    (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4)
  runEmptyOracleComp <|
    simulateQ
      (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
        (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
        ToyProblem.Spec.instOracleInterfaceOracleStatement _
        (ToyProblem.SimplifiedIOR.pSpec (F := TestField)).Message
        ToyProblem.SimplifiedIOR.instOracleInterfaceMessagePSpec
        inputStatement.2 simplifiedTranscript.messages)
      (verifier.simulateOutputQuery simplifiedTranscript.challenges ⟨0, j⟩)

/-- The complete C6.9 transcript after applying the standard salt adapter. -/
def simplifiedSaltedTranscript :
    ((ToyProblem.SimplifiedIOR.pSpec (F := TestField)).addSalt
      (fun _ ↦ Unit)).FullTranscript :=
  fun i ↦ match i with
    | ⟨0, _⟩ => gamma

/-- Query C6.9 after salting; this is the regression for adapter preservation. -/
def querySimplifiedSaltedOutput (j : Fin 4) : Fin 2 → TestField :=
  letI saltedMessageInterface : ∀ i, OracleInterface
      (((ToyProblem.SimplifiedIOR.pSpec (F := TestField)).addSalt
        (fun _ ↦ Unit)).Message i) :=
    @ProtocolSpec.instAddSaltMessage 1
      (ToyProblem.SimplifiedIOR.pSpec (F := TestField)) (fun _ ↦ Unit)
      ToyProblem.SimplifiedIOR.instOracleInterfaceMessagePSpec
  let verifier := (ToyProblem.SimplifiedIOR.oracleVerifier
    (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4)).addSalt
      (fun _ ↦ Unit)
  runEmptyOracleComp <|
    simulateQ
      (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
        (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
        ToyProblem.Spec.instOracleInterfaceOracleStatement _
        ((ToyProblem.SimplifiedIOR.pSpec (F := TestField)).addSalt
          (fun _ ↦ Unit)).Message
        saltedMessageInterface inputStatement.2 simplifiedSaltedTranscript.messages)
      (verifier.simulateOutputQuery simplifiedSaltedTranscript.challenges ⟨0, j⟩)

/-- Query C6.9 after a protocol cast.  Even an identity cast exercises the
dependent interface-coherence argument used by the generic adapter. -/
def simplifiedCastedVerifier : OracleVerifier []ₒ
    (ToyProblem.Spec.Statement (F := TestField) 4)
    (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
    (ToyProblem.SimplifiedIOR.OutputStatement (F := TestField) 4)
    (ToyProblem.SimplifiedIOR.OutputOracleStatement
      (Fin 4) (Fin 2 → TestField))
    (ToyProblem.SimplifiedIOR.pSpec (F := TestField)) :=
  OracleVerifier.cast
    (pSpec₁ := ToyProblem.SimplifiedIOR.pSpec (F := TestField))
    (pSpec₂ := ToyProblem.SimplifiedIOR.pSpec (F := TestField))
    rfl rfl (fun _ ↦ rfl)
    (ToyProblem.SimplifiedIOR.oracleVerifier
      (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4))

def querySimplifiedCastedOutput (j : Fin 4) : Fin 2 → TestField :=
  runEmptyOracleComp <|
    simulateQ
      (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
        (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
        ToyProblem.Spec.instOracleInterfaceOracleStatement _
        (ToyProblem.SimplifiedIOR.pSpec (F := TestField)).Message
        ToyProblem.SimplifiedIOR.instOracleInterfaceMessagePSpec
        inputStatement.2 simplifiedTranscript.messages)
      (simplifiedCastedVerifier.simulateOutputQuery
        simplifiedTranscript.challenges ⟨0, j⟩)

/-- Identity executable lens used to exercise virtual-oracle preservation by
`OracleVerifier.liftContext` without changing the toy instance. -/
def simplifiedIdentityLens : OracleStatement.ExecutableLens
    (ToyProblem.Spec.Statement (F := TestField) 4)
    (ToyProblem.SimplifiedIOR.OutputStatement (F := TestField) 4)
    (ToyProblem.Spec.Statement (F := TestField) 4)
    (ToyProblem.SimplifiedIOR.OutputStatement (F := TestField) 4)
    (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
    (ToyProblem.SimplifiedIOR.OutputOracleStatement
      (Fin 4) (Fin 2 → TestField))
    (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
    (ToyProblem.SimplifiedIOR.OutputOracleStatement
      (Fin 4) (Fin 2 → TestField)) where
  projStmt := id
  materializeInput := fun _ oStmt ↦ oStmt
  simulateInput := fun _ ↦ QueryImpl.id'
    [ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField)]ₒ
  simulateInput_eq := by intros; rfl
  liftStmt := fun _ stmt ↦ stmt
  materializeOutput := fun _ oStmt ↦ oStmt
  simulateOutput := fun q ↦ QueryImpl.id'
    ([ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField)]ₒ +
      [ToyProblem.SimplifiedIOR.OutputOracleStatement
        (Fin 4) (Fin 2 → TestField)]ₒ) (Sum.inr q)
  simulateOutput_eq := by intros; rfl

def simplifiedLiftOutput : OracleVerifier.LiftContextOutput simplifiedIdentityLens
    (ToyProblem.SimplifiedIOR.oracleVerifier
      (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4)) where
  outputOracle := (ToyProblem.SimplifiedIOR.oracleVerifier
    (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4)).outputOracle
  materialize_eq := by
    intros
    simp only [simplifiedIdentityLens, OracleVerifier.materializeOutput]

/-- Query C6.9 after an executable context lift. -/
def querySimplifiedLiftedOutput (j : Fin 4) : Fin 2 → TestField :=
  let verifier := OracleVerifier.liftContext simplifiedIdentityLens
    (ToyProblem.SimplifiedIOR.oracleVerifier
      (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4))
    simplifiedLiftOutput
  runEmptyOracleComp <|
    simulateQ
      (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
        (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
        ToyProblem.Spec.instOracleInterfaceOracleStatement _
        (ToyProblem.SimplifiedIOR.pSpec (F := TestField)).Message
        ToyProblem.SimplifiedIOR.instOracleInterfaceMessagePSpec
        inputStatement.2 simplifiedTranscript.messages)
      (verifier.simulateOutputQuery simplifiedTranscript.challenges ⟨0, j⟩)

def simplifiedSeqStmt : Fin 2 → Type :=
  Fin.cases (ToyProblem.Spec.Statement (F := TestField) 4)
    (fun _ ↦ ToyProblem.SimplifiedIOR.OutputStatement (F := TestField) 4)

def simplifiedSeqOIdx : Fin 2 → Type :=
  Fin.cases (Fin 2) (fun _ ↦ Fin 1)

def simplifiedSeqOStmt : (i : Fin 2) → simplifiedSeqOIdx i → Type :=
  Fin.cases (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
    (fun _ ↦ ToyProblem.SimplifiedIOR.OutputOracleStatement
      (Fin 4) (Fin 2 → TestField))

local instance simplifiedSeqOInterface : ∀ i j,
    OracleInterface (simplifiedSeqOStmt i j) :=
  Fin.cases ToyProblem.Spec.instOracleInterfaceOracleStatement
    (fun _ ↦ ToyProblem.SimplifiedIOR.instOracleInterfaceOutputOracleStatement)

def simplifiedSeqRounds : Fin 1 → ℕ :=
  Fin.cases 1 (fun i ↦ i.elim0)

def simplifiedSeqPSpec : (i : Fin 1) → ProtocolSpec (simplifiedSeqRounds i) :=
  Fin.cases (ToyProblem.SimplifiedIOR.pSpec (F := TestField))
    (fun i ↦ i.elim0)

local instance simplifiedSeqMessageInterface : ∀ i j,
    OracleInterface ((simplifiedSeqPSpec i).Message j) :=
  Fin.cases ToyProblem.SimplifiedIOR.instOracleInterfaceMessagePSpec
    (fun i ↦ i.elim0)

def simplifiedSeqVerifiers : (i : Fin 1) → OracleVerifier []ₒ
    (simplifiedSeqStmt i.castSucc) (simplifiedSeqOStmt i.castSucc)
    (simplifiedSeqStmt i.succ) (simplifiedSeqOStmt i.succ)
    (simplifiedSeqPSpec i) :=
  Fin.cases
    (ToyProblem.SimplifiedIOR.oracleVerifier
      (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4))
    (fun i ↦ i.elim0)

/-- The one-stage generic sequential composer.  Its output is still C6.9's
virtual oracle, so this tests the `seqCompose` path rather than only `append`. -/
def simplifiedSequentialVerifier : OracleVerifier []ₒ
    (ToyProblem.Spec.Statement (F := TestField) 4)
    (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
    (ToyProblem.SimplifiedIOR.OutputStatement (F := TestField) 4)
    (ToyProblem.SimplifiedIOR.OutputOracleStatement
      (Fin 4) (Fin 2 → TestField))
    (ToyProblem.SimplifiedIOR.pSpec (F := TestField)) :=
  OracleVerifier.seqCompose simplifiedSeqStmt simplifiedSeqOStmt simplifiedSeqVerifiers

def querySimplifiedSequentialOutput (j : Fin 4) : Fin 2 → TestField :=
  runEmptyOracleComp <|
    simulateQ
      (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
        (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
        ToyProblem.Spec.instOracleInterfaceOracleStatement _
        (ToyProblem.SimplifiedIOR.pSpec (F := TestField)).Message
        ToyProblem.SimplifiedIOR.instOracleInterfaceMessagePSpec
        inputStatement.2 simplifiedTranscript.messages)
      (simplifiedSequentialVerifier.simulateOutputQuery
        simplifiedTranscript.challenges ⟨0, j⟩)

/- A downstream verifier that consumes C6.9's output oracle by querying one
coordinate.  Its own output-oracle family is empty. -/
def downstreamCoordinateVerifier (j : Fin 4) :
    OracleVerifier []ₒ
      (ToyProblem.SimplifiedIOR.OutputStatement (F := TestField) 4)
      (ToyProblem.SimplifiedIOR.OutputOracleStatement
        (Fin 4) (Fin 2 → TestField))
      (Fin 2 → TestField) ToyProblem.Spec.OutputOracleStatement !p[] where
  verify := fun _ _ ↦ do
    let value : Fin 2 → TestField ← liftM <| OracleSpec.query
      (show ([]ₒ +
        ([ToyProblem.SimplifiedIOR.OutputOracleStatement
          (Fin 4) (Fin 2 → TestField)]ₒ + [!p[].Message]ₒ)).Domain from
        Sum.inr (Sum.inl ⟨0, j⟩))
    pure value
  outputOracle := .inl {
    embed := ⟨fun i ↦ i.elim0, fun i _ _ ↦ i.elim0⟩
    hEq := fun i ↦ i.elim0
    outputInterface_heq := fun i ↦ i.elim0 }

def emptyTranscript : (!p[]).FullTranscript := fun i ↦ i.elim0

def simplifiedAppendedTranscript :
    ((ToyProblem.SimplifiedIOR.pSpec (F := TestField)) ++ₚ !p[]).FullTranscript :=
  simplifiedTranscript ++ₜ emptyTranscript

local instance simplifiedAppendedMessageInterface : ∀ i, OracleInterface
    (((ToyProblem.SimplifiedIOR.pSpec (F := TestField)) ++ₚ !p[]).Message i) :=
  @instOracleInterfaceMessageAppend 1 0
    (ToyProblem.SimplifiedIOR.pSpec (F := TestField)) !p[]
    ToyProblem.SimplifiedIOR.instOracleInterfaceMessagePSpec (by infer_instance)

/- Execute an actual `OracleVerifier.append`: the second verifier's input
query must be routed through C6.9's virtual output implementation. -/
def querySimplifiedOutputAfterAppend (j : Fin 4) : Option (Fin 2 → TestField) :=
  let verifier := OracleVerifier.append
    (ToyProblem.SimplifiedIOR.oracleVerifier
      (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4))
    (downstreamCoordinateVerifier j)
  let result := verifier.toVerifier.verify inputStatement simplifiedAppendedTranscript
  (runEmptyOracleComp result.run).map Prod.fst

/- A zero-round downstream verifier whose identity output is deliberately
represented as virtual.  This forces append to compose one virtual output
implementation with another virtual output implementation. -/
def downstreamVirtualVerifier : OracleVerifier []ₒ
    (ToyProblem.SimplifiedIOR.OutputStatement (F := TestField) 4)
    (ToyProblem.SimplifiedIOR.OutputOracleStatement
      (Fin 4) (Fin 2 → TestField))
    (ToyProblem.SimplifiedIOR.OutputStatement (F := TestField) 4)
    (ToyProblem.SimplifiedIOR.OutputOracleStatement
      (Fin 4) (Fin 2 → TestField)) !p[] where
  verify := fun stmt _ ↦ pure stmt
  outputOracle := .inr {
    materializeOutput := fun _ oStmt _ ↦ oStmt
    simulateOutputQuery := fun _ q ↦ by
      rcases q with ⟨i, j⟩
      change OracleComp
        ([]ₒ + ([ToyProblem.SimplifiedIOR.OutputOracleStatement
          (Fin 4) (Fin 2 → TestField)]ₒ + [!p[].Message]ₒ))
        (Fin 2 → TestField)
      exact (liftM
        (liftM (([ToyProblem.SimplifiedIOR.OutputOracleStatement
          (Fin 4) (Fin 2 → TestField)]ₒ).query ⟨i, j⟩) :
            OracleComp
              ([ToyProblem.SimplifiedIOR.OutputOracleStatement
                (Fin 4) (Fin 2 → TestField)]ₒ + [!p[].Message]ₒ) _) :
          OracleComp
            ([]ₒ + ([ToyProblem.SimplifiedIOR.OutputOracleStatement
              (Fin 4) (Fin 2 → TestField)]ₒ + [!p[].Message]ₒ)) _)
    simulateOutputQuery_eq := by
      intro _ oStmt messages q
      rcases q with ⟨i, j⟩
      change simulateQ (OracleInterface.simOracle2 []ₒ oStmt messages)
          (liftM (liftM (([ToyProblem.SimplifiedIOR.OutputOracleStatement
            (Fin 4) (Fin 2 → TestField)]ₒ).query ⟨i, j⟩))) = _
      calc
        _ = liftM (simulateQ
            (OracleInterface.simOracle0
              (ToyProblem.SimplifiedIOR.OutputOracleStatement
                (Fin 4) (Fin 2 → TestField)) oStmt)
            (([ToyProblem.SimplifiedIOR.OutputOracleStatement
              (Fin 4) (Fin 2 → TestField)]ₒ).query ⟨i, j⟩)) := by
          exact OracleVerifier.simulateQ_addLift_add_liftM_left
            (QueryImpl.id []ₒ)
            (OracleInterface.simOracle0
              (ToyProblem.SimplifiedIOR.OutputOracleStatement
                (Fin 4) (Fin 2 → TestField)) oStmt)
            (OracleInterface.simOracle0 !p[].Message messages)
            (([ToyProblem.SimplifiedIOR.OutputOracleStatement
              (Fin 4) (Fin 2 → TestField)]ₒ).query ⟨i, j⟩)
        _ = _ := rfl }

def querySimplifiedVirtualOutputAfterAppend (j : Fin 4) : Fin 2 → TestField :=
  let verifier := OracleVerifier.append
    (ToyProblem.SimplifiedIOR.oracleVerifier
      (ι := Fin 4) (F := TestField) (A := Fin 2 → TestField) (k := 4))
    downstreamVirtualVerifier
  runEmptyOracleComp <|
    simulateQ
      (@OracleInterface.simOracle2 _ (emptySpec.{0, 0}) _
        (ToyProblem.Spec.OracleStatement (Fin 4) (Fin 2 → TestField))
        ToyProblem.Spec.instOracleInterfaceOracleStatement _
        ((ToyProblem.SimplifiedIOR.pSpec (F := TestField)) ++ₚ !p[]).Message
        simplifiedAppendedMessageInterface inputStatement.2
        simplifiedAppendedTranscript.messages)
      (verifier.simulateOutputQuery simplifiedAppendedTranscript.challenges ⟨0, j⟩)

def fieldArithmeticPasses : Bool :=
  let x : KoalaBear.Ext6 := CompPoly.Extension.Ext.ofFn fun i ↦ (i.val + 1 : ℕ)
  let y : KoalaBear.Ext6 := CompPoly.Extension.Ext.ofFn fun i ↦ (2 * i.val + 3 : ℕ)
  (x * y) / x == y

def encodeDecodePasses : Bool :=
  erasureDecodeOrZero 4 2 two_dvd_four testDomain Finset.univ encodedOne == messageOne

def rejectedErasurePasses : Bool :=
  ToyProblem.Spec.rsErasureDecoder 2 testDomain ({0} : Finset (Fin 4))
    (fun _ ↦ 0) == none

def transitionPasses : Bool :=
  let extracted := transitionExtractor 4 2 two_dvd_four testDomain
    inputStatement gamma combinedMessage
  extracted 0 == messageOne && extracted 1 == messageTwo

def rejectedTransitionPasses : Bool :=
  let zeroMessage : Fin 4 → TestField := 0
  let nodes := gammaAgreementSet 4 2 two_dvd_four testDomain
    encodedOne encodedTwo 0 zeroMessage
  let extracted := transitionExtractor 4 2 two_dvd_four testDomain
    inputStatement 0 zeroMessage
  nodes.card == 0 && extracted 0 == 0 && extracted 1 == 0

def straightlinePasses : Bool :=
  match extractStraightline with
  | some extracted => extracted 0 == messageOne && extracted 1 == messageTwo
  | none => false

def verifierAcceptRejectPasses : Bool :=
  (runOracleVerifier combinedMessage).isSome &&
    !(runOracleVerifier 0).isSome

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

def simplifiedSaltedVirtualOutputPasses : Bool :=
  querySimplifiedSaltedOutput 0 == encodedOne 0 + gamma • encodedTwo 0 &&
  querySimplifiedSaltedOutput 1 == encodedOne 1 + gamma • encodedTwo 1 &&
  querySimplifiedSaltedOutput 2 == encodedOne 2 + gamma • encodedTwo 2 &&
  querySimplifiedSaltedOutput 3 == encodedOne 3 + gamma • encodedTwo 3

def simplifiedCastedVirtualOutputPasses : Bool :=
  querySimplifiedCastedOutput 0 == encodedOne 0 + gamma • encodedTwo 0 &&
  querySimplifiedCastedOutput 1 == encodedOne 1 + gamma • encodedTwo 1 &&
  querySimplifiedCastedOutput 2 == encodedOne 2 + gamma • encodedTwo 2 &&
  querySimplifiedCastedOutput 3 == encodedOne 3 + gamma • encodedTwo 3

def simplifiedLiftedVirtualOutputPasses : Bool :=
  querySimplifiedLiftedOutput 0 == encodedOne 0 + gamma • encodedTwo 0 &&
  querySimplifiedLiftedOutput 1 == encodedOne 1 + gamma • encodedTwo 1 &&
  querySimplifiedLiftedOutput 2 == encodedOne 2 + gamma • encodedTwo 2 &&
  querySimplifiedLiftedOutput 3 == encodedOne 3 + gamma • encodedTwo 3

def simplifiedSequentialVirtualOutputPasses : Bool :=
  querySimplifiedSequentialOutput 0 == encodedOne 0 + gamma • encodedTwo 0 &&
  querySimplifiedSequentialOutput 1 == encodedOne 1 + gamma • encodedTwo 1 &&
  querySimplifiedSequentialOutput 2 == encodedOne 2 + gamma • encodedTwo 2 &&
  querySimplifiedSequentialOutput 3 == encodedOne 3 + gamma • encodedTwo 3

def simplifiedAppendVirtualOutputPasses : Bool :=
  querySimplifiedOutputAfterAppend 0 == some (encodedOne 0 + gamma • encodedTwo 0) &&
  querySimplifiedOutputAfterAppend 1 == some (encodedOne 1 + gamma • encodedTwo 1) &&
  querySimplifiedOutputAfterAppend 2 == some (encodedOne 2 + gamma • encodedTwo 2) &&
  querySimplifiedOutputAfterAppend 3 == some (encodedOne 3 + gamma • encodedTwo 3)

def simplifiedVirtualOnVirtualAppendPasses : Bool :=
  querySimplifiedVirtualOutputAfterAppend 0 == encodedOne 0 + gamma • encodedTwo 0 &&
  querySimplifiedVirtualOutputAfterAppend 1 == encodedOne 1 + gamma • encodedTwo 1 &&
  querySimplifiedVirtualOutputAfterAppend 2 == encodedOne 2 + gamma • encodedTwo 2 &&
  querySimplifiedVirtualOutputAfterAppend 3 == encodedOne 3 + gamma • encodedTwo 3

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"toy-problem runtime check failed: {name}"

def run : IO Unit := do
  check "KoalaBear.Ext6 arithmetic" fieldArithmeticPasses
  check "IRS s>1 encode/decode" encodeDecodePasses
  check "rejected erasure pattern" rejectedErasurePasses
  check "dynamic agreement extraction" transitionPasses
  check "rejected dynamic agreement" rejectedTransitionPasses
  check "named straightline extractor" straightlinePasses
  check "C6.2 deciding verifier accept/reject" verifierAcceptRejectPasses
  check "C6.9 named straightline extractor" simplifiedStraightlinePasses
  check "C6.9 named RBR extractor" simplifiedRbrPasses
  check "C6.9 virtual output oracle" simplifiedVirtualOutputPasses
  check "C6.9 virtual output oracle after addSalt" simplifiedSaltedVirtualOutputPasses
  check "C6.9 virtual output oracle after cast" simplifiedCastedVirtualOutputPasses
  check "C6.9 virtual output oracle after liftContext" simplifiedLiftedVirtualOutputPasses
  check "C6.9 virtual output oracle through seqCompose" simplifiedSequentialVirtualOutputPasses
  check "C6.9 virtual output oracle through append" simplifiedAppendVirtualOutputPasses
  check "C6.9 virtual-on-virtual output through append" simplifiedVirtualOnVirtualAppendPasses
  IO.println "toy-problem runtime checks passed"

end ToyProblemRuntime

def main : IO Unit := ToyProblemRuntime.run
