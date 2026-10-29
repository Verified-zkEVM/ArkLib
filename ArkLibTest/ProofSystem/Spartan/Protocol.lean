/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Basic
import ArkLib.OracleReduction.Security.ChallengePresampling
import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import Mathlib.Algebra.Field.ZMod

/-! End-to-end execution of Spartan on a satisfied two-row R1CS instance over `ZMod 5`. -/

namespace SpartanTest.Protocol

open Spartan Spartan.Realization OracleComp OracleSpec ProtocolSpec

abbrev F := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev size : R1CS.Size := ⟨2, 2, 1, by decide⟩
abbrev params : PublicParams := PublicParams.forSize size
abbrev emptySpec : OracleSpec.{0, 0} PEmpty := []ₒ

local instance : ∀ i, OracleInterface (R1CS.OracleStatement F size i) :=
  WitnessAttachment.sourceOracleInterface size

def publicInput : R1CS.Statement F size := fun _ => 1
def witness : R1CS.Witness F size := fun _ => 2

def matrices : ∀ i, R1CS.OracleStatement F size i
  | .A | .B => fun a b => if a.val = b.val then 1 else 0
  | .C => fun a b => if b.val = 0 then if a.val = 0 then 1 else 4 else 0

example : R1CS.relation F size publicInput matrices witness := by decide

/-- Non-Boolean sumcheck challenges and three distinct batching coefficients. -/
def challenges : (Spartan.pSpec (R := F) size).Challenges
  | ⟨⟨0, _⟩, h⟩ => nomatch h
  | ⟨⟨1, _⟩, _⟩ => fun _ => 2
  | ⟨⟨2, _⟩, h⟩ => nomatch h
  | ⟨⟨3, _⟩, _⟩ => (3 : F)
  | ⟨⟨4, _⟩, h⟩ => nomatch h
  | ⟨⟨5, _⟩, _⟩ => fun | .A => 1 | .B => 2 | .C => 3
  | ⟨⟨6, _⟩, h⟩ => nomatch h
  | ⟨⟨7, _⟩, _⟩ => (4 : F)

/-- Run the composed honest prover, including witness attachment and both sumchecks. -/
def honestRun :=
  (simulateQ (fixedChallengeImpl challenges)
    ((Spartan.oracleReduction size emptySpec).prover.run
      (publicInput, matrices) witness)).runEmpty

/-- Run the composed oracle verifier on the actual honest transcript. -/
def accepts : Bool :=
  ((Spartan.oracleReduction size emptySpec).verifier.toVerifier.run
    (publicInput, matrices) honestRun.1).run.runEmpty.isSome

/-- Run the certified executable extractor on the actual honest transcript. -/
def recoveredWitness : Option (R1CS.Witness F size) :=
  ((Spartan.straightlineExtractor size emptySpec)
    (publicInput, matrices) () honestRun.1 [] []).run.runEmpty

/-- info: (true, some 2) -/
#guard_msgs in
#eval (accepts, recoveredWitness.map fun w => (w 0).val)

end SpartanTest.Protocol
