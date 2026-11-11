/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Sumcheck.First
import ArkLib.ProofSystem.Spartan.Sumcheck.Second
import ArkLib.OracleReduction.Security.ChallengePresampling
import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import Mathlib.Algebra.Field.ZMod

/-! Executable honest virtual sumcheck rounds on a satisfied two-row R1CS instance. -/

namespace SpartanTest.VirtualSumcheck

open Spartan Spartan.Realization OracleComp OracleSpec ProtocolSpec
open scoped NNReal

abbrev F := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev params : PublicParams := ⟨1, 1, 0, by decide⟩

def publicInput : R1CS.Statement F params.toSizeR1CS := fun _ => 1
def witness : R1CS.Witness F params.toSizeR1CS := fun _ => 2

def matrices : ∀ i, R1CS.OracleStatement F params.toSizeR1CS i
  | .A | .B => fun a b => if a.val = b.val then 1 else 0
  | .C => fun a b => if b.val = 0 then if a.val = 0 then 1 else 4 else 0

def oracles : ∀ i, OracleStatement (R := F) params i
  | .inl i => matrices i
  | .inr _ => witness

example : R1CS.relation F params.toSizeR1CS publicInput matrices witness := by decide

def firstInput : FirstSumcheck.Statement (R := F) params := (fun _ => 3, publicInput)

def firstChallenges : (Sumcheck.Spec.pSpec F 3 params.ℓ_m).Challenges := by
  intro i
  have hi : i = (⟨⟨1, by decide⟩, rfl⟩ : (Sumcheck.Spec.pSpec F 3 params.ℓ_m).ChallengeIdx) := by
    fin_cases i
    rfl
  subst i
  change F
  exact 2

/-- Execute the actual first honest prover with its row challenge fixed to two. -/
def firstRun :=
  (simulateQ (fixedChallengeImpl firstChallenges)
    ((FirstSumcheck.oracleProver params []ₒ).run (firstInput, oracles) ())).runEmpty

/-- The second input batches the three true row evaluations at the first returned point. -/
def secondInput : Batching.Statement (R := F) params :=
  Batching.batch params
    (Evaluation.values params firstRun.2.1.1 oracles, firstRun.2.1.1) (fun _ => 1)

def secondChallenges : (Sumcheck.Spec.pSpec F 2 params.ℓ_n).Challenges := by
  intro i
  have hi : i = (⟨⟨1, by decide⟩, rfl⟩ : (Sumcheck.Spec.pSpec F 2 params.ℓ_n).ChallengeIdx) := by
    fin_cases i
    rfl
  subst i
  change F
  exact 3

/-- Execute the actual second honest prover with its column challenge fixed to three. -/
def secondRun :=
  (simulateQ (fixedChallengeImpl secondChallenges)
    ((SecondSumcheck.oracleProver params []ₒ).run (secondInput, oracles) ())).runEmpty

/-- info: (1, 3, 3) -/
#guard_msgs in
#eval (firstRun.2.1.1.e.val, secondInput.c.val, secondRun.2.1.1.e.val)

abbrev paramsTwo : PublicParams := ⟨1, 2, 1, by decide⟩

def publicInputTwo : R1CS.Statement F paramsTwo.toSizeR1CS := ![2, 1]
def witnessTwo : R1CS.Witness F paramsTwo.toSizeR1CS := ![3, 4]

def matricesTwo : ∀ i, R1CS.OracleStatement F paramsTwo.toSizeR1CS i
  | .A => fun _ j => if j.val = 0 then 1 else 0
  | .B => fun _ j => if j.val = 2 then 1 else 0
  | .C => fun _ j => if j.val = 1 then 1 else 0

def oraclesTwo : ∀ i, OracleStatement (R := F) paramsTwo i
  | .inl i => matricesTwo i
  | .inr _ => witnessTwo

example : R1CS.relation F paramsTwo.toSizeR1CS publicInputTwo matricesTwo witnessTwo := by decide

def secondInputTwo : Batching.Statement (R := F) paramsTwo :=
  Batching.batch paramsTwo
    ((fun | .A => 2 | .B => 3 | .C => 1), ⟨publicInputTwo, 0, 0, 0⟩) (fun _ => 1)

def challengesTwo : (Sumcheck.Spec.pSpec F 2 paramsTwo.ℓ_n).Challenges := fun i =>
  have hi : (Sumcheck.Spec.pSpec F 2 paramsTwo.ℓ_n).Challenge i = F := by
    fin_cases i <;> rfl
  cast hi.symm (if i.val.val = 1 then (3 : F) else 4)

/-- Two actual honest rounds exercise recursive message and challenge reindexing. -/
def secondRunTwo :=
  (simulateQ (fixedChallengeImpl challengesTwo)
    ((SecondSumcheck.oracleProver paramsTwo []ₒ).run (secondInputTwo, oraclesTwo) ())).runEmpty

/-- info: (3, 3, 4) -/
#guard_msgs in
#eval (secondRunTwo.2.1.1.e.val, (secondRunTwo.2.1.1.r_y 0).val,
  (secondRunTwo.2.1.1.r_y 1).val)

/-- Execute the first oracle verifier on the actual honest transcript. -/
def acceptsFirst : Bool :=
  ((FirstSumcheck.oracleVerifier params []ₒ).toVerifier.run
    (firstInput, oracles) firstRun.1).run.runEmpty.isSome

/-- Execute the second oracle verifier on the actual honest transcript. -/
def acceptsSecond (s : Batching.Statement (R := F) params) : Bool :=
  ((SecondSumcheck.oracleVerifier params []ₒ).toVerifier.run
    (s, oracles) secondRun.1).run.runEmpty.isSome

/-- Alter the first challenge while retaining both polynomials of the two-round transcript. -/
def alteredTranscriptTwo : (Sumcheck.Spec.pSpec F 2 paramsTwo.ℓ_n).FullTranscript :=
  Function.update secondRunTwo.1 ⟨1, by decide⟩ (by change F; exact 0)

/-- Execute both recursive verifier rounds using the supplied transcript. -/
def acceptsTwo (tr : (Sumcheck.Spec.pSpec F 2 paramsTwo.ℓ_n).FullTranscript) : Bool :=
  ((SecondSumcheck.oracleVerifier paramsTwo []ₒ).toVerifier.run
    (secondInputTwo, oraclesTwo) tr).run.runEmpty.isSome

/-- info: (true, true, false, true, false) -/
#guard_msgs in
#eval (acceptsFirst, acceptsSecond secondInput,
  acceptsSecond {secondInput with c := secondInput.c + 1},
  acceptsTwo secondRunTwo.1, acceptsTwo alteredTranscriptTwo)

def emptyImpl : QueryImpl []ₒ (StateT Unit ProbComp) := fun q => isEmptyElim q

example : (FirstSumcheck.oracleReduction (R := F) params []ₒ).perfectCompleteness
    (pure ()) emptyImpl (FirstSumcheck.relIn params) (FirstSumcheck.relOut params) :=
  FirstSumcheck.perfectCompleteness params []ₒ (pure ()) emptyImpl

example : (SecondSumcheck.oracleReduction (R := F) params []ₒ).perfectCompleteness
    (pure ()) emptyImpl (SecondSumcheck.relIn params) (SecondSumcheck.relOut params) :=
  SecondSumcheck.perfectCompleteness params []ₒ (pure ()) emptyImpl

example : (FirstSumcheck.oracleVerifier (R := F) params
      []ₒ).toVerifier.rbrKnowledgeSoundness
      (pure ()) emptyImpl
      (FirstSumcheck.relIn params) (FirstSumcheck.relOut params)
      (fun _ => (3 : ℝ≥0) / Fintype.card F) :=
  FirstSumcheck.rbrKnowledgeSoundness params []ₒ

example : (SecondSumcheck.oracleVerifier (R := F) params
      []ₒ).toVerifier.rbrKnowledgeSoundness
      (pure ()) emptyImpl
      (SecondSumcheck.relIn params) (SecondSumcheck.relOut params)
      (fun _ => (2 : ℝ≥0) / Fintype.card F) :=
  SecondSumcheck.rbrKnowledgeSoundness params []ₒ (pure ()) emptyImpl

example : AllQueriesSatisfy
    ((FirstSumcheck.oracleVerifier params []ₒ).verify firstInput firstChallenges).run
    (fun q => ∃ i, q = Sum.inr (Sum.inr i)) :=
  FirstSumcheck.sumcheck_verifier_no_inputPolynomial_queries params []ₒ firstInput firstChallenges

end SpartanTest.VirtualSumcheck
