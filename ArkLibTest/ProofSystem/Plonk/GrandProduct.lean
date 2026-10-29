/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Plonk.GrandProduct.Reduction
import ArkLib.ProofSystem.Plonk.Batch.Reduction
import ArkLib.ProofSystem.Plonk.Quotient.Reduction
import Mathlib.Algebra.Field.ZMod

/-! # Executable Plonk stage checks over a prime field -/

namespace ArkLibTest.PlonkGrandProduct

open Plonk OracleSpec OracleComp ProtocolSpec

private abbrev F := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private theorem primitive : IsPrimitiveRoot (16 : F) 2 := by
  apply (IsPrimitiveRoot.iff (by decide)).mpr
  constructor
  · decide
  · intro l hl hlt
    have h : l = 1 := by omega
    subst l
    decide

private def domain : EvaluationDomain F 2 := EvaluationDomain.primitiveRoot 16 primitive

private def cosets : CosetLabels domain where
  k₁ := 2
  k₂ := 3
  k₁_ne_zero := by decide
  k₂_ne_zero := by decide
  disjoint_left_right := Set.disjoint_range_iff.mpr (by decide)
  disjoint_left_output := Set.disjoint_range_iff.mpr (by decide)
  disjoint_right_output := Set.disjoint_range_iff.mpr (by decide)

private def circuit : ConstraintSystem F 2 2 := ![Gate.add 0 0 1, Gate.add 0 0 1]

private def wires (c : Fin 3) : GeneratorBatch.Poly F 2 :=
  ⟨CompPoly.CPolynomial.C (![1, 1, 2] c), by simp⟩

private def publicInput : GeneratorBatch.Poly F 2 := ⟨0, by simp⟩

private def noQueries : QueryImpl []ₒ Id := fun q => nomatch q

private def grandProductChallenges : QueryImpl
    ([]ₒ + [(GrandProduct.pSpec F 2).Challenge]ₒ'challengeOracleInterface) Id
  | .inl q => nomatch q
  | .inr ⟨⟨0, _⟩, _⟩ => (1, 4)
  | .inr ⟨⟨1, h⟩, _⟩ => nomatch h

private def grandProductRun :=
  (simulateQ grandProductChallenges
    ((GrandProduct.oracleProver 16 primitive (by decide) circuit cosets publicInput []ₒ).run
      ((), wires) ())).run

private def grandProductVerified :=
  (simulateQ noQueries
    ((GrandProduct.oracleVerifier 16 primitive (by decide)
      circuit cosets publicInput []ₒ).toVerifier.verify ((), wires) grandProductRun.1).run).run

private def batchChallenges : QueryImpl
    ([]ₒ + [(Batch.pSpec F).Challenge]ₒ'challengeOracleInterface) Id
  | .inl q => nomatch q
  | .inr ⟨⟨0, _⟩, _⟩ => pure (3 : F)

private def batchRun :=
  (simulateQ batchChallenges
    ((Batch.oracleProver (F := F) (n := 2) []ₒ).run grandProductRun.2.1 ())).run

private def batchVerified :=
  (simulateQ noQueries
    ((Batch.oracleVerifier (F := F) (n := 2) []ₒ).toVerifier.verify
      grandProductRun.2.1 batchRun.1).run).run

private def grandProductVirtualQuery (j : Fin 3) (z : F) : F :=
  (simulateQ noQueries <| simulateQ
    (OracleInterface.simOracle2 []ₒ wires grandProductRun.1.messages)
    ((GrandProduct.oracleVerifier 16 primitive (by decide)
      circuit cosets publicInput []ₒ).simulateOutputQuery
      grandProductRun.1.challenges ⟨.inr (.inr j), z⟩)).run

private def batchVirtualQuery (z : F) : F :=
  (simulateQ noQueries <| simulateQ
    (OracleInterface.simOracle2 []ₒ grandProductRun.2.1.2 batchRun.1.messages)
    ((Batch.oracleVerifier (F := F) (n := 2) []ₒ).simulateOutputQuery
      batchRun.1.challenges ⟨.inr (), z⟩)).run

private def quotientChallenges : QueryImpl
    ([]ₒ + [(Quotient.pSpec 16 primitive (by decide)).Challenge]ₒ'challengeOracleInterface) Id
  | .inl q => nomatch q
  | .inr ⟨⟨0, h⟩, _⟩ => nomatch h
  | .inr ⟨⟨1, _⟩, _⟩ => pure (5 : F)

private def quotientRun :=
  (simulateQ quotientChallenges
    ((Quotient.oracleReduction 16 primitive (by decide) []ₒ).prover.run batchRun.2.1 ())).run

private def quotientVerified :=
  (simulateQ noQueries
    ((Quotient.oracleVerifier 16 primitive (by decide) []ₒ).toVerifier.verify
      batchRun.2.1 quotientRun.1).run).run

private def forgedOracles : ∀ i, Batch.OStmtOut F 2 i
  | .inl i => batchRun.2.1.2 (.inl i)
  | .inr _ => ⟨CompPoly.CPolynomial.C 1, by simp⟩

private def forgedTranscript : (Quotient.pSpec 16 primitive (by decide)).FullTranscript
  | ⟨0, _⟩ => ⟨0, by simp⟩
  | ⟨1, _⟩ => (5 : F)

private def forgedVerified :=
  (simulateQ noQueries
    ((Quotient.oracleVerifier 16 primitive (by decide) []ₒ).toVerifier.verify
      ((1, 4), forgedOracles) forgedTranscript).run).run

private def runtimeChecks : IO Unit := do
  unless (List.ofFn (fun c => (wires c).val.evalHorner 1) = [1, 1, 2]) do
    throw (IO.userError "Unexpected wire values")
  unless ((show F × F from grandProductRun.1 0) = (1, 4)) do
    throw (IO.userError "Unexpected joint challenge")
  unless (grandProductRun.1 1).val.evalHorner 1 = 1 do
    throw (IO.userError "Unexpected accumulator normalization")
  let some gp := grandProductVerified
    | throw (IO.userError "Grand-product verifier rejected the honest transcript")
  unless (gp.1 = (1, 4)) do
    throw (IO.userError "Grand-product verifier lost its challenge")
  unless (∀ j : Fin 3, ∀ i : Fin 2,
      (gp.2 (.inr (.inr j))).val.evalHorner (domain.node i) = 0) do
    throw (IO.userError "Honest grand-product residual did not vanish")
  unless (∀ j : Fin 3, ∀ z : F, grandProductVirtualQuery j z =
      (gp.2 (.inr (.inr j))).val.evalHorner z) do
    throw (IO.userError "Virtual grand-product query disagreed with its polynomial")
  let some batched := batchVerified
    | throw (IO.userError "Batch verifier rejected the honest transcript")
  unless (∀ i : Fin 2, (batched.2 (.inr ())).val.evalHorner (domain.node i) = 0) do
    throw (IO.userError "Honest batch did not vanish")
  unless (∀ z : F, (batched.2 (.inr ())).val.evalHorner z =
      (gp.2 (.inr (.inr 0))).val.evalHorner z +
      3 * (gp.2 (.inr (.inr 1))).val.evalHorner z +
      9 * (gp.2 (.inr (.inr 2))).val.evalHorner z) do
    throw (IO.userError "Unexpected batch evaluation")
  unless (∀ z : F, batchVirtualQuery z = (batched.2 (.inr ())).val.evalHorner z) do
    throw (IO.userError "Virtual batch query disagreed with its polynomial")
  unless quotientVerified.isSome do
    throw (IO.userError "Quotient verifier rejected the honest transcript")
  unless forgedVerified.isNone do
    throw (IO.userError "Terminal guard accepted a forged constant batch and zero quotient")
  IO.println "Plonk grand-product, batch and quotient runtime checks passed."

/-- info: Plonk grand-product, batch and quotient runtime checks passed. -/
#guard_msgs in
#eval runtimeChecks

end ArkLibTest.PlonkGrandProduct
