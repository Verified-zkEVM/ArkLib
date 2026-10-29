/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Plonk.Assembly.CircuitExtraction
import Mathlib.Algebra.Field.ZMod

/-! # Executable end-to-end Plonk check over a prime field -/

namespace ArkLibTest.PlonkAssembly

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

private def circuit : ConstraintSystem F 2 1 := ![Gate.add 0 0 1]

private def publicInput : Fin 1 → F := fun _ => 1

private def witness : Fin (2 - 1) → F := fun _ => 2

private theorem satisfied : relation circuit 1 (by decide) publicInput witness := by
  intro i
  fin_cases i
  change (1 : F) * 1 + 1 * 1 + (-1) * 2 + 0 * (1 * 1) + 0 = 0
  decide

private def wires := Assembly.honestWires domain (by decide) circuit
  (show 1 ≤ 2 by decide) publicInput witness

private def reduction := Assembly.Circuit.oracleReduction 16 primitive (by decide)
  circuit (show 1 ≤ 2 by decide) publicInput cosets []ₒ

private def initialStatement : Unit × ∀ i, SendWitness.OStmtIn i :=
  ((), fun i => Fin.elim0 i)

private def noQueries : QueryImpl []ₒ Id := fun q => nomatch q

private def challenges : QueryImpl
    ([]ₒ + [(Assembly.pSpec 16 primitive (by decide)).Challenge]ₒ'challengeOracleInterface) Id
  | .inl q => nomatch q
  | .inr ⟨⟨⟨0, _⟩, h⟩, _⟩ => nomatch h
  | .inr ⟨⟨⟨1, _⟩, _⟩, _⟩ => (1, 4)
  | .inr ⟨⟨⟨2, _⟩, h⟩, _⟩ => nomatch h
  | .inr ⟨⟨⟨3, _⟩, _⟩, _⟩ => (3 : F)
  | .inr ⟨⟨⟨4, _⟩, h⟩, _⟩ => nomatch h
  | .inr ⟨⟨⟨5, _⟩, _⟩, _⟩ => (5 : F)

private def honestRun :=
  (simulateQ challenges (reduction.prover.run initialStatement wires)).run

private def verified :=
  (simulateQ noQueries
    (reduction.verifier.toVerifier.verify initialStatement honestRun.1).run).run

private def extracted :=
  (simulateQ noQueries
    ((Assembly.Circuit.transcriptExtractor 16 primitive (by decide) circuit
      (show 1 ≤ 2 by decide) publicInput []ₒ)
        initialStatement () honestRun.1 [] []).run).run

private def runtimeChecks : IO Unit := do
  unless verified.isSome do
    throw (IO.userError "Composed Plonk verifier rejected the honest circuit transcript")
  unless ((show F × F from honestRun.1 ⟨1, by decide⟩) = (1, 4)) do
    throw (IO.userError "Unexpected joint grand-product challenge")
  unless ((show F from honestRun.1 ⟨3, by decide⟩) = 3 ∧
      (show F from honestRun.1 ⟨5, by decide⟩) = 5) do
    throw (IO.userError "Unexpected batching or evaluation challenge")
  unless (∀ c : Fin 3, ∀ z : F,
      (honestRun.1 ⟨0, by decide⟩ c).val.evalHorner z = (wires c).val.evalHorner z) do
    throw (IO.userError "Initial transcript table differs from the honest witness encoding")
  let decoded := Assembly.circuitExtractor domain circuit (show 1 ≤ 2 by decide)
    publicInput (honestRun.1 ⟨0, by decide⟩)
  unless decoded 0 = 2 do
    throw (IO.userError "Revealed polynomial table did not decode to the circuit witness")
  let some recovered := extracted
    | throw (IO.userError "Circuit transcript extractor failed")
  unless recovered 0 = 2 do
    throw (IO.userError "Ordinary circuit extractor returned the wrong private witness")
  IO.println "Plonk assembly acceptance and circuit extraction runtime checks passed."

/-- info: Plonk assembly acceptance and circuit extraction runtime checks passed. -/
#guard_msgs in
#eval runtimeChecks

end ArkLibTest.PlonkAssembly
