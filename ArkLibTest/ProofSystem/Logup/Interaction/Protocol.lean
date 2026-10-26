/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLibTest.ProofSystem.Logup.Interaction.Fixture
import Lean.Compiler.IR

/-! # Actual weighted prefix, native suffix, and terminal source execution -/

open LogupRuntimeFixture
open Lean Elab Command

run_cmd do
  let full := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  let abort := [0, 1, 2, 3, 4, 5, 6, 8]
  unless summary 0 (affine 0 0) == (true, 81, 8, full) do
    throwError "weighted honest execution changed"
  unless summary 0 (affine 2 (-1)) == (false, 81, 8, full) do
    throwError "weighted forged final claim was not rejected"
  unless summary 1 (affine 0 0) == (false, 81, 8, full) do
    throwError "weighted endpoint failed to bind the actual helper"
  unless summary 0 (affine 0 1) == (false, 76, 2, abort) do
    throwError "weighted public abort lost private effects or drew another challenge"
  let honest := [(5, 0), (5, 0), (5, 0), (0, 0), (1, 0), (2, 1), (3, -1), (4, 0)]
  unless observations 0 (affine 0 0) == honest do
    throwError "weighted terminal check did not query actual original/helper sources"
  let forged := [(5, -1), (5, 1), (5, 9), (0, 0), (1, 0), (2, 1), (3, -1), (4, 0)]
  unless observations 0 (affine 2 (-1)) == forged do
    throwError "weighted forged transcript source answers changed"
  unless observations 0 (affine 0 1) == [(5, 1), (5, 1)] do
    throwError "weighted abort performed terminal input queries"
  unless endpoint 0 (affine 0 0) == (true, full) do
    throwError "named execute endpoint differs from logged honest execution"
  unless endpoint 0 (affine 2 (-1)) == (false, full) do
    throwError "named execute endpoint accepted the forgery"
  unless endpoint 1 (affine 0 0) == (false, full) do
    throwError "named execute endpoint ignored the mutated helper"
  unless endpoint 0 (affine 0 1) == (false, abort) do
    throwError "named execute endpoint abort effects changed"

run_cmd do
  unless ZeroRound.summary 0 == (true, 37, 5, [0, 1, 2, 4, 5]) do
    throwError "zero-round prefix skipped actual terminal authentication"
  unless ZeroRound.summary 1 == (false, 37, 5, [0, 1, 2, 4, 5]) do
    throwError "zero-round prefix failed to bind its retained helper"

run_cmd do
  for name in #[``Logup.Interaction.prefixVerifier, ``Logup.Interaction.suffixVerifier,
      ``Logup.Interaction.reductionVerifier, ``Logup.Interaction.verifier,
      ``Logup.Interaction.execute, ``Logup.Interaction.uniformExecute, ``prover, ``run,
      ``observed, ``observations, ``endpoint, ``uniformEndpoint, ``ZeroRound.run,
      ``ZeroRound.summary] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing weighted protocol executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless (← collectAxioms ``realizes).all allowed.contains do
    throwError "weighted fixture source realization has an unexpected axiom"
