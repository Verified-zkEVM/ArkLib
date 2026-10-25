/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.Fixture
import Lean.Compiler.IR

/-! # Actual pre-beta multiplicities, private continuations and terminal tuple authentication -/

open LogupTupleProtocolFixture
open Lean Elab Command

run_cmd do
  let full := List.range 12
  let abort := (List.range 10) ++ [11]
  unless summary 0 correctMessage == (true, 9, 17, full) &&
      summary 1 correctMessage == (true, 10, 17, full) do
    throwError "actual tuple endpoint rejected the beta0/1 compression collision transcripts"
  unless summary 0 (fun _ => affine 2 (-1)) == (false, 9, 17, full) do
    throwError "tuple endpoint accepted a forged final claim against the actual coefficient source"
  unless summary 0 (fun _ => affine 0 1) == (false, 4, 2, abort) do
    throwError "native tuple abort lost private effects or sampled a round challenge"
  let originals := [(0, 0), (1, 13), (2, 7), (3, 0), (4, 0), (5, 2),
    (6, 0), (7, 0), (8, 3), (100, 0), (101, 9)]
  unless observations 0 correctMessage ==
      [(300, 8), (300, 9), (300, 13)] ++ originals ++ [(200, 9), (201, 0), (202, 4)] do
    throwError "tuple terminal source lost coefficient order, prior mu or newest helpers"
  unless observations 1 correctMessage ==
      [(300, 1), (300, 16), (300, 8)] ++ originals ++ [(200, 16), (201, 0), (202, 9)] do
    throwError "unused zero-weight alpha pole was retried or repaired in a collision execution"
  unless endpoint 0 correctMessage == (true, full) &&
      endpoint 1 correctMessage == (true, full) &&
      endpoint 0 (fun _ => affine 2 (-1)) == (false, full) &&
      endpoint 0 (fun _ => affine 0 1) == (false, abort) do
    throwError "actual endpoint and logged tuple execution differ"
  unless decomposed 0 correctMessage == endpoint 0 correctMessage &&
      decomposed 0 (fun _ => affine 0 1) == endpoint 0 (fun _ => affine 0 1) do
    throwError "actual sender/beta-response decomposition changed execution effects"
  unless dependentRun 0 correctMessage == endpoint 0 correctMessage &&
      dependentRun 1 correctMessage == endpoint 1 correctMessage &&
      dependentRun 0 (fun _ => affine 0 1) == endpoint 0 (fun _ => affine 0 1) do
    throwError "private output depending on actual mu and beta changed tuple execution"
  unless betaAbort 0 == (none, [0, 1, 2]) do
    throwError "aborting inside the actual beta response ran alpha or later source actions"
  unless SameShape.endpoint false && !SameShape.endpoint true do
    throwError "same-shaped retained mu and later helper messages were confused"
  let zeroEffects := [0, 1, 2, 3, 4, 5, 7, 8, 11]
  unless ZeroRound.summary 0 == (true, 3, zeroEffects) &&
      ZeroRound.summary 1 == (false, 3, zeroEffects) &&
      ZeroRound.endpoint 0 == (true, zeroEffects) &&
      ZeroRound.endpoint 1 == (false, zeroEffects) do
    throwError "zero-round tuple execution skipped actual retained-source terminal authentication"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Logup.Lookup.Tuple.execute_eq_sender_beta_bind, ``realizes, ``false_lookup,
      ``actual_bind] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "tuple actual-prefix proof has an unexpected axiom: {name}"
  for name in #[``Logup.Lookup.Tuple.protocol, ``Logup.Lookup.Tuple.verifier,
      ``Logup.Lookup.Tuple.execute, ``Logup.Lookup.Tuple.uniformExecute,
      ``prover, ``endpoint, ``decomposed, ``run, ``summary, ``observations,
      ``dependentProver, ``dependentRun, ``betaAbort, ``SameShape.endpoint,
      ``ZeroRound.prover, ``ZeroRound.summary, ``ZeroRound.endpoint] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable tuple caller IR: {name}"
