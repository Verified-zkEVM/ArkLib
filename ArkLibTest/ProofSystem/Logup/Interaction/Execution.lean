/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Interaction.Execution
import ArkLibTest.ProofSystem.Logup.Interaction.Fixture
import Lean.Compiler.IR

/-! # Whole-prover execution laws preserve actual private effects and aborts -/

open Interaction.Oracle OracleComp OracleSpec Logup.Interaction
open LogupRuntimeFixture
open Lean Elab Command

namespace LogupExecutionFixture

set_option backward.isDefEq.respectTransparency false in
/-- Compile the right side of the exact whole-prover execution theorem independently. -/
def decomposedRun (h : E) (q : LogupRuntimeFixture.Message) : OracleComp ambientSpec Bool := do
  let prefixP := splitPrefixProver 1 1 2 ambientSpec
    (Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ ↦ (() : Unit))
      (prover privateEffect h q))
  let alpha ← event 0
  let helperStage ← prefixP alpha
  let sent ← helperStage
  let joint ← jointDraw
  let continuation ← sent.2 joint
  Sumcheck.Interaction.Computable.executeWithFinalCheck E 1 4 ambientSpec (event 7) [0, 1]
    1 0 (Nat.zero_add 1) (family (E := E) 1 2).spec.toPFunctor
    (VirtualOracle.id (family (E := E) 1 2)) (zeroStatement E 1)
    ((qView embedding 1 2 1 cfg.groups alpha joint.1 joint.2 2 access view).eval
      (Access.extendImpl access (helperInterface (E := E) 1 1) impl sent.1))
    (OutP := fun _ ↦ Unit) continuation

set_option backward.isDefEq.respectTransparency false in
theorem decomposedRun_eq (h : E) (q : LogupRuntimeFixture.Message) :
    decomposedRun h q = execute embedding 1 2 2 cfg ambientSpec (event 0) jointDraw (event 7)
      access view impl (prover privateEffect h q) :=
  (execute_eq_prefix_binds embedding 1 2 2 cfg ambientSpec (event 0) jointDraw (event 7)
    access view impl (prover privateEffect h q)).symm

def decomposedEndpoint (h : E) (q : LogupRuntimeFixture.Message) : Bool × List Nat :=
  (simulateQ logger (decomposedRun h q)).run []

/-- The helper oracle remains present even when the native suffix has zero rounds. -/
def zeroDecomposedRun (h : E) : OracleComp ambientSpec Bool := do
  let prefixP := splitPrefixProver 0 1 2 ambientSpec
    (Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ ↦ (() : Unit))
      (ZeroRound.prover h))
  let alpha ← event 0
  let helperStage ← prefixP alpha
  let sent ← helperStage
  let joint ← ZeroRound.jointDraw
  let continuation ← sent.2 joint
  Sumcheck.Interaction.Computable.executeWithFinalCheck E 0 4 ambientSpec (event 7) [0, 1]
    0 0 (Nat.zero_add 0) (family (E := E) 0 2).spec.toPFunctor
    (VirtualOracle.id (family (E := E) 0 2)) (zeroStatement E 0)
    ((qView embedding 0 2 1 ZeroRound.cfg.groups alpha joint.1 joint.2 2
      ZeroRound.access ZeroRound.view).eval
      (Access.extendImpl ZeroRound.access (helperInterface (E := E) 0 1) ZeroRound.impl sent.1))
    (OutP := fun _ ↦ Unit) continuation

theorem zeroDecomposedRun_eq (h : E) :
    zeroDecomposedRun h = execute embedding 0 2 2 ZeroRound.cfg ambientSpec (event 0)
      ZeroRound.jointDraw (event 7) ZeroRound.access ZeroRound.view ZeroRound.impl
      (ZeroRound.prover h) :=
  (execute_eq_prefix_binds embedding 0 2 2 ZeroRound.cfg ambientSpec (event 0)
    ZeroRound.jointDraw (event 7) ZeroRound.access ZeroRound.view ZeroRound.impl
    (ZeroRound.prover h)).symm

def zeroDecomposedEndpoint (h : E) : Bool × List Nat :=
  (simulateQ logger (zeroDecomposedRun h)).run []

run_cmd do
  let full := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  let abort := [0, 1, 2, 3, 4, 5, 6, 8]
  unless decomposedEndpoint 0 (affine 0 0) == (true, full) do
    throwError "prefix projection changed honest execution or private effect order"
  unless decomposedEndpoint 0 (affine 2 (-1)) == (false, full) do
    throwError "decomposed execution accepted a forged final source value"
  unless decomposedEndpoint 1 (affine 0 0) == (false, full) do
    throwError "decomposed execution forgot the actual retained helper"
  unless decomposedEndpoint 0 (affine 0 1) == (false, abort) do
    throwError "private return erasure skipped abort effects or drew another challenge"
  unless zeroDecomposedEndpoint 0 == (true, [0, 1, 2, 4, 5]) do
    throwError "zero-round prefix execution changed the actual receiver/sender bind order"
  unless zeroDecomposedEndpoint 1 == (false, [0, 1, 2, 4, 5]) do
    throwError "zero-round execution dropped terminal retained-helper authentication"

run_cmd do
  for name in #[``splitPrefixProver, ``decomposedRun, ``decomposedEndpoint,
      ``zeroDecomposedRun, ``zeroDecomposedEndpoint] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing execution-law external caller IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``execute_eq_accepts_closed, ``execute_eq_prefix_run, ``execute_eq_eraseOutput,
      ``execute_eq_prefix_binds, ``decomposedRun_eq, ``zeroDecomposedRun_eq] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "execution-law proof has an unexpected axiom: {name}"

end LogupExecutionFixture
