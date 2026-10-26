/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Resources
import ArkLib.Interaction.Oracle.PhasedExecution
import ArkLibTest.ProofSystem.Sumcheck.Interaction.Resources
import Lean.Compiler.IR

/-! # Actual terminal binding preserves complete packets and ordered source traces -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Sumcheck.Interaction
namespace LoggedTerminalTests
open TerminalCheckTest
abbrev p := Computable.protocol F 1 1
abbrev oldOut := TerminalClaim p inputSpec.toPFunctor (fun _ => Native.Core.FinalStatement F 1)
  (fun _ => MultivariateRound.polynomialFamily F 1 1)
abbrev finalAccess (path : p.tree.BranchPath) :=
  TypeTree.accessAfter p.tree p.oracles inputSpec.toPFunctor path

def tail (path : p.tree.BranchPath) (out : oldOut path) :
    OracleComp (ambientSpec + ofPFunctor (finalAccess path)) F := do
  match out with
  | none => OracleComp.liftComp (event 2) (ambientSpec + ofPFunctor (finalAccess path))
  | some claim =>
    let first : F ← liftM (claim.oracles.query ⟨(), claim.stmt.challenges⟩)
    let marker ← OracleComp.liftComp (event 0) (ambientSpec + ofPFunctor (finalAccess path))
    let second : F ← liftM (claim.oracles.query ⟨(), claim.stmt.challenges⟩)
    return first + second + marker

def mappedVerifier : Verifier.Strategy ambientSpec p.tree p.roles p.oracles inputSpec.toPFunctor
    (fun _ => F) :=
  Verifier.Fragment.mapOutput ambientSpec (fun path action => action >>= tail path)
    (Computable.verifier F 1 1 ambientSpec (event 1) [0,1] 1 0 rfl
      inputSpec.toPFunctor originalView initial)

abbrev result := LoggedResult p.tree p.oracles inputSpec.toPFunctor
  NativeResourcesTests.Private (fun _ => F)
abbrev packet := LoggedObservation p.tree p.oracles inputSpec.toPFunctor
  NativeResourcesTests.Private (fun _ => F)

def run (q : Sumcheck.Impl.Representation.Message F 1) : OracleComp ambientSpec result :=
  executeStrategiesLogged ambientSpec p.tree p.roles p.oracles inputSpec.toPFunctor inputImpl
    (NativeResourcesTests.dependentProver q) mappedVerifier

def decomposed (q : Sumcheck.Impl.Representation.Message F 1) : OracleComp ambientSpec packet := do
  let old ← NativeResourcesTests.bare q
  let terminal ← (simulateQ
    (Verifier.loggedLiftAccessImpl ambientSpec (finalAccess old.path.toBranchPath)
      (old.path.closingImpl p.oracles inputSpec.toPFunctor inputImpl))
    (tail old.path.toBranchPath old.verifierOut)).run
  return ⟨old.path, old.proverOut, terminal.1, old.sourceLog ++ terminal.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem packet_eq (q : Sumcheck.Impl.Representation.Message F 1) :
    LoggedResult.observe <$> run q = decomposed q := by
  have h := executeStrategiesLogged_bindTerminal ambientSpec p.tree p.roles p.oracles
      inputSpec.toPFunctor inputImpl oldOut (fun _ => F) NativeResourcesTests.Private
      (NativeResourcesTests.dependentProver q)
      (Computable.verifier F 1 1 ambientSpec (event 1) [0,1] 1 0 rfl
        inputSpec.toPFunctor originalView initial) tail
  simp only [run, mappedVerifier, decomposed, NativeResourcesTests.bare] at h ⊢
  exact h

def summarize (observed : packet × List Nat) : F × List (String × F) × List Nat × List Nat :=
  (observed.1.2.2.1, encodeSource observed.1.1 observed.1.2.2.2,
    observed.1.2.1.toList.map ZMod.val, observed.2)

def summary (q : Sumcheck.Impl.Representation.Message F 1) :=
  summarize ((simulateQ logger (LoggedResult.observe <$> run q)).run [])
def separatedSummary (q : Sumcheck.Impl.Representation.Message F 1) :=
  summarize ((simulateQ logger (decomposed q)).run [])

abbrev nativePacket := LoggedObservation p.tree p.oracles inputSpec.toPFunctor
  NativeResourcesTests.Private (fun _ => Bool)

def nativeDecomposed (q : Sumcheck.Impl.Representation.Message F 1) :
    OracleComp ambientSpec nativePacket := do
  let old ← NativeResourcesTests.bare q
  match old.verifierOut with
  | none => return ⟨old.path, old.proverOut, false, old.sourceLog⟩
  | some claim =>
    let observed : F × QueryLog (ofPFunctor (finalAccess old.path.toBranchPath)) :=
      (simulateQ (old.path.closingImpl p.oracles inputSpec.toPFunctor inputImpl)
        (claim.oracles.query ⟨(), claim.stmt.challenges⟩).withQueryLog).run
    return ⟨old.path, old.proverOut, decide (observed.1 = claim.stmt.target),
      old.sourceLog ++ observed.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem native_packet_eq (q : Sumcheck.Impl.Representation.Message F 1) :
    LoggedResult.observe <$> NativeResourcesTests.completed q = nativeDecomposed q := by
  have h := Computable.Resources.complete_log_eq 1 1 ambientSpec (event 1)
    1 0 rfl inputSpec.toPFunctor originalView initial inputImpl
    (NativeResourcesTests.dependentProver q)
  simp only [NativeResourcesTests.completed, NativeResourcesTests.bare, nativeDecomposed] at h ⊢
  dsimp only [LoggedResult.observe, p, finalAccess] at h ⊢
  convert h using 1
  · rfl
  · apply bind_congr
    intro old
    cases old.verifierOut with
    | none => rfl
    | some claim => rfl

def nativeSummary (observed : nativePacket × List Nat) : Bool × Nat × List Nat × List Nat :=
  (observed.1.2.2.1, observed.1.2.2.2.length, observed.1.2.1.toList.map ZMod.val, observed.2)

namespace Sender
abbrev ambient : OracleSpec Empty := Empty →ₒ Nat
abbrev input : OracleSpec Nat := Nat →ₒ Nat
abbrev initial := input.toPFunctor
def handler : QueryImpl ambient Id := fun i => nomatch i
def impl : QueryImpl (ofPFunctor initial) Id := fun q => 10+q
@[reducible] def interface : OracleInterface Nat where
  Query := Nat
  toOC.spec := Nat →ₒ Nat
  toOC.impl q := do return (← read)+q
abbrev treeProtocol : Interaction.Oracle.Protocol :=
  .public .sender Unit (fun _ => .oracleWith Nat interface .done)
def Private (path : treeProtocol.tree.ExecutionPath) : Type := Vector Nat path.2.1
def prover : Prover.Strategy ambient treeProtocol.tree treeProtocol.roles Private :=
  pure ⟨(), pure ⟨(3 : Nat),#v[7,7,7]⟩⟩
def verifier : Verifier.Strategy ambient treeProtocol.tree treeProtocol.roles
    treeProtocol.oracles initial (fun _ => Nat) := by
  intro _
  change OracleComp (ambient+ofPFunctor initial)
    (OracleComp (ambient+ofPFunctor (Access.extend initial interface))
      (OracleComp (ambient+ofPFunctor (Access.extend initial interface)) Nat))
  exact do
    let before : Nat ← liftM ((ambient+ofPFunctor initial).query (.inr (0 : Nat)))
    return do
      let after : Nat ← liftM ((ambient+ofPFunctor (Access.extend initial interface)).query
        (.inr (.inr (2 : Nat))))
      return pure (before+after)

def tail (path : treeProtocol.tree.BranchPath) (old : Nat) :
    OracleComp (ambient+ofPFunctor (TypeTree.accessAfter treeProtocol.tree
      treeProtocol.oracles initial path)) Nat := do
  let value : Nat ← liftM ((ambient+ofPFunctor (TypeTree.accessAfter treeProtocol.tree
    treeProtocol.oracles initial path)).query (.inr (.inl (1 : Nat))))
  return old+value
abbrev Result := LoggedResult treeProtocol.tree treeProtocol.oracles initial Private (fun _ => Nat)
def run : OracleComp ambient Result := executeStrategiesLogged ambient treeProtocol.tree
  treeProtocol.roles treeProtocol.oracles initial impl prover
  (Verifier.Fragment.mapOutput ambient (fun path action => action >>= tail path) verifier)
def summarize (result : Result) : Nat × List (Nat × Nat × Nat) × List Nat :=
  (result.verifierOut, result.sourceLog.map (fun entry => match entry with
    | ⟨.inl q,answer⟩ => (0,q,answer)
    | ⟨.inr q,answer⟩ => (1,q,answer)), result.proverOut.toList)
def summary : Nat × List (Nat × Nat × Nat) × List Nat := summarize (simulateQ handler run)
end Sender

def check : IO Unit := do
  let expected := [
    ("message(0)", (-1 : F)), ("message(1)", 1), ("message(3)", 5),
    ("input[0](3)", 6), ("input[1](3)", -1),
    ("input[0](3)", 6), ("input[1](3)", -1)]
  unless summary (affine 2 (-1)) == (0, expected, [15,15,15], [0,1,2,0]) do
    throw (IO.userError
      "effectful terminal bind changed source order, private output or ambient effects")
  unless summary (affine 0 1) ==
      (5, [("message(0)", 1), ("message(1)", 1)], [12], [0,2,2]) do
    throw (IO.userError
      "abort/no-source tail was skipped or lost its actual private/terminal effects")
  for q in [affine 2 (-1), affine 0 0, affine 0 1] do
    unless summary q == separatedSummary q do
      throw (IO.userError
        "whole generic actual logger disagrees with its proved terminal decomposition")
    let actual := nativeSummary
      ((simulateQ logger (LoggedResult.observe <$> NativeResourcesTests.completed q)).run [])
    let separated := nativeSummary ((simulateQ logger (nativeDecomposed q)).run [])
    unless actual == separated do
      throw (IO.userError "whole complete native trace lost exact raw terminal fanout")
  unless Sender.summary == (26, [(0,0,10),(1,2,5),(0,1,11)], [7,7,7]) do
    throw (IO.userError
      "public sender/pre-extension query was not routed before the actual terminal tail")
  IO.println "generic/native terminal binding: source order, effects and complete packets passed"

open Lean Elab Command in
run_cmd do
  liftIO check
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``executeStrategiesLogged_bindTerminal,
      ``Verifier.loggedLiftAccessImpl_liftComp, ``Computable.Resources.complete_log_eq,
      ``packet_eq, ``native_packet_eq] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected logged terminal binding axiom: {name}"
  for name in #[``run, ``decomposed, ``summary, ``nativeDecomposed] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual logged terminal caller IR"

end LoggedTerminalTests
