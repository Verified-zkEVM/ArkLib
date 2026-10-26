/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.Sumcheck.Interaction.NativeSourceRouting
import ArkLibTest.Interaction.Oracle.LoggedTerminal
import Lean.Compiler.IR

/-! # Leaf-map laws preserve actual node effects, paths, dependent outputs and raw logs -/

open Interaction.Oracle OracleComp OracleSpec
namespace FragmentMapsTests
namespace Receiver
open NativeSourceRoutingTests
abbrev resultType (path : p.tree.BranchPath) :=
  Vector Nat (if (show Option Nat from path.2.1).isSome then 2 else 1)
abbrev action (path : p.tree.BranchPath) (A : Type) :=
  OracleComp (ambient + ofPFunctor (finalAccess path)) A

def first (path : p.tree.BranchPath) (program : action path Bool) : action path Nat := do
  let accepted ← program
  let extra ← (event 0).liftComp (ambient + ofPFunctor (finalAccess path))
  return (if accepted then 5 else 7) + extra

def pack (path : p.tree.BranchPath) (value extra : Nat) : resultType path := by
  rcases path with ⟨message, ⟨choice, rest⟩⟩
  cases choice
  · exact #v[value + extra]
  · exact #v[value, extra]

def second (path : p.tree.BranchPath) (program : action path Nat) :
    action path (resultType path) := do
  let value ← program
  let extra ← (event 2).liftComp (ambient + ofPFunctor (finalAccess path))
  return pack path value extra

def mapped (target : Nat) := Verifier.Fragment.mapOutput ambient second
  (Verifier.Fragment.mapOutput ambient first (completeRouted target))
def composed (target : Nat) := Verifier.Fragment.mapOutput ambient
  (fun path out => second path (first path out)) (completeRouted target)

theorem identity (target : Nat) :
    Verifier.Fragment.mapOutput ambient (fun _ out => out) (completeRouted target) =
      completeRouted target :=
  Verifier.Fragment.mapOutput_id ambient _ _ _ _ _ _
theorem composition (target : Nat) : mapped target = composed target :=
  Verifier.Fragment.mapOutput_comp ambient _ _ _ _ _ _ _ first second _

def values (path : p.tree.ExecutionPath) (out : resultType path.toBranchPath) : List Nat := by
  rcases path with ⟨message, ⟨choice, rest⟩⟩
  cases choice <;> exact out.toList

def summary (nested : Bool) (target : Nat) :=
  let result := (simulateQ logger (executeStrategiesLogged ambient p.tree p.roles p.oracles raw
    (impl true) (prover true) (if nested then mapped target else composed target))).run []
  (values result.1.path result.1.verifierOut, encodeLog result.1.path result.1.sourceLog,
    encodePrivate result.1.path result.1.proverOut, result.2)

end Receiver

namespace Sender
open LoggedTerminalTests.Sender

def extend (path : treeProtocol.tree.BranchPath) (program :
    OracleComp (ambient + ofPFunctor (TypeTree.accessAfter treeProtocol.tree
      treeProtocol.oracles initial path)) Nat) := program >>= tail path

def nested := Verifier.Fragment.mapOutput ambient extend
  (Verifier.Fragment.mapOutput ambient extend verifier)
def composed := Verifier.Fragment.mapOutput ambient
  (fun path out => extend path (extend path out)) verifier

theorem composition : nested = composed :=
  Verifier.Fragment.mapOutput_comp ambient _ _ _ _ _ _ _ extend extend _

def summary := summarize (simulateQ handler (executeStrategiesLogged ambient treeProtocol.tree
  treeProtocol.roles treeProtocol.oracles initial impl prover nested))
end Sender

open Lean Elab Command in
run_cmd do
  let success := [(1,0,1),(1,1,3),(1,6,13),(0,6,0),(0,7,13)]
  unless Receiver.summary true 4 == ([12,8], success, [7,14], [0,1,2,0,2]) do
    throwError "leaf composition changed receiver effects, terminal reads or dependent output"
  unless Receiver.summary true 0 == ([22], [(1,0,1),(1,1,3)], [0], [0,2,0,2]) do
    throwError "leaf composition changed abort effects or path-dependent output type"
  for target in [0,4] do
    unless Receiver.summary true target == Receiver.summary false target do
      throwError "nested and composed leaf maps produced different complete packets"
  unless Sender.summary == (37, [(0,0,10),(1,2,5),(0,1,11),(0,1,11)], [7,7,7]) do
    throwError "leaf composition lost public-sender/fresh-source ordering or repeated queries"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Verifier.Fragment.mapOutput_id, ``Verifier.Fragment.mapOutput_comp,
      ``Receiver.identity, ``Receiver.composition, ``Sender.composition] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected fragment leaf-map axiom: {name}"
  for name in #[``Receiver.first, ``Receiver.second, ``Receiver.mapped, ``Receiver.composed,
      ``Receiver.summary, ``Sender.summary] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual fragment leaf-map caller IR: {name}"
  logInfo "fragment leaf maps: dependent outputs, effects and repeated raw reads passed"
end FragmentMapsTests
