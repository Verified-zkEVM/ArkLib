/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Protocol
import ArkLib.Interaction.Oracle.PhasedExecution
import Lean.Compiler.IR

/-! # Exact native substitution over Nat with arbitrary messages and dependent private output -/

open Interaction.Oracle OracleComp OracleSpec
open Sumcheck.Interaction
namespace NativeSourceRoutingTests
abbrev ambient : OracleSpec (Fin 3) := Fin 3 →ₒ Nat
abbrev sourceSpec : OracleSpec (Unit × Nat) := (Unit × Nat) →ₒ Nat
abbrev rawSpec : OracleSpec Nat := Nat →ₒ Nat
abbrev source := sourceSpec.toPFunctor
abbrev raw := rawSpec.toPFunctor
def evaluate (message : Bool) (x : Nat) : Nat := if message then 2*x+1 else 0
abbrev p := Native.Core.protocol Nat Bool evaluate 1
def event (i : Fin 3) : OracleComp ambient Nat := liftM (ambient.query i)
def logger : QueryImpl ambient (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return ![7, 6, 8] i
def impl (twoReads : Bool) : QueryImpl (ofPFunctor raw) Id :=
  fun q => if q = 6 then if twoReads then 0 else 1 else 13
def route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor raw)) := fun q => do
  let first ← liftM (rawSpec.query q.2)
  if first = 0 then liftM (rawSpec.query (q.2+1)) else pure first
def original : VirtualOracle (ofPFunctor source)
    (MultivariateRound.polynomialFamily Nat 1 1) :=
  ⟨fun q => liftM (sourceSpec.query ((), q.2 0))⟩
def statement (target : Nat) : Sumcheck.Spec.StatementRound Nat 1 0 := ⟨target, Fin.elim0⟩
def bare (target : Nat) :=
  Native.Core.verifier Nat 1 1 Bool evaluate ambient (event 1) [0, 1] 1 0 rfl
    source original (statement target)
def routed (target : Nat) := Verifier.routeClaimStrategy ambient p.tree p.roles p.oracles
  source raw route (fun _ => Native.Core.FinalStatement Nat 1)
  (fun _ => Sumcheck.Spec.OracleStatement Nat 1 1)
  (fun _ => MultivariateRound.polynomialFamily Nat 1 1) (bare target)
def direct (target : Nat) :=
  Native.Core.verifier Nat 1 1 Bool evaluate ambient (event 1) [0, 1] 1 0 rfl
    raw (original.substSource route) (statement target)
theorem strategies_eq (target : Nat) : routed target = direct target :=
  Native.Core.routeClaimStrategy_verifier 1 1 Bool evaluate ambient (event 1) [0, 1]
    1 0 rfl source raw route original (statement target)
def Private (path : p.tree.ExecutionPath) : Type :=
  if (show Option Nat from path.2.1).isSome then Vector Nat 2 else Bool
def prover (message : Bool) : Prover.Strategy ambient p.tree p.roles Private := do
  let secret ← event 0
  return ⟨message, fun
    | none => do
      let _ ← event 2
      return false
    | some r => do
      let trailing ← event 2
      return #v[secret, r+trailing]⟩
abbrev finalAccess (path : p.tree.BranchPath) := TypeTree.accessAfter p.tree p.oracles raw path
def completeRouted (target : Nat) := Verifier.Fragment.mapOutput ambient
  (fun path action => Native.Core.checkFinalResult Nat 1 1 ambient (finalAccess path) action)
  (routed target)
def completeDirect (target : Nat) :=
  Native.Core.verifierWithFinalCheck Nat 1 1 Bool evaluate ambient (event 1) [0, 1] 1 0 rfl
    raw (original.substSource route) (statement target)
theorem completed_eq (target : Nat) : completeRouted target = completeDirect target := by
  rw [completeRouted, strategies_eq]
  rfl
abbrev Result := LoggedResult p.tree p.oracles raw Private (fun _ => Bool)
def run (directly twoReads : Bool) (target : Nat) (message : Bool) : OracleComp ambient Result :=
  executeStrategiesLogged ambient p.tree p.roles p.oracles raw (impl twoReads) (prover message)
    (if directly then completeDirect target else completeRouted target)
theorem actual_eq (twoReads : Bool) (target : Nat) (message : Bool) :
    run false twoReads target message = run true twoReads target message := by
  simp only [run, Bool.false_eq_true, ↓reduceIte, completed_eq]
def encodePrivate (path : p.tree.ExecutionPath) (out : Private path) : List Nat := by
  rcases path with ⟨message, ⟨choice, rest⟩⟩
  cases choice
  · change Bool at out
    exact if out then [1] else [0]
  · exact out.toList
def encodeLog (path : p.tree.ExecutionPath)
    (log : QueryLog (ofPFunctor (finalAccess path.toBranchPath))) : List (Nat × Nat × Nat) := by
  rcases path with ⟨message, ⟨choice, rest⟩⟩
  cases choice <;>
    exact log.map (fun entry => match entry with
      | ⟨.inl q, answer⟩ => (0, q, answer)
      | ⟨.inr q, answer⟩ => (1, q, answer))
def summary (directly twoReads : Bool) (target : Nat) (message : Bool) :
    Bool × List (Nat × Nat × Nat) × List Nat × List Nat :=
  let result := (simulateQ logger (run directly twoReads target message)).run []
  (result.1.verifierOut, encodeLog result.1.path result.1.sourceLog,
    encodePrivate result.1.path result.1.proverOut, result.2)

namespace Zero
abbrev p := Native.Core.protocol Nat Bool evaluate 0
def original : VirtualOracle (ofPFunctor source)
    (MultivariateRound.polynomialFamily Nat 0 1) :=
  ⟨fun _ => liftM (sourceSpec.query ((), 6))⟩
def statement (target : Nat) : Sumcheck.Spec.StatementRound Nat 0 0 := ⟨target, Fin.elim0⟩
def bare (target : Nat) :=
  Native.Core.verifier Nat 0 1 Bool evaluate ambient (event 1) [0, 1] 0 0 rfl
    source original (statement target)
def routed (target : Nat) := Verifier.routeClaimStrategy ambient p.tree p.roles p.oracles
  source raw route (fun _ => Native.Core.FinalStatement Nat 0)
  (fun _ => Sumcheck.Spec.OracleStatement Nat 0 1)
  (fun _ => MultivariateRound.polynomialFamily Nat 0 1) (bare target)
def direct (target : Nat) :=
  Native.Core.verifier Nat 0 1 Bool evaluate ambient (event 1) [0, 1] 0 0 rfl
    raw (original.substSource route) (statement target)
theorem strategies_eq (target : Nat) : routed target = direct target :=
  Native.Core.routeClaimStrategy_verifier 0 1 Bool evaluate ambient (event 1) [0, 1]
    0 0 rfl source raw route original (statement target)
def prover : Prover.Strategy ambient p.tree p.roles (fun _ => Nat) := by
  change Nat
  exact 37
def run (target : Nat) : OracleComp ambient Bool := do
  let result ← executeStrategiesLogged ambient p.tree p.roles p.oracles raw (impl true)
    (OutP := fun _ => Nat) prover
    (Verifier.Fragment.mapOutput ambient
      (fun path action => Native.Core.checkFinalResult Nat 0 1 ambient
        (TypeTree.accessAfter p.tree p.oracles raw path) action) (routed target))
  return result.verifierOut
end Zero

open Lean Elab Command in
run_cmd do
  let success := [(1,0,1),(1,1,3),(1,6,13),(0,6,0),(0,7,13)]
  unless summary false true 4 true == (true, success, [7,14], [0,1,2]) do
    throwError "routing changed fresh reads, dependent output or terminal fanout"
  unless summary false false 4 true ==
      (false, [(1,0,1),(1,1,3),(1,6,13),(0,6,1)], [7,14], [0,1,2]) do
    throwError "answer-dependent route lost terminal rejection or raw order"
  unless summary false true 0 true ==
      (false, [(1,0,1),(1,1,3)], [0], [0,2]) do
    throwError "routing queried an old source or drew a challenge after native abort"
  for twoReads in [true,false] do
    for target in [0,4] do
      for message in [true,false] do
        unless summary false twoReads target message == summary true twoReads target message do
          throwError "actual routed strategy differed from direct source substitution"
  unless ((simulateQ logger (Zero.run 13)).run []).run == (true, []) &&
      ((simulateQ logger (Zero.run 0)).run []).run == (false, []) do
    throwError "zero-round routing skipped authentication or sampled a challenge"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Native.Core.routeClaimStrategy_verifier,
      ``strategies_eq,
      ``completed_eq,
      ``actual_eq,
      ``Zero.strategies_eq] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected exact source-routing axiom: {name}"
  for name in #[``route,
      ``routed,
      ``direct,
      ``completeRouted,
      ``completeDirect,
      ``prover,
      ``run,
      ``summary,
      ``encodePrivate,
      ``encodeLog,
      ``Zero.run] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable source-routing caller IR: {name}"
  logInfo "Nat routing: exact programs, fanout, effects and dependent outputs passed"

end NativeSourceRoutingTests
