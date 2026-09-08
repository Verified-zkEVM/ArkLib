/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.LoggedExecution

/-!
# Paired logged executions

`executeLogged` pairs a core run with the ordered source observations made during that run.
The supported constructor accepts a reduction and its inputs, never separately supplied outputs
and traces. Membership in a runner distribution remains the provenance criterion.
-/

universe u v w

namespace Interaction.Oracle

open OracleComp OracleSpec

/-- A core execution and the source log produced alongside it. -/
structure LoggedRun (protocol : Oracle.Protocol.{u}) (initial : PFunctor.{u, u})
    (Stmt : protocol.tree.BranchPath → Type u)
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    (Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path))
    (OutP : protocol.tree.ExecutionPath → Type u) where
  private mk ::
  /-- The actual path, resources, private output, and verifier claim. -/
  core : CoreRun protocol initial Stmt Out OutP
  /-- The verifier's source queries and responses, in execution order. -/
  deltaTrace : QueryLog (OracleSpec.ofPFunctor
    (TypeTree.accessAfter protocol.tree protocol.oracles initial core.path.toBranchPath))

namespace LoggedRun

variable {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u}

/-- Verifier observations derived from the enclosing execution's log, without replay. This view
contains the structural public path, source observations, and terminal output. Ambient world
observations belong to the enclosing VCVio runtime artifact. -/
def verifierLocalView (run : LoggedRun protocol initial Stmt Out OutP) :
    (path : protocol.tree.BranchPath) ×
      QueryLog (OracleSpec.ofPFunctor
        (TypeTree.accessAfter protocol.tree protocol.oracles initial path)) ×
      TerminalClaim protocol initial Stmt Out path :=
  ⟨run.core.path.toBranchPath, run.deltaTrace, run.core.outcome⟩

/-- Closing uses the core's own resources; the trace is observational evidence, not a handler. -/
def closed (run : LoggedRun protocol initial Stmt Out OutP) := run.core.closed

end LoggedRun

/-- Run the prover setup and both strategies once, pairing the core result with its source log. -/
def executeLogged {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {StatementIn : Type v} {WitnessIn : Type w}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalClaim protocol initial Stmt Out))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    OracleComp ambient (LoggedRun protocol initial Stmt Out OutP) := do
  let prover ← reduction.prover stmt wit
  let result ← executeStrategiesLogged ambient protocol.tree protocol.roles protocol.oracles
    initial impl prover (reduction.verifier stmt)
  return ⟨⟨result.path, impl, result.proverOut, result.verifierOut⟩, result.deltaTrace⟩

/-- Erasing the log recovers the existing trace-free core executor as an open ambient program. -/
theorem executeLogged_erase {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {StatementIn : Type v} {WitnessIn : Type w}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalClaim protocol initial Stmt Out))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    LoggedRun.core <$> executeLogged reduction impl stmt wit =
      executeCore reduction impl stmt wit := by
  simp only [executeLogged, executeCore, Reduction.execute, map_bind, map_pure, bind_assoc]
  congr 1
  funext prover
  have h := executeStrategiesLogged_erase ambient protocol.tree protocol.roles protocol.oracles
    initial impl prover (reduction.verifier stmt)
  have lifted := congrArg (fun program =>
    (fun result => (⟨result.1, impl, result.2.1, result.2.2⟩ :
      CoreRun protocol initial Stmt Out OutP)) <$> program) h
  simpa only [Functor.map_map, LoggedResult.erase, bind_pure_comp] using lifted

end Interaction.Oracle
