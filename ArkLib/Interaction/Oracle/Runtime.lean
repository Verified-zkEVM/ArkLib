/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.LoggedRun
public import VCVio.OracleComp.Runtime

/-!
# Executing native strategies in a persistent runtime

The runtime runs one source-logged native strategy program and returns its output, final state,
and ordered ambient query log together. Reduction setup remains inside that same runtime run.
Source queries stay in `LoggedRun.sourceLog`; ambient queries stay
in the runtime's query log. Closing is derived from the returned core's own resources.
A run-result value alone carries no assertion that it was sampled by this computation.
-/

@[expose] public section

namespace Interaction.Oracle

open OracleComp OracleSpec

variable {ι κ : Type} {imports : OracleSpec ι} {ambient : OracleSpec κ}
    {protocol : Oracle.Protocol} {initial : PFunctor}
    {StatementIn WitnessIn : Type}
    {Stmt : protocol.tree.BranchPath → Type}
    {Idx : protocol.tree.BranchPath → Type}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type}

/-- Run native strategies in one initialized runtime, retaining source and ambient observations. -/
def executeStrategiesWithRuntime (runtime : OracleRuntime imports ambient)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (prover : Prover.Strategy ambient protocol.tree protocol.roles OutP)
    (verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial
      (TerminalClaim protocol initial Stmt Out)) :
    OracleComp imports (RunResult runtime (LoggedRun protocol initial Stmt Out OutP)) :=
  runtime.run (executeStrategiesLoggedRun impl prover verifier)

/-- Native runtime execution uses the same source-logged strategy program. -/
theorem executeStrategiesWithRuntime_eq (runtime : OracleRuntime imports ambient)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (prover : Prover.Strategy ambient protocol.tree protocol.roles OutP)
    (verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial
      (TerminalClaim protocol initial Stmt Out)) :
    executeStrategiesWithRuntime runtime impl prover verifier =
      runtime.run (executeStrategiesLoggedRun impl prover verifier) := rfl

/-- Erasing instrumentation retains the core output and actual final persistent state. -/
theorem executeStrategiesWithRuntime_erase (runtime : OracleRuntime imports ambient)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (prover : Prover.Strategy ambient protocol.tree protocol.roles OutP)
    (verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial
      (TerminalClaim protocol initial Stmt Out)) :
    (fun result => (result.output.core, result.state)) <$>
        executeStrategiesWithRuntime runtime impl prover verifier =
      (runtime.setup >>= fun state => runtime.handler.runState state
        (executeStrategiesCore impl prover verifier)) := by
  rw [executeStrategiesWithRuntime_eq, OracleRuntime.run_eq]
  simp only [map_bind]
  congr 1
  funext state
  have erased := runtime.runFrom_eraseTrace state
    (executeStrategiesLoggedRun impl prover verifier)
  have paired := congrArg (fun program =>
    (fun result => (result.1.core, result.2)) <$> program) erased
  have core := congrArg (runtime.handler.runState state)
    (executeStrategiesLoggedRun_erase impl prover verifier)
  calc
    _ = (fun result => (result.1.core, result.2)) <$>
        runtime.handler.runState state (executeStrategiesLoggedRun impl prover verifier) := by
      simpa only [Functor.map_map] using paired
    _ = _ := by
      simpa [QueryImpl.Stateful.runState, monad_norm] using core

/-- Run both participants in one initialized runtime, retaining both kinds of query observation. -/
def executeWithRuntime (runtime : OracleRuntime imports ambient)
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalClaim protocol initial Stmt Out))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    OracleComp imports (RunResult runtime (LoggedRun protocol initial Stmt Out OutP)) :=
  runtime.run (executeLogged reduction impl stmt wit)

/-- The runtime adapter introduces no extra execution or source-query replay. -/
theorem executeWithRuntime_eq (runtime : OracleRuntime imports ambient)
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalClaim protocol initial Stmt Out))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    executeWithRuntime runtime reduction impl stmt wit =
      runtime.run (executeLogged reduction impl stmt wit) := rfl

/-- Erasing the two logs yields the core run and final state from the ordinary stateful runner. -/
theorem executeWithRuntime_erase (runtime : OracleRuntime imports ambient)
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalClaim protocol initial Stmt Out))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    (fun result => (result.output.core, result.state)) <$>
        executeWithRuntime runtime reduction impl stmt wit =
      (runtime.setup >>= fun state => runtime.handler.runState state
        (executeCore reduction impl stmt wit)) := by
  rw [executeWithRuntime_eq, OracleRuntime.run_eq]
  simp only [map_bind]
  congr 1
  funext state
  have erased := runtime.runFrom_eraseTrace state (executeLogged reduction impl stmt wit)
  have paired := congrArg (fun program =>
    (fun result => (result.1.core, result.2)) <$> program) erased
  have core := congrArg (runtime.handler.runState state)
    (executeLogged_erase reduction impl stmt wit)
  calc
    _ = (fun result => (result.1.core, result.2)) <$>
        runtime.handler.runState state (executeLogged reduction impl stmt wit) := by
      simpa only [Functor.map_map] using paired
    _ = _ := by
      simpa [QueryImpl.Stateful.runState, monad_norm] using core

end Interaction.Oracle
