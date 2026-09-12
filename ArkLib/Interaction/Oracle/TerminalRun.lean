/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.LoggedExecution
public import ArkLib.Interaction.Oracle.Terminal

/-!
# Execution with explicit returned outcomes

`executeTerminal` uses the same logged strategy runner for acceptance, rejection, and returned
faults. It pairs the result with the input behavior used by that execution. Closing transforms
only accepted claims, using the paired input behavior and concrete messages. Runtime failure to
return is outside this open-program boundary.
-/

universe u v w

@[expose] public section

namespace Interaction.Oracle

open OracleComp OracleSpec

/-- A returned terminal outcome over exactly the branch's accumulated source signature. -/
abbrev TerminalOutcome (protocol : Oracle.Protocol.{u}) (initial : PFunctor.{u, u})
    (Stmt : protocol.tree.BranchPath → Type u)
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    (Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path))
    (Fault : Type u) (path : protocol.tree.BranchPath) :=
  Terminal (OpenClaim
    (OracleSpec.ofPFunctor (TypeTree.accessAfter protocol.tree protocol.oracles initial path))
    (Stmt path) (Out path)) Fault

/-- A logged terminal result paired with the input behavior used by the executor. The constructor
is private; reachability and probability still require the runner's semantics. -/
structure TerminalRun (protocol : Oracle.Protocol.{u}) (initial : PFunctor.{u, u})
    (Stmt : protocol.tree.BranchPath → Type u)
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    (Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path))
    (OutP : protocol.tree.ExecutionPath → Type u) (Fault : Type u) where
  private mk ::
  /-- The actual concrete path, participant outputs, and ordered source observations. -/
  result : LoggedResult protocol.tree protocol.oracles initial OutP
    (TerminalOutcome protocol initial Stmt Out Fault)
  /-- Input behavior supplied to this same execution. -/
  inputImpl : QueryImpl (OracleSpec.ofPFunctor initial) Id

namespace TerminalRun

variable {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u} {Fault : Type u}

/-- Forget logging and input packaging, retaining the actual returned terminal outcome. -/
def erase (run : TerminalRun protocol initial Stmt Out OutP Fault) := run.result.erase

/-- Close accepted claims using this run's available context, preserving rejection and
returned faults. -/
def closed (run : TerminalRun protocol initial Stmt Out OutP Fault) :
    Terminal (ClosedClaim (Stmt run.result.path.toBranchPath)
      (Out run.result.path.toBranchPath)) Fault :=
  run.result.verifierOut.map fun claim =>
    claim.closeWith (run.result.path.closingImpl protocol.oracles initial run.inputImpl)

/-- Acceptance closes the actual claim with the same input and concrete messages. -/
theorem closed_of_accept (run : TerminalRun protocol initial Stmt Out OutP Fault)
    (claim : OpenClaim
      (OracleSpec.ofPFunctor (TypeTree.accessAfter protocol.tree protocol.oracles initial
        run.result.path.toBranchPath))
      (Stmt run.result.path.toBranchPath) (Out run.result.path.toBranchPath))
    (h : run.result.verifierOut = .accept claim) :
    run.closed = .accept
      (claim.closeWith (run.result.path.closingImpl protocol.oracles initial run.inputImpl)) := by
  simp [closed, h]

/-- Closing cannot create or erase verifier rejection. -/
@[simp]
theorem closed_eq_reject_iff (run : TerminalRun protocol initial Stmt Out OutP Fault) :
    run.closed = .reject ↔ run.result.verifierOut = .reject := by
  unfold closed
  cases run.result.verifierOut <;> simp [Terminal.map]

/-- Closing preserves the exact returned fault, rather than collapsing all failures together. -/
@[simp]
theorem closed_eq_fault_iff (run : TerminalRun protocol initial Stmt Out OutP Fault)
    (fault : Fault) :
    run.closed = .fault fault ↔ run.result.verifierOut = .fault fault := by
  unfold closed
  cases run.result.verifierOut <;> simp [Terminal.map]

/-- An optional-result terminal action can be decoded before or after closing. Absence remains
rejection, while no returned fault can be introduced by this migration decoder. -/
theorem closed_of_ofOption (run : TerminalRun protocol initial Stmt Out OutP Fault)
    (outcome : TerminalClaim protocol initial Stmt Out run.result.path.toBranchPath)
    (h : run.result.verifierOut = Terminal.ofOption outcome) :
    run.closed = Terminal.ofOption (outcome.map fun claim =>
      claim.closeWith (run.result.path.closingImpl protocol.oracles initial run.inputImpl)) := by
  rw [closed, h, ← Terminal.ofOption_map]

/-- The local view is read from this result's source log, never obtained by replay. -/
def verifierLocalView (run : TerminalRun protocol initial Stmt Out OutP Fault) :
    (path : protocol.tree.BranchPath) ×
      QueryLog (OracleSpec.ofPFunctor
        (TypeTree.accessAfter protocol.tree protocol.oracles initial path)) ×
      TerminalOutcome protocol initial Stmt Out Fault path :=
  ⟨run.result.path.toBranchPath, run.result.sourceLog, run.result.verifierOut⟩

end TerminalRun

/-- Execute setup and the ordinary logged strategy runner once, retaining returned faults as data.
The fault type shares the runner's result universe; public statement and witness universes remain
independent. -/
@[no_expose]
def executeTerminal {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {StatementIn : Type v} {WitnessIn : Type w}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u} {Fault : Type u}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalOutcome protocol initial Stmt Out Fault))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    OracleComp ambient (TerminalRun protocol initial Stmt Out OutP Fault) := do
  let prover ← reduction.prover stmt wit
  let result ← executeStrategiesLogged ambient protocol.tree protocol.roles protocol.oracles
    initial impl prover (reduction.verifier stmt)
  return ⟨result, impl⟩

/-- Erasure is an open-program equality with the existing reduction executor, including its
explicit returned faults. No world handler or probability assumption is used. -/
theorem executeTerminal_erase {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {StatementIn : Type v} {WitnessIn : Type w}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u} {Fault : Type u}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalOutcome protocol initial Stmt Out Fault))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    TerminalRun.erase <$> executeTerminal reduction impl stmt wit =
      reduction.execute impl stmt wit := by
  simp only [executeTerminal, Reduction.execute, map_bind, bind_pure_comp, Functor.map_map,
    TerminalRun.erase, executeStrategiesLogged_erase]

end Interaction.Oracle
