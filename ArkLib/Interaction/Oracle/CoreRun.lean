/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Execution
public import ArkLib.Interaction.Oracle.RunSources
public import ArkLib.Interaction.Oracle.Claim

/-!
# Trace-free execution and closing

The executor pairs its actual path, input behavior, private output, and verifier-produced claim.
`CoreRun.closed` accepts no replacement handler: it derives answers from these paired resources.
The carrier alone does not certify that an execution occurred. Execution theorems concern
`executeCore`; arbitrary record values carry no reachability or probability assertion.

`none` is an explicit verifier rejection. Runtime faults, missing probability mass, query logs,
and security games remain outside this trace-free boundary.
-/

@[expose] public section

universe u v w

namespace Interaction.Oracle

/-- An optional terminal claim over the final branch signature.
`none` denotes verifier rejection. -/
abbrev TerminalClaim (protocol : Oracle.Protocol.{u}) (initial : PFunctor.{u, u})
    (Stmt : protocol.tree.BranchPath → Type u)
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    (Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path))
    (path : protocol.tree.BranchPath) :=
  Option (OpenClaim
    (OracleSpec.ofPFunctor (TypeTree.accessAfter protocol.tree protocol.oracles initial path))
    (Stmt path) (Out path))

/-- Data for closing a completed interaction. The carrier is public; executor equations or support
membership establish that its fields arose together. -/
structure CoreRun (protocol : Oracle.Protocol.{u}) (initial : PFunctor.{u, u})
    (Stmt : protocol.tree.BranchPath → Type u)
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    (Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path))
    (OutP : protocol.tree.ExecutionPath → Type u) where
  /-- Concrete path, including hidden prover messages. -/
  path : protocol.tree.ExecutionPath
  /-- Input behavior used to interpret the final access signature. -/
  inputImpl : QueryImpl (OracleSpec.ofPFunctor initial) Id
  /-- Private prover output may depend on the concrete path. -/
  proverOut : OutP path
  /-- Optional verifier output at the recorded structural branch. -/
  outcome : TerminalClaim protocol initial Stmt Out path.toBranchPath

namespace CoreRun

variable {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u}

/-- Close using only this run's input and sent messages. -/
def closed (run : CoreRun protocol initial Stmt Out OutP) :
    Option (ClosedClaim (Stmt run.path.toBranchPath) (Out run.path.toBranchPath)) :=
  run.outcome.map fun claim =>
    claim.closeWith (run.path.closingImpl protocol.oracles initial run.inputImpl)

/-- Successful closing uses the paired concrete resources; its statement is left unchanged. -/
theorem closed_of_some (run : CoreRun protocol initial Stmt Out OutP)
    (claim : OpenClaim
      (OracleSpec.ofPFunctor
        (TypeTree.accessAfter protocol.tree protocol.oracles initial run.path.toBranchPath))
      (Stmt run.path.toBranchPath) (Out run.path.toBranchPath))
    (h : run.outcome = some claim) :
    run.closed = some
      (claim.closeWith (run.path.closingImpl protocol.oracles initial run.inputImpl)) := by
  simp [closed, h]

/-- Rejection cannot become a successful closed claim. -/
theorem closed_eq_none_iff (run : CoreRun protocol initial Stmt Out OutP) :
    run.closed = none ↔ run.outcome = none := by
  simp [closed]

/-- Concrete output agreement is derived from statement agreement and query-by-query interpretation
under the resources of this run. It never requires equality of concrete representations. -/
theorem closed_eq_concrete_iff (run : CoreRun protocol initial Stmt Out OutP)
    (claim : OpenClaim
      (OracleSpec.ofPFunctor
        (TypeTree.accessAfter protocol.tree protocol.oracles initial run.path.toBranchPath))
      (Stmt run.path.toBranchPath) (Out run.path.toBranchPath))
    (data : ConcreteClaim (Stmt run.path.toBranchPath) (Out run.path.toBranchPath))
    (h : run.outcome = some claim) :
    run.closed = some data.toClosed ↔
      claim.stmt = data.stmt ∧ ∀ query,
        simulateQ (run.path.closingImpl protocol.oracles initial run.inputImpl)
          (claim.oracles.query query) =
        (Out run.path.toBranchPath).behaviorOfRealizations data.oracles query := by
  rw [run.closed_of_some claim h]
  simp only [Option.some.injEq, OpenClaim.closeWith, ConcreteClaim.toClosed, ClaimWith.mk.injEq]
  constructor
  · rintro ⟨hs, ho⟩
    exact ⟨hs, fun query => congrFun ho query⟩
  · rintro ⟨hs, ho⟩
    exact ⟨hs, funext ho⟩

end CoreRun

/-- Execute the existing restricted strategies and retain the resources needed for closing. -/
def executeCore {ι : Type u} {ambient : OracleSpec.{u, u} ι}
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
    OracleComp ambient (CoreRun protocol initial Stmt Out OutP) := do
  let result ← reduction.execute impl stmt wit
  return ⟨result.1, impl, result.2.1, result.2.2⟩

/-- The public executor is the ordinary execution followed only by packaging its own outputs. -/
theorem executeCore_eq_execute {ι : Type u} {ambient : OracleSpec.{u, u} ι}
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
    executeCore reduction impl stmt wit = (do
      let result ← reduction.execute impl stmt wit
      return ⟨result.1, impl, result.2.1, result.2.2⟩) := rfl

end Interaction.Oracle
