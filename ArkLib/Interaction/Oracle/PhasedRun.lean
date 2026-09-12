/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.PhasedExecution
public import ArkLib.Interaction.Oracle.Runtime
public import ArkLib.Interaction.Oracle.TerminalRun
import all ArkLib.Interaction.Oracle.WorldSegments
import all ArkLib.Interaction.Oracle.LoggedRun
import all ArkLib.Interaction.Oracle.TerminalRun

/-!
# Complete protocol executions with world phases

The prover setup and every subsequent local action are instrumented in one open computation.
An oracle runtime interprets that computation with one initialized persistent state. Boundary
labels and available contexts come from the returned concrete path; world-query profiles use an
explicit fixed query classification.
-/

@[expose] public section

namespace Interaction.Oracle

open OracleSpec OracleComp

/-- A complete protocol execution with its setup and local-action logs kept together. -/
structure PhasedRun {ι : Type} (ambient : OracleSpec ι) (tree : Oracle.TypeTree)
    (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration) (initial : PFunctor)
    (OutP : tree.ExecutionPath → Type) (OutV : tree.BranchPath → Type) where
  private mk ::
  /-- World queries made by the prover setup, before the first protocol move. -/
  setupTrace : QueryLog ambient
  /-- The input behavior supplied to this same execution. -/
  inputImpl : QueryImpl (OracleSpec.ofPFunctor initial) Id
  /-- The actual protocol execution and its node-local query regions. -/
  execution : PhasedResult ambient tree roles oracles initial OutP OutV

namespace PhasedRun

variable {ι : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    {roles : tree.RoleDecoration} {oracles : tree.OracleDecoration} {initial : PFunctor}
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}

/-- Complete chronological log, including prover setup. -/
def worldTrace (run : PhasedRun ambient tree roles oracles initial OutP OutV) : QueryLog ambient :=
  run.setupTrace ++ run.execution.world.flatten

/-- All paired source observations and the complete world log. -/
def logView (run : PhasedRun ambient tree roles oracles initial OutP OutV) :=
  (run.execution.observe, run.worldTrace)

/-- Local actions and their concrete stopping boundaries, beginning with setup. -/
def phases (run : PhasedRun ambient tree roles oracles initial OutP OutV) :
    List (WorldPhase ambient tree) :=
  run.execution.world.phasesWithSetup run.setupTrace roles

/-- The chronological regions account for the whole log without deleting duplicate queries. -/
theorem phases_flatten (run : PhasedRun ambient tree roles oracles initial OutP OutV) :
    ((run.phases).map WorldPhase.queries).flatten = run.worldTrace :=
  WorldSegments.phasesWithSetup_flatten ..

/-- Every action boundary, including setup, extends to the same complete concrete path. -/
theorem phases_reached (run : PhasedRun ambient tree roles oracles initial OutP OutV)
    (phase : WorldPhase ambient tree)
    (member : phase ∈ run.phases) :
    Nonempty (TypeTree.ExecutionPrefix.Extends phase.prefix
      (TypeTree.ExecutionPrefix.ofExecutionPath run.execution.path)) := by
  simp only [phases, WorldSegments.phasesWithSetup, List.mem_cons] at member
  rcases member with rfl | member
  · exact ⟨⟨TypeTree.ExecutionPrefix.ofExecutionPath run.execution.path,
      TypeTree.ExecutionPrefix.root_comp _⟩⟩
  · exact WorldSegments.phases_reached roles run.execution.world phase member

/-- A boundary's available context embeds into the final context with unchanged stable names. -/
noncomputable def contextInclusion (run : PhasedRun ambient tree roles oracles initial OutP OutV)
    (phase : WorldPhase ambient tree)
    (member : phase ∈ run.phases) (InputId : Type) :
    NamedContext.Inclusion (phase.availableContext InputId)
      ((TypeTree.ExecutionPrefix.ofExecutionPath run.execution.path).availableContext InputId) :=
  TypeTree.ExecutionPrefix.contextInclusion (run.phases_reached phase member).some.toCursor
    InputId

/-- The sum of action profiles counts precisely the complete world log, with one fixed identity
classification throughout. Repeated queries contribute repeatedly. -/
theorem queryProfiles_sum {κ : Type} (run : PhasedRun ambient tree roles oracles initial OutP OutV)
    (classify : ambient.Domain → κ) :
    ((run.phases).map (fun phase => phase.queryProfile classify)).sum =
      (run.worldTrace.map
        (fun entry => ResourceProfile.single (ω := ℕ) (classify entry.1))).sum := by
  rw [WorldPhase.queryProfile_sum, run.phases_flatten]

end PhasedRun

/-- Run setup and both strategies once, instrumenting every actual local action. -/
@[no_expose]
def executePhases {ι : Type} (ambient : OracleSpec ι)
    (tree : Oracle.TypeTree) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (setup : OracleComp ambient (Prover.Strategy ambient tree roles OutP))
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV) :
    OracleComp ambient (PhasedRun ambient tree roles oracles initial OutP OutV) := do
  let ⟨prover, setupTrace⟩ ← setup.withQueryLog
  let result ← executeStrategiesPhased ambient tree roles oracles initial impl prover verifier
  return ⟨setupTrace, impl, result⟩

set_option backward.isDefEq.respectTransparency false in
/-- Including setup preserves the complete paired world/source observation of the logged run. -/
theorem executePhases_logView {ι : Type} (ambient : OracleSpec ι)
    (tree : Oracle.TypeTree) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (setup : OracleComp ambient (Prover.Strategy ambient tree roles OutP))
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV) :
    PhasedRun.logView <$> executePhases ambient tree roles oracles initial impl setup verifier =
      (fun result => (result.1.observe, result.2)) <$>
        (setup >>= fun prover =>
          executeStrategiesLogged ambient tree roles oracles initial impl prover
            verifier).withQueryLog := by
  simp only [executePhases, map_bind, map_pure, OracleComp.withQueryLog_bind,
    Functor.map_map]
  congr 1
  funext p
  have h := executeStrategiesPhased_logView ambient tree roles oracles initial impl p.1 verifier
  have lifted := congrArg (fun program =>
    (fun result => (result.1, p.2 ++ result.2)) <$> program) h
  simpa [PhasedRun.logView, PhasedRun.worldTrace, PhasedResult.logView,
    Functor.map_map, monad_norm] using lifted

/-- Supported complete runs retain exactly their actual world log, including setup. -/
theorem executePhases_world_eq {ι : Type} (ambient : OracleSpec ι)
    (tree : Oracle.TypeTree) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (setup : OracleComp ambient (Prover.Strategy ambient tree roles OutP))
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV)
    (result : PhasedRun ambient tree roles oracles initial OutP OutV) (trace : QueryLog ambient)
    (generated : (result, trace) ∈ support
      (executePhases ambient tree roles oracles initial impl setup verifier).withQueryLog) :
    result.worldTrace = trace := by
  have natural {α β : Type} (f : α → β) (program : OracleComp ambient α) :
      (f <$> program).withQueryLog = (fun result => (f result.1, result.2)) <$>
        program.withQueryLog := by simp [OracleComp.withQueryLog]
  have observed : (result.logView, trace) ∈ support
      (PhasedRun.logView <$>
        executePhases ambient tree roles oracles initial impl setup verifier).withQueryLog := by
    rw [natural, support_map]
    exact ⟨(result, trace), generated, rfl⟩
  rw [executePhases_logView, natural, support_map] at observed
  obtain ⟨⟨⟨original, inner⟩, outer⟩, supported, equal⟩ := observed
  have agree := OracleComp.withQueryLog_self_log_eq
    (setup >>= fun prover =>
      executeStrategiesLogged ambient tree roles oracles initial impl prover verifier) supported
  have inner_eq : inner = result.worldTrace := congrArg (fun x => x.1.2) equal
  have outer_eq : outer = trace := congrArg Prod.snd equal
  exact inner_eq.symm.trans (agree.trans outer_eq)

/-- The phased execution of a protocol reduction includes its prover setup. -/
def executePhased {ι : Type} {ambient : OracleSpec ι} {protocol : Oracle.Protocol}
    {initial : PFunctor} {StatementIn WitnessIn : Type}
    {OutP : protocol.tree.ExecutionPath → Type} {OutV : protocol.tree.BranchPath → Type}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP OutV)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :=
  executePhases ambient protocol.tree protocol.roles protocol.oracles initial impl
    (reduction.prover stmt wit) (reduction.verifier stmt)

section Claims

variable {ι : Type} {ambient : OracleSpec ι} {protocol : Oracle.Protocol}
    {initial : PFunctor} {Stmt : protocol.tree.BranchPath → Type}
    {Idx : protocol.tree.BranchPath → Type}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type}

/-- The existing logged run's actual path, participant outputs, and source observations. -/
def LoggedRun.observation (run : LoggedRun protocol initial Stmt Out OutP) :
    LoggedObservation protocol.tree protocol.oracles initial OutP
      (TerminalClaim protocol initial Stmt Out) :=
  ⟨run.core.path, run.core.proverOut, run.core.outcome, run.sourceLog⟩

/-- Close an optional claim with the input behavior and concrete messages stored by this run. -/
def PhasedRun.closed
    (run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial OutP
      (TerminalClaim protocol initial Stmt Out)) :
    Option (ClosedClaim (Stmt run.execution.path.toBranchPath)
      (Out run.execution.path.toBranchPath)) :=
  run.execution.verifierOut.map fun claim =>
    claim.closeWith
      (run.execution.path.closingImpl protocol.oracles initial run.inputImpl)

/-- Package the structural branch together with its closed optional outcome. -/
def PhasedRun.closedResult
    (run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial OutP
      (TerminalClaim protocol initial Stmt Out)) :
    (path : protocol.tree.BranchPath) × Option (ClosedClaim (Stmt path) (Out path)) :=
  ⟨run.execution.path.toBranchPath, run.closed⟩

/-- Closing cannot turn verifier rejection into a successful claim. -/
@[simp]
theorem PhasedRun.closed_eq_none_iff
    (run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial OutP
      (TerminalClaim protocol initial Stmt Out)) :
    run.closed = none ↔ run.execution.verifierOut = none := by
  simp [PhasedRun.closed]

/-- The claim-bearing phased runner agrees with `executeLogged`, including the complete world
log and the same path-dependent output claim. The phased artifact separately retains the same
input behavior for its closing operation. -/
theorem executePhased_logView {StatementIn WitnessIn : Type}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalClaim protocol initial Stmt Out))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    PhasedRun.logView <$> executePhased reduction impl stmt wit =
      (fun result => (result.1.observation, result.2)) <$>
        (executeLogged reduction impl stmt wit).withQueryLog := by
  rw [executePhased, executePhases_logView]
  simp [executeLogged, OracleComp.withQueryLog_bind, LoggedRun.observation, LoggedResult.observe,
    monad_norm]

/-- Closing the phased artifact agrees with closing the trace-free artifact produced by the
same reduction execution. -/
theorem executePhased_closed {StatementIn WitnessIn : Type}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalClaim protocol initial Stmt Out))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    PhasedRun.closedResult <$> executePhased reduction impl stmt wit =
      (fun run => ⟨run.path.toBranchPath, run.closed⟩) <$>
        executeCore reduction impl stmt wit := by
  simp only [executePhased, executePhases, executeCore, Reduction.execute, map_bind, map_pure]
  conv_rhs => rw [← loggingOracle.fst_map_run_simulateQ (reduction.prover stmt wit)]
  simp only [bind_map_left, bind_assoc]
  apply bind_congr
  intro setupResult
  have observed := executeStrategiesPhased_erase ambient protocol.tree protocol.roles
    protocol.oracles initial impl setupResult.1 (reduction.verifier stmt)
  have projected := congrArg (fun program =>
    (fun observation : LoggedObservation protocol.tree protocol.oracles initial OutP
        (TerminalClaim protocol initial Stmt Out) =>
      (⟨observation.1.toBranchPath,
        observation.2.2.1.map fun claim => claim.closeWith
          (observation.1.closingImpl protocol.oracles initial impl)⟩ :
        (path : protocol.tree.BranchPath) ×
          Option (ClosedClaim (Stmt path) (Out path)))) <$> program) observed
  simp only [Functor.map_map, PhasedResult.observe, LoggedResult.observe] at projected
  have erased := executeStrategiesLogged_erase ambient protocol.tree protocol.roles
    protocol.oracles initial impl setupResult.1 (reduction.verifier stmt)
  have closed := congrArg (fun program =>
    (fun result =>
      (⟨result.1.toBranchPath,
        result.2.2.map fun claim => claim.closeWith
          (result.1.closingImpl protocol.oracles initial impl)⟩ :
        (path : protocol.tree.BranchPath) ×
          Option (ClosedClaim (Stmt path) (Out path)))) <$> program) erased
  simp only [Functor.map_map, LoggedResult.erase] at closed
  simpa [PhasedRun.closedResult, PhasedRun.closed, CoreRun.closed] using projected.trans closed

end Claims

section TerminalClaims

variable {ι : Type} {ambient : OracleSpec ι} {protocol : Oracle.Protocol}
    {initial : PFunctor} {Stmt : protocol.tree.BranchPath → Type}
    {Idx : protocol.tree.BranchPath → Type}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type} {Fault : Type}

/-- Close an explicit returned outcome with this phased run's stored input and messages.
Rejection and returned faults remain distinct. -/
def PhasedRun.terminalClosed
    (run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial OutP
      (TerminalOutcome protocol initial Stmt Out Fault)) :
    Terminal (ClosedClaim (Stmt run.execution.path.toBranchPath)
      (Out run.execution.path.toBranchPath)) Fault :=
  run.execution.verifierOut.map fun claim =>
    claim.closeWith
      (run.execution.path.closingImpl protocol.oracles initial run.inputImpl)

/-- Package the structural branch together with its closed explicit outcome. -/
def PhasedRun.terminalClosedResult
    (run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial OutP
      (TerminalOutcome protocol initial Stmt Out Fault)) :
    (path : protocol.tree.BranchPath) ×
      Terminal (ClosedClaim (Stmt path) (Out path)) Fault :=
  ⟨run.execution.path.toBranchPath, run.terminalClosed⟩

/-- Closing cannot create or erase verifier rejection. -/
@[simp]
theorem PhasedRun.terminalClosed_eq_reject_iff
    (run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial OutP
      (TerminalOutcome protocol initial Stmt Out Fault)) :
    run.terminalClosed = .reject ↔ run.execution.verifierOut = .reject := by
  unfold PhasedRun.terminalClosed
  cases run.execution.verifierOut <;> simp [Terminal.map]

/-- Closing preserves the exact returned fault. -/
@[simp]
theorem PhasedRun.terminalClosed_eq_fault_iff
    (run : PhasedRun ambient protocol.tree protocol.roles protocol.oracles initial OutP
      (TerminalOutcome protocol initial Stmt Out Fault)) (fault : Fault) :
    run.terminalClosed = .fault fault ↔ run.execution.verifierOut = .fault fault := by
  unfold PhasedRun.terminalClosed
  cases run.execution.verifierOut <;> simp [Terminal.map]

/-- Closing a phased explicit outcome agrees with closing the terminal artifact produced by the
same reduction execution. The comparison erases phase instrumentation; it does not replay the
protocol or construct a replacement terminal run. -/
theorem executePhased_terminalClosed {StatementIn WitnessIn : Type}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP
      (TerminalOutcome protocol initial Stmt Out Fault))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    PhasedRun.terminalClosedResult <$> executePhased reduction impl stmt wit =
      (fun run => ⟨run.result.path.toBranchPath, run.closed⟩) <$>
        executeTerminal reduction impl stmt wit := by
  simp only [executePhased, executePhases, executeTerminal, map_bind, map_pure]
  conv_rhs => rw [← loggingOracle.fst_map_run_simulateQ (reduction.prover stmt wit)]
  simp only [bind_map_left]
  apply bind_congr
  intro setupResult
  have observed := executeStrategiesPhased_erase ambient protocol.tree protocol.roles
    protocol.oracles initial impl setupResult.1 (reduction.verifier stmt)
  have projected := congrArg (fun program =>
    (fun observation : LoggedObservation protocol.tree protocol.oracles initial OutP
        (TerminalOutcome protocol initial Stmt Out Fault) =>
      (⟨observation.1.toBranchPath,
        observation.2.2.1.map fun claim => claim.closeWith
          (observation.1.closingImpl protocol.oracles initial impl)⟩ :
        (path : protocol.tree.BranchPath) ×
          Terminal (ClosedClaim (Stmt path) (Out path)) Fault)) <$> program) observed
  simpa [PhasedRun.terminalClosedResult, PhasedRun.terminalClosed,
    PhasedResult.observe, LoggedResult.observe, executeTerminal, TerminalRun.closed,
    Functor.map_map] using projected

end TerminalClaims

/-- Initialize the world once and execute setup and every protocol action in that shared state. -/
def executePhasedWithRuntime {ι κ : Type} {Import : OracleSpec ι} {Surface : OracleSpec κ}
    (runtime : OracleRuntime Import Surface) {protocol : Oracle.Protocol}
    {initial : PFunctor} {StatementIn WitnessIn : Type}
    {OutP : protocol.tree.ExecutionPath → Type} {OutV : protocol.tree.BranchPath → Type}
    (reduction : Reduction Surface protocol initial StatementIn WitnessIn OutP OutV)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :=
  runtime.run (executePhased reduction impl stmt wit)

/-- On a supported runtime result, the derived chronological protocol regions are exactly its
world-surface log. The runtime support witness supplies provenance; the carrier alone does not. -/
theorem executePhasedWithRuntime_trace {ι κ : Type}
    {Import : OracleSpec ι} {Surface : OracleSpec κ} (runtime : OracleRuntime Import Surface)
    {protocol : Oracle.Protocol} {initial : PFunctor} {StatementIn WitnessIn : Type}
    {OutP : protocol.tree.ExecutionPath → Type} {OutV : protocol.tree.BranchPath → Type}
    (reduction : Reduction Surface protocol initial StatementIn WitnessIn OutP OutV)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn)
    (result : RunResult runtime
      (PhasedRun Surface protocol.tree protocol.roles protocol.oracles initial OutP OutV))
    (generated : runtime.GeneratedBy (executePhased reduction impl stmt wit) result) :
    ((result.output.phases).map WorldPhase.queries).flatten = result.trace := by
  rw [PhasedRun.phases_flatten]
  exact executePhases_world_eq Surface protocol.tree protocol.roles protocol.oracles initial impl
    (reduction.prover stmt wit) (reduction.verifier stmt) result.output result.trace
    (runtime.mem_support_logged_of_generatedBy _ _ generated)

end Interaction.Oracle
