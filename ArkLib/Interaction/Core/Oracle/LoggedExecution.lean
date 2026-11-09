/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.Knowledge
public import VCVio.OracleComp.Runtime

/-!
# Logged and runtime execution of passive oracle verifiers

`OracleVerifier.runWithLog` records the prover's ambient queries and every query of the decision
before routing: ambient queries and queries to the input and message oracles, in order and with
repeats. Forgetting both logs gives `OracleVerifier.run` exactly.

A persistent `OracleRuntime` whose surface is the run's oracle interface (ambient queries and
challenge draws) executes the logged run once, after its setup. The result pairs the logged
observation with the final runtime state and the ordered surface trace. Erasing the logs and the
trace gives the ordinary stateful execution of `OracleVerifier.run`.
-/

@[expose] public section

-- `OracleComp.withQueryLog_simulateQ` mentions no ArkLib type; it moves to VCVio next to
-- `QueryImpl.simulateQ_compose`, and is removed here when the pinned VCVio provides it.

/-- Logging after substitution records the target queries actually made by each handler program,
in their execution order. One source query may make zero, one, or many target queries. -/
theorem OracleComp.withQueryLog_simulateQ {ι κ : Type} {source : OracleSpec ι}
    {target : OracleSpec κ} {α : Type}
    (route : QueryImpl source (OracleComp target)) (program : OracleComp source α) :
    (simulateQ route program).withQueryLog =
      (simulateQ (QueryImpl.compose target.loggingOracle route) program).run := by
  unfold OracleComp.withQueryLog OracleSpec.loggingOracle
  rw [QueryImpl.simulateQ_compose]

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

namespace OracleVerifier
variable {ι I J S T : Type} {ambient : OracleSpec ι} {s : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
  {Out : PathAlong oracleSig s → Type}

private theorem bind_run_withLogging {κ α β : Type} {spec : OracleSpec κ}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (program : OracleComp spec α) (next : α → m β) :
    simulateQ impl program >>= next =
      (simulateQ impl.withLogging program).run >>= fun z => next z.1 := by
  rw [← QueryImpl.fst_map_run_withLogging, bind_map_left]

/-- Forgetting both logs of the logged run gives the oracle verifier's run exactly. -/
theorem runWithLog_erase (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    Sigma.fst <$> V.runWithLog stmt data prover = V.run stmt data prover := by
  simp only [runWithLog, run, _root_.map_bind]
  conv_rhs => rw [← simulateQ_id' (TwoParty.Lens.run s _ _),
    bind_run_withLogging (QueryImpl.id' (ambient + challengeSpec oracleSig s))]
  refine bind_congr fun x => ?_
  obtain ⟨⟨tr, out, _⟩, proveLog⟩ := x
  rw [bind_run_withLogging (QueryImpl.addLift _ _)]
  refine bind_congr fun y => ?_
  simp

/-- Execute the logged run once in a persistent runtime that interprets the run's ambient
queries and challenge draws. -/
def runWithRuntime (V : OracleVerifier ambient s S T inputs outputs)
    {κ : Type} {Import : OracleSpec κ}
    (runtime : OracleRuntime Import (ambient + challengeSpec oracleSig s)) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    OracleComp Import (RunResult runtime
      ((obs : Observation oracleSig s Out (T × (∀ j, B j))) × QueryLog ambient ×
        QueryLog (ambient +
          (sumFamily inputs (pathFamily s (projectPathAlong oracleSig s obs.1))).spec))) :=
  runtime.run (V.runWithLog stmt data prover)

/-- Runtime execution initializes once, then runs the logged program from that state, with no
other execution or replay of resource queries. -/
theorem runWithRuntime_eq (V : OracleVerifier ambient s S T inputs outputs)
    {κ : Type} {Import : OracleSpec κ}
    (runtime : OracleRuntime Import (ambient + challengeSpec oracleSig s)) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    V.runWithRuntime runtime stmt data prover =
      runtime.setup >>= fun state => runtime.runFrom state (V.runWithLog stmt data prover) :=
  runtime.run_eq _

/-- Erasing the logs and the trace leaves the run's observation and the actual final state of the
ordinary stateful execution. -/
theorem runWithRuntime_erase (V : OracleVerifier ambient s S T inputs outputs)
    {κ : Type} {Import : OracleSpec κ}
    (runtime : OracleRuntime Import (ambient + challengeSpec oracleSig s)) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    (fun result => (result.output.1, result.state)) <$>
        V.runWithRuntime runtime stmt data prover =
      runtime.setup >>= fun state =>
        runtime.handler.runState state (V.run stmt data prover) := by
  rw [runWithRuntime_eq, _root_.map_bind]
  refine bind_congr fun state => ?_
  have erased := runtime.runFrom_eraseTrace state (V.runWithLog stmt data prover)
  have paired := congrArg (fun program =>
    (fun result => (result.1.1, result.2)) <$> program) erased
  have logged := congrArg (runtime.handler.runState state) (V.runWithLog_erase stmt data prover)
  calc
    _ = (fun result => (result.1.1, result.2)) <$>
        runtime.handler.runState state (V.runWithLog stmt data prover) := by
      simpa only [Functor.map_map] using paired
    _ = _ := by
      simpa [QueryImpl.Stateful.runState, monad_norm] using logged

end OracleVerifier
end Interaction.Core
