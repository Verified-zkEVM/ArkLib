/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Oracle.LoggedExecution

/-!
# Laws of the step log

The step log of `runWithStepLog` records each step with its transcript so far, its actor and its
queries. This file shows that the step log forgets to the existing logged runs. Forgetting the step
boundaries gives `runWithLog`, and forgetting all logs gives `run`. The same holds for the ambient
step log, for a run with a separate setup step, and under any lawful interpreter. These laws
mention `runWithLog`, which `Security/Knowledge.lean` defines on top of `StepLog.lean`. They
cannot live in `StepLog.lean` without an import cycle.
-/

@[expose] public section

universe u q uS uI dI wJ

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

namespace OracleVerifier

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, 0, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : PathAlong oracleSig s → Type}

/-- Forgetting the step boundaries gives exactly the existing full logged run. -/
theorem toLog_runWithStepLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    StepLog.toLog <$> V.runWithStepLog stmt data prover = V.runWithLog stmt data prover := rfl

/-- Forgetting the whole step log gives exactly the ordinary run. -/
theorem map_fst_runWithStepLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    StepLog.observation <$> V.runWithStepLog stmt data prover = V.run stmt data prover := by
  have h := congrArg (Functor.map Sigma.fst) (V.toLog_runWithStepLog stmt data prover)
  simpa only [Functor.map_map, StepLog.toLog, map_fst_runWithLog] using h

/-- Keeping only the ambient queries of the decision log gives the ambient-only logged run. -/
theorem toAmbientLog_runWithStepLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    (fun r : StepLog V Out =>
      (r.observation, (concatQueries r.steps).fst, r.decisionQueries.fst)) <$>
        V.runWithStepLog stmt data prover = V.runWithAmbientLog stmt data prover := by
  rw [← V.map_runWithLog_eq_runWithAmbientLog stmt data prover,
    ← V.toLog_runWithStepLog stmt data prover, Functor.map_map]
  rfl

/-- Execute an explicit prover setup action and log it as a separate step at the empty
transcript. -/
def runWithSetupStep (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    OracleComp (ambient + challengeSpec oracleSig s) (StepLog V Out) := do
  let (prover, queries) ← simulateQ
    (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) setup.withQueryLog
  let result ← V.runWithStepLog stmt data prover
  pure (result.withSetupStep queries)

/-- Forgetting the boundaries of the setup step and the participant steps gives the existing
logged execution, with the setup queries in front of its prover log. -/
theorem toLog_runWithSetupStep (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    StepLog.toLog <$> V.runWithSetupStep stmt data setup = (do
      let (prover, queries) ← simulateQ
        (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) setup.withQueryLog
      (fun z => (⟨z.1, queries ++ z.2.1, z.2.2⟩ :
        (obs : Observation oracleSig s Out (OracleVerifier.Output T B)) × QueryLog ambient ×
          QueryLog (ambient + (pathResources inputs s (projectPathAlong oracleSig s obs.1)).spec)))
        <$> V.runWithLog stmt data prover) := by
  simp only [runWithSetupStep, _root_.map_bind, LawfulApplicative.map_pure]
  refine bind_congr fun r => ?_
  rw [← V.toLog_runWithStepLog stmt data r.1, Functor.map_map, map_eq_bind_pure_comp]
  refine bind_congr fun result => ?_
  exact congrArg pure (result.toLog_withSetupStep r.2)

/-- Forgetting the step log of a run with a setup step gives the ordinary setup followed by the
ordinary run. -/
theorem map_fst_runWithSetupStep (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    StepLog.observation <$> V.runWithSetupStep stmt data setup = (do
      let prover ← simulateQ
        (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) setup
      V.run stmt data prover) := by
  let lift : QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)) :=
    fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))
  trans simulateQ lift setup.withQueryLog >>= fun r => V.run stmt data r.1
  · simp only [runWithSetupStep, _root_.map_bind, LawfulApplicative.map_pure]
    refine bind_congr fun r => ?_
    simpa only [map_eq_bind_pure_comp, StepLog.withSetupStep, Function.comp_def] using
      V.map_fst_runWithStepLog stmt data r.1
  · rw [← bind_map_left Prod.fst, ← simulateQ_map]
    have erased : Prod.fst <$> setup.withQueryLog = setup :=
      loggingOracle.fst_map_run_simulateQ setup
    rw [erased]

/-- Interpreting the step log of a run commutes with forgetting it to the full query logs. This
includes stateful runtimes. -/
theorem simulateQ_toLog_runWithStepLog {m : Type → Type u} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    StepLog.toLog <$> simulateQ handler (V.runWithStepLog stmt data prover) =
      simulateQ handler (V.runWithLog stmt data prover) := by
  rw [← simulateQ_map, toLog_runWithStepLog]

/-- Keep only the ambient queries of the decision and the same participant steps. -/
def StepLog.toAmbient {V : OracleVerifier ambient s S T inputs outputs}
    (r : StepLog V Out) : AmbientStepLog V Out :=
  ⟨r.observation, r.steps, r.decisionQueries.fst⟩

/-- The full and the ambient step logs have exactly the same transcripts so far, actors and
query groups. -/
theorem toAmbient_runWithStepLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    StepLog.toAmbient <$> V.runWithStepLog stmt data prover =
      V.runWithAmbientStepLog stmt data prover := by
  simp only [runWithStepLog, runWithAmbientStepLog, executeWith, Functor.map_map, _root_.map_bind]
  refine bind_congr fun r => ?_
  rw [← map_run_withLogging_addLift_fst, bind_map_left]
  simp [StepLog.toAmbient]

section AmbientStepLog

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, q}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, uI, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : PathAlong oracleSig s → Type}

/-- Forgetting the step boundaries of the ambient step log gives exactly the existing ambient
logged run. -/
theorem toLog_runWithAmbientStepLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientStepLog.toLog <$> V.runWithAmbientStepLog stmt data prover =
      V.runWithAmbientLog stmt data prover := rfl

/-- Forgetting the ambient step log gives the ordinary run, with independent resource-query
universes. -/
theorem map_fst_runWithAmbientStepLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientStepLog.observation <$> V.runWithAmbientStepLog stmt data prover =
      V.run stmt data prover := by
  have h := congrArg (Functor.map Prod.fst) (V.toLog_runWithAmbientStepLog stmt data prover)
  simpa only [Functor.map_map, AmbientStepLog.toLog, map_fst_runWithAmbientLog] using h

/-- Forgetting the ambient step log to the ambient query logs also commutes with every lawful
interpreter. -/
theorem simulateQ_toLog_runWithAmbientStepLog {m : Type → Type u} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientStepLog.toLog <$> simulateQ handler (V.runWithAmbientStepLog stmt data prover) =
      simulateQ handler (V.runWithAmbientLog stmt data prover) := by
  rw [← simulateQ_map, toLog_runWithAmbientStepLog]

end AmbientStepLog

end OracleVerifier

end Interaction.Core
