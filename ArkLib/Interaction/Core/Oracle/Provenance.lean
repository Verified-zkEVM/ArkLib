/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Oracle.LoggedExecution

/-!
# Erasure and interpretation of per-slot provenance

Prefixes contain the actual moves, including challenges and oracle payloads. Slot owners come
from the participant whose action the runner executes. The passive verifier's decision is a
separate terminal phase. Logging each slot preserves the order and multiplicity of queries.
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

/-- Erasing phase boundaries gives exactly the existing full logged run. -/
theorem runWithTrace_logView (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    TracedRun.logView <$> V.runWithTrace stmt data prover = V.runWithLog stmt data prover := rfl

/-- Forgetting all provenance gives exactly the ordinary run. -/
theorem runWithTrace_erase (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    TracedRun.observation <$> V.runWithTrace stmt data prover = V.run stmt data prover := by
  have h := congrArg (Functor.map Sigma.fst) (V.runWithTrace_logView stmt data prover)
  simpa only [Functor.map_map, TracedRun.logView, map_fst_runWithLog] using h

/-- Restricting the terminal decision log to ambient queries gives the ambient-only logged run. -/
theorem runWithTrace_ambientLog (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    (fun r : TracedRun V Out =>
      (r.observation, (slotQueries r.interaction).fst, r.decisionQueries.fst)) <$>
        V.runWithTrace stmt data prover = V.runWithAmbientLog stmt data prover := by
  rw [← V.map_runWithLog_eq_runWithAmbientLog stmt data prover,
    ← V.runWithTrace_logView stmt data prover, Functor.map_map]
  rfl

/-- Execute an explicit prover setup action as a separate traced slot at the empty prefix. -/
def runWithSetupTrace (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    OracleComp (ambient + challengeSpec oracleSig s) (TracedRun V Out) := do
  let (prover, queries) ← simulateQ
    ((QueryImpl.id' (ambient + challengeSpec oracleSig s)).restrictLeft) setup.withQueryLog
  let result ← V.runWithTrace stmt data prover
  pure (result.prependSetup queries)

/-- Forgetting setup and interaction boundaries gives the existing logged execution, with
setup queries prepended to its prover log. -/
theorem runWithSetupTrace_logView (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    TracedRun.logView <$> V.runWithSetupTrace stmt data setup = (do
      let (prover, queries) ← simulateQ
        (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) setup.withQueryLog
      (fun z => (⟨z.1, queries ++ z.2.1, z.2.2⟩ :
        (obs : Observation oracleSig s Out (OracleVerifier.Output T B)) × QueryLog ambient ×
          QueryLog (ambient + (pathResources inputs s (projectPathAlong oracleSig s obs.1)).spec)))
        <$> V.runWithLog stmt data prover) := by
  simp only [runWithSetupTrace, _root_.map_bind, LawfulApplicative.map_pure]
  refine bind_congr fun r => ?_
  rw [← V.runWithTrace_logView stmt data r.1, Functor.map_map, map_eq_bind_pure_comp]
  refine bind_congr fun result => ?_
  exact congrArg pure (result.logView_prependSetup r.2)

/-- Forgetting explicit setup provenance preserves the ordinary setup followed by the run. -/
theorem runWithSetupTrace_erase (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    TracedRun.observation <$> V.runWithSetupTrace stmt data setup = (do
      let prover ← simulateQ
        (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) setup
      V.run stmt data prover) := by
  let lift : QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)) :=
    (QueryImpl.id' (ambient + challengeSpec oracleSig s)).restrictLeft
  trans simulateQ lift setup.withQueryLog >>= fun r => V.run stmt data r.1
  · simp only [runWithSetupTrace, _root_.map_bind, LawfulApplicative.map_pure]
    refine bind_congr fun r => ?_
    simpa only [map_eq_bind_pure_comp, TracedRun.prependSetup, Function.comp_def] using
      V.runWithTrace_erase stmt data r.1
  · rw [← bind_map_left Prod.fst, ← simulateQ_map]
    have erased : Prod.fst <$> setup.withQueryLog = setup :=
      loggingOracle.fst_map_run_simulateQ setup
    rw [erased]
    rfl

/-- Interpreting a traced run commutes with its full-log projection, including stateful runtimes. -/
theorem simulateQ_runWithTrace_logView {m : Type → Type u} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    TracedRun.logView <$> simulateQ handler (V.runWithTrace stmt data prover) =
      simulateQ handler (V.runWithLog stmt data prover) := by
  rw [← simulateQ_map, runWithTrace_logView]

/-- Keep only ambient decision queries while retaining the same produced interaction slots. -/
def TracedRun.ambientView {V : OracleVerifier ambient s S T inputs outputs}
    (r : TracedRun V Out) : AmbientTracedRun V Out :=
  ⟨r.observation, r.interaction, r.decisionQueries.fst⟩

/-- Full and ambient traces use exactly the same produced prefixes, owners and query groups. -/
theorem runWithTrace_ambientView (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    TracedRun.ambientView <$> V.runWithTrace stmt data prover =
      V.runWithAmbientTrace stmt data prover := by
  simp only [runWithTrace, runWithAmbientTrace, executeWith, Functor.map_map, _root_.map_bind]
  refine bind_congr fun r => ?_
  rw [← map_run_withLogging_addLift_fst, bind_map_left]
  simp [TracedRun.ambientView]

section AmbientTrace

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, q}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : Resources.{0, uI, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : PathAlong oracleSig s → Type}

/-- Forgetting ambient phase boundaries gives exactly the existing ambient logged run. -/
theorem runWithAmbientTrace_logView (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientTracedRun.logView <$> V.runWithAmbientTrace stmt data prover =
      V.runWithAmbientLog stmt data prover := rfl

/-- Ambient provenance erases to the ordinary run with independent resource-query universes. -/
theorem runWithAmbientTrace_erase (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientTracedRun.observation <$> V.runWithAmbientTrace stmt data prover =
      V.run stmt data prover := by
  have h := congrArg (Functor.map Prod.fst) (V.runWithAmbientTrace_logView stmt data prover)
  simpa only [Functor.map_map, AmbientTracedRun.logView, map_fst_runWithAmbientLog] using h

/-- Ambient trace projection also commutes with every lawful interpreter. -/
theorem simulateQ_runWithAmbientTrace_logView {m : Type → Type u} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientTracedRun.logView <$> simulateQ handler (V.runWithAmbientTrace stmt data prover) =
      simulateQ handler (V.runWithAmbientLog stmt data prover) := by
  rw [← simulateQ_map, runWithAmbientTrace_logView]

end AmbientTrace

end OracleVerifier

end Interaction.Core
