/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.LoggedExecution
public import ArkLib.Interaction.Oracle.QueriesByMove

/-!
# Laws of the queries by move

`runWithQueriesByMove` records, for each move, an entry with the partial transcript before it, the
querier and the queries made there. This file shows that these queries by move forget to the
existing logged runs. Forgetting the move boundaries gives `runWithLog`, and forgetting all logs
gives `run`. The same holds for the ambient queries by move, for a run with a separate prover
setup entry, and under any lawful interpreter. These laws mention `runWithLog`, which
`Security/Knowledge.lean` defines. Both runners execute through `OracleVerifier.executeWith`, so
the projection laws combine `runWithQueriesByMove_toLog` with `runWithLog_eq`.
-/

@[expose] public section

universe u q uS uI dI wJ

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

namespace OracleVerifier

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : OracleBundle.{0, 0, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : Transcript oracleSig s → Type}

/-- Forgetting the move boundaries gives exactly the existing full logged run. -/
theorem toLog_runWithQueriesByMove (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    QueriesByMove.toLog <$> V.runWithQueriesByMove stmt data prover =
      V.runWithLog stmt data prover :=
  (V.runWithQueriesByMove_toLog stmt data prover).trans (V.runWithLog_eq stmt data prover).symm

/-- Forgetting all the queries by move gives exactly the ordinary run. -/
theorem map_fst_runWithQueriesByMove (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    QueriesByMove.outcome <$> V.runWithQueriesByMove stmt data prover = V.run stmt data prover := by
  have h := congrArg (Functor.map Sigma.fst) (V.toLog_runWithQueriesByMove stmt data prover)
  simpa only [Functor.map_map, QueriesByMove.toLog, map_fst_runWithLog] using h

/-- Keeping only the ambient queries of the decision log gives the ambient-only logged run. -/
theorem toAmbientLog_runWithQueriesByMove (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    (fun r : QueriesByMove V Out =>
      (r.outcome, (concatQueries r.moves).fst, r.decisionQueries.fst)) <$>
        V.runWithQueriesByMove stmt data prover = V.runWithAmbientLog stmt data prover := by
  rw [← V.map_runWithLog_eq_runWithAmbientLog stmt data prover,
    ← V.toLog_runWithQueriesByMove stmt data prover, Functor.map_map]
  rfl

/-- Execute an explicit prover setup action and log it as a separate entry at the empty partial
transcript. -/
def runWithProverSetup (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    OracleComp (ambient + challengeSpec oracleSig s) (QueriesByMove V Out) := do
  let (prover, queries) ← simulateQ
    ((QueryImpl.id' (ambient + challengeSpec oracleSig s)).restrictLeft) setup.withQueryLog
  let result ← V.runWithQueriesByMove stmt data prover
  pure (result.withProverSetup queries)

/-- Forgetting the boundaries of the setup entry and the moves' entries gives the existing
logged execution, with the setup queries in front of its prover log. -/
theorem toLog_runWithProverSetup (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    QueriesByMove.toLog <$> V.runWithProverSetup stmt data setup = (do
      let (prover, queries) ← simulateQ
        (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) setup.withQueryLog
      (fun z => (⟨z.1, queries ++ z.2.1, z.2.2⟩ :
        (obs : Outcome oracleSig s Out (OracleVerifier.Output T B)) × QueryLog ambient ×
          QueryLog (ambient + (pathBundle inputs s (Transcript.path obs.1)).spec)))
        <$> V.runWithLog stmt data prover) := by
  simp only [runWithProverSetup, _root_.map_bind, LawfulApplicative.map_pure]
  refine bind_congr fun r => ?_
  rw [← V.toLog_runWithQueriesByMove stmt data r.1, Functor.map_map, map_eq_bind_pure_comp]
  refine bind_congr fun result => ?_
  exact congrArg pure (result.toLog_withProverSetup r.2)

/-- Forgetting the queries by move of a run with a setup entry gives the ordinary setup followed by
the ordinary run. -/
theorem map_fst_runWithProverSetup (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : inputs.Data) (setup : OracleComp ambient (Prover oracleSig ambient s Out)) :
    QueriesByMove.outcome <$> V.runWithProverSetup stmt data setup = (do
      let prover ← simulateQ
        (fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))) setup
      V.run stmt data prover) := by
  let lift : QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)) :=
    (QueryImpl.id' (ambient + challengeSpec oracleSig s)).restrictLeft
  trans simulateQ lift setup.withQueryLog >>= fun r => V.run stmt data r.1
  · simp only [runWithProverSetup, _root_.map_bind, LawfulApplicative.map_pure]
    refine bind_congr fun r => ?_
    simpa only [map_eq_bind_pure_comp, QueriesByMove.withProverSetup, Function.comp_def] using
      V.map_fst_runWithQueriesByMove stmt data r.1
  · rw [← bind_map_left Prod.fst, ← simulateQ_map]
    have erased : Prod.fst <$> setup.withQueryLog = setup :=
      loggingOracle.fst_map_run_simulateQ setup
    rw [erased]
    rfl

/-- Interpreting the queries by move of a run commutes with forgetting it to the full query logs.
This includes stateful runtimes. -/
theorem simulateQ_toLog_runWithQueriesByMove {m : Type → Type u} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    QueriesByMove.toLog <$> simulateQ handler (V.runWithQueriesByMove stmt data prover) =
      simulateQ handler (V.runWithLog stmt data prover) := by
  rw [← simulateQ_map, toLog_runWithQueriesByMove]

/-- Keep only the ambient queries of the decision and the same moves' entries. -/
def QueriesByMove.toAmbient {V : OracleVerifier ambient s S T inputs outputs}
    (r : QueriesByMove V Out) : AmbientQueriesByMove V Out :=
  ⟨r.outcome, r.moves, r.decisionQueries.fst⟩

/-- The full and the ambient queries by move have exactly the same partial transcripts, queriers
and query groups. -/
theorem toAmbient_runWithQueriesByMove (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    QueriesByMove.toAmbient <$> V.runWithQueriesByMove stmt data prover =
      V.runWithAmbientQueriesByMove stmt data prover := by
  simp only [runWithQueriesByMove, runWithAmbientQueriesByMove, executeWith, Functor.map_map,
    _root_.map_bind]
  refine bind_congr fun r => ?_
  rw [← map_run_withLogging_addLift_fst, bind_map_left]
  simp [QueriesByMove.toAmbient]

section AmbientQueriesByMove

variable {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol.{0, q}}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : OracleBundle.{0, uI, dI}} {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : Transcript oracleSig s → Type}

/-- Forgetting the move boundaries of the ambient queries by move gives exactly the existing ambient
logged run. -/
theorem toLog_runWithAmbientQueriesByMove (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientQueriesByMove.toLog <$> V.runWithAmbientQueriesByMove stmt data prover =
      V.runWithAmbientLog stmt data prover :=
  (V.runWithAmbientQueriesByMove_toLog stmt data prover).trans
    (V.runWithAmbientLog_eq stmt data prover).symm

/-- Forgetting the ambient queries by move gives the ordinary run, with independent bundle-query
universes. -/
theorem map_fst_runWithAmbientQueriesByMove (V : OracleVerifier ambient s S T inputs outputs)
    (stmt : S) (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientQueriesByMove.outcome <$> V.runWithAmbientQueriesByMove stmt data prover =
      V.run stmt data prover := by
  have h := congrArg (Functor.map Prod.fst) (V.toLog_runWithAmbientQueriesByMove stmt data prover)
  simpa only [Functor.map_map, AmbientQueriesByMove.toLog, map_fst_runWithAmbientLog] using h

/-- Forgetting the ambient queries by move to the ambient query logs also commutes with every lawful
interpreter. -/
theorem simulateQ_toLog_runWithAmbientQueriesByMove {m : Type → Type u} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : inputs.Data) (prover : Prover oracleSig ambient s Out) :
    AmbientQueriesByMove.toLog <$>
        simulateQ handler (V.runWithAmbientQueriesByMove stmt data prover) =
      simulateQ handler (V.runWithAmbientLog stmt data prover) := by
  rw [← simulateQ_map, toLog_runWithAmbientQueriesByMove]

end AmbientQueriesByMove

end OracleVerifier

end Interaction
