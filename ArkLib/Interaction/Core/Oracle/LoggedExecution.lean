/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.Knowledge
public import VCVio.OracleComp.Runtime

/-!
# Logged execution of passive oracle verifiers

`OracleVerifier.runWithLog` records the prover's ambient queries and every query of the decision
before routing: ambient queries and queries to the input and message oracles, in order and with
repeats. Forgetting both logs gives `OracleVerifier.run` exactly.

Logging after substitution, VCVio's `OracleComp.withQueryLog_simulateQ`, records the target
queries each handler program makes, in order. A persistent `OracleRuntime` executes the logged run
directly as `runtime.run (V.runWithLog stmt data prover)`.
-/

@[expose] public section

universe v u uι uI uJ uS wI wJ

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

namespace OracleVerifier
variable {ι I : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol}
  {T : Path s → Type} {A : I → Type} {J : Path s → Type}
  {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{0, 0, 0} I A}
  {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {Out : PathAlong oracleSig s → Type}

/-- Interpreting a logged run in any lawful monad commutes with erasing both logs. -/
theorem simulateQ_runWithLog_erase {m : Type → Type v} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    Sigma.fst <$> simulateQ handler (V.runWithLog stmt data prover) =
      simulateQ handler (V.run stmt data prover) := by
  rw [← simulateQ_map, map_fst_runWithLog]

/-- Running the logged run in a persistent runtime and erasing the logs and the trace gives the
ordinary stateful execution of the run. This composes VCVio's `runFrom_eraseTrace` with
`map_fst_runWithLog`. -/
theorem runtime_runWithLog_erase {κ : Type} {Import : OracleSpec κ}
    (V : OracleVerifier ambient s S T inputs outputs)
    (runtime : OracleRuntime Import (ambient + challengeSpec oracleSig s)) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    (fun result => (result.output.1, result.state)) <$>
        runtime.run (V.runWithLog stmt data prover) =
      runtime.setup >>= fun state => runtime.handler.runState state (V.run stmt data prover) := by
  rw [OracleRuntime.run_eq, _root_.map_bind]
  refine bind_congr fun state => ?_
  have erased := runtime.runFrom_eraseTrace state (V.runWithLog stmt data prover)
  have paired := congrArg (fun program =>
    (fun result => (result.1.1, result.2)) <$> program) erased
  have logged := congrArg (runtime.handler.runState state) (V.map_fst_runWithLog stmt data prover)
  calc
    _ = (fun result => (result.1.1, result.2)) <$>
        runtime.handler.runState state (V.runWithLog stmt data prover) := by
      simpa only [Functor.map_map] using paired
    _ = _ := by
      simpa [QueryImpl.Stateful.runState, monad_norm] using logged

/-- Interpret a final decision in a monad with labelled failures, retaining every answered
query before a failure. The failing query has no answer and contributes no log entry. The
state transformer lies below the exception transformer, so rejection and failure remain distinct
and both retain the completed query log. -/
def decideWithFailureLog {ε : Type} {m : Type → Type v} [Monad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl ambient (ExceptT ε m)) (stmt : S) (p : Path s)
    (view : View s p) (data : (pathResources inputs s p).Data) :
    m (Except ε (Option (T p)) × QueryLog (ambient + (pathResources inputs s p).spec)) :=
  let spec := ambient + (pathResources inputs s p).spec
  let answer : QueryImpl spec (ExceptT ε m) :=
    QueryImpl.addLift handler ((pathResources inputs s p).answer data)
  let logged : QueryImpl spec (ExceptT ε (StateT (QueryLog spec) m)) := fun q =>
    ExceptT.mk do
      let result ← liftM (answer q).run
      match result with
      | .error e => pure (.error e)
      | .ok a =>
        modify (· ++ [⟨q, a⟩])
        pure (.ok a)
  ((simulateQ logged (V.decide stmt p view).run).run).run []

/-- Embedding an optional verdict before closing with the completed transcript's resources
agrees with closing first and then embedding. Absence remains rejection and creates no failure. -/
theorem close_optional_ok {ε : Type v} {ι : Type uι} {I : Type uI} {S : Type uS}
    {ambient : OracleSpec.{uι, u} ι} {s : OracleProtocol.{u}} {T : Path s → Type u}
    {A : I → Type u} {J : Path s → Type uJ} {B : (p : Path s) → J p → Type u}
    {inputs : OracleFamily.{uI, u, wI} I A}
    {outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : ∀ i, A i)
    (tr : PathAlong oracleSig s) (outcome : Option (T (projectPathAlong oracleSig s tr))) :
    let p := projectPathAlong oracleSig s tr
    let resources : (pathResources inputs s p).Data := (data, payloads s tr)
    let close := fun t => (t, (V.outputMap stmt p (toView s tr)).f resources)
    (Except.ok outcome : Except ε (Option (T p))).map (Option.map close) =
      Except.ok (outcome.map close) := rfl

end OracleVerifier
end Interaction.Core
